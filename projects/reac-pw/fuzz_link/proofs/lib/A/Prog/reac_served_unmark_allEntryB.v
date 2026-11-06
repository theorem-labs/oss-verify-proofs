(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module paths and module names changed; 489 of its 555 lines of code are new or changed and 525 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08) on image A, THE
   ENTRY PIECE B: from the BRANCH cut (+0x18c, reac_served_unmark_allEntryDefs.v) to the RELEASE, TAIL or HEAD cut.
   It proves `um_entryB : um_rel_obl SK B -> um_tail_obl SK B -> um_head_obl SK B 0 -> um_br_obl SK B`.

   The code (listing (internal path) (internal record, sha256 9bc7ee7c887a),
   lines 103-121 and 286-290):
     +0x18c  beqz s4, +0x350                  m = 0: the RELEASE cut
     +0x190  srli a0, s4, 3; add s10, a0, s10; lb a0, 0(s10); bnez a0, +0x468
     +0x468  andi a1, s4, 7; addi a1, a1, 3; blt a1, a0, +0x1a0; (else errpath_load4)
                                              ASan's check of the 4-byte load at m: the token engine closes it
                                              with the marks block's shadow entry (mkSHE 20 0 516)
     +0x1a0  lw a0, 0(s4); blez a0, +0x340    n = m->n = 0: the TAIL cut
     +0x1a8 .. +0x1d4                         the loop set-up: s11 := 0, s5 := F + 32, s6 := m + 4,
                                              s7 := .str.4, s8 := -8, a2 := (m & 7) + 3,
                                              [s1 + 0x18] := .str.7, [s1 + 0x10] := a2: the HEAD cut, round 0
   m = 0 is one token run from a state seated at the cut with the condition m = 0 (no region); m <> 0 is one run
   from a state seated with m <> 0, the slot window [s1 + 16, s1 + 32) and the marks block (its first word = an
   atom for n, 0 <= n <= 32 by marks_wf) to `blez`, a branch on n, and one run to the TAIL or HEAD cut. Every
   cut is re-established from the BRANCH cut's um_base (only the two slots in the caller's stack window change)
   and um_gnl_kept (g_nl's bytes are the call's: um_kinv at round 0, and the Post's m = 0 arm).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allEntryDefs reac_served_unmark_allWriteKit
reac_served_unmark_allWrite reac_served_unmark_allTail.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_entryB : YI16.sink_head := _.

(* ---- the states seated at the BRANCH cut: the registers as atoms (26 = s10, the shadow base) ---- *)
Definition ebBx : sv := SOff 26 0.
(* m <> 0: the slot window of s1 (atom 9), the marks block (atom 20) whose first word is n (atom 32), its shadow *)
Definition ebSH : list shent := [mkSHE 20 0 516].
Definition eb_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 32 16 32 [].
Definition eb_mk : YP09.region := YP09.mkRegion (Some 20%nat) 0 516 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition eb_f1 : facts :=
  mkFacts [(9%nat, mkAF 140735332483072 (2 ^ 47) 5); (20%nat, mkAF 1 (2 ^ 47 - 524) 0);
           (26%nat, mkAF 0x7fff8000 0x7fff8000 0); (32%nat, mkAF 0 32 0)] [mkAC BC_NE (SOff 20 0) (SLit 0)] [].
Definition eb_ss1 : sstate := mkSS (AF_reac_served_unmark_all + 0x18c) sr_atoms [eb_slot; eb_mk] None eb_f1.
(* m = 0: no region *)
Definition eb_ss0 : sstate :=
  mkSS (AF_reac_served_unmark_all + 0x18c) sr_atoms [] None (mkFacts [] [mkAC BC_EQ (SOff 20 0) (SLit 0)] []).

Lemma eb_consts : LA_G_NL = 0x5dcac0 /\ NK_SIZE = 271992 /\ NK_IF_NAME = 271024 /\ MK_SIZE = 516 /\
  MK_NAME = 4 /\ MARK_LEN = 16 /\ MARKS_MAX = 32 /\ SHADOW_OFF = 0x7fff8000 /\ kLowMemEnd = 0x7fff8000 /\
  kHighMemBeg = 0x10007fff8000 /\ kHighMemEnd = 0x800000000000 /\ LA_S_SERVED = 0x213c0 /\ LA_S_EMPTY = 0x214e0 /\
  UM_ALIAS = 32 /\ UM_SLOT_EMPTY = 24 /\ UM_SLOT_LIM = 16 /\ UM_FLAGPTR = 504 /\ UM_FB = 512 /\ UM_SHN = 64 /\
  UM_FRAME = 160.
Proof. repeat split; reflexivity. Qed.

(* ==========================================================================
   1. Bytes and words
   ========================================================================== *)

Lemma eb_testbit_byte : forall (b : byte) i, 8 <= i -> Z.testbit (bv_unsigned b) i = false.
Proof.
  intros b i Hi. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
  rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma eb_le_byte_low : forall z (w k : nat), (k < w)%nat ->
  YO0f.le_byte z w k = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
  intros z w k Hk. unfold YO0f.le_byte. change 256 with (2 ^ 8). apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hl|Hl].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma eb_bytes_le_nth : forall bs k, (k < length bs)%nat ->
  Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b bs IH]; intros k Hk; [cbn [length] in Hk; lia|].
  cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change 256 with (2 ^ 8).
    apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 8) as [Hl|Hl].
    + rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
    + rewrite Z.mod_pow2_bits_high by lia. symmetry. apply eb_testbit_byte. lia.
  - cbn [nth length] in *. rewrite <- (IH k) by lia. f_equal.
    apply Z.bits_inj'. intros i Hi. rewrite !Z.shiftr_spec by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
    rewrite eb_testbit_byte by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma eb_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i] d H; cbn; try reflexivity; try lia.
  apply IH. lia.
Qed.

(* the first word of a marks block, read as the 4-byte value n = mk_n *)
Lemma eb_val_mem_n : forall segs (mem : word -> option byte) p gbs, abytes segs mem p gbs -> (4 <= length gbs)%nat ->
  val_mem segs mem p 4 (mk_n gbs).
Proof.
  intros segs mem p gbs (Ha & Hl & Hb) L k Hk. rewrite (Hb k ltac:(lia)).
  rewrite (nth_error_nth' gbs (Z_to_bv 8 0)) by lia. f_equal.
  rewrite eb_le_byte_low by exact Hk. unfold mk_n, fld_u32, rdn, MK_N, slice.
  change (skipn (Z.to_nat 0) gbs) with gbs. change (Z.to_nat 4) with 4%nat.
  rewrite eb_bytes_le_nth by (rewrite length_firstn; lia).
  rewrite eb_nth_firstn by exact Hk. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* an 8-byte chunk of a region, as a word of memory *)
Lemma eb_chunk8_vm : forall segs E (m : word -> option byte) base off e v,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs m (base + off) 8 v.
Proof.
  intros segs E m base off e v Hc He Hv k Hk.
  destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [cbyte YP09.c_off YP09.c_val] in Hb. injection Hb as <-. cbn [YP09.c_off] in Hm. rewrite Hm. f_equal.
  rewrite He. unfold byte_of_word, YO0f.le_byte. rewrite unsigned_lit_small by lia.
  change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma eb_land7 : forall m, 0 <= m -> 0 <= Z.land m 7 < 8.
Proof. intros m Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* ---- the engine's values ---- *)
Lemma eb_U_shadow : forall E m, ew E 20 = Z_to_bv 64 m -> ew E 26 = Z_to_bv 64 0x7fff8000 -> 0 <= m < 2 ^ 47 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 26 0)) = 0x7fff8000 + m / 8.
Proof.
  intros E m H20 H26 Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 20 m H20) by lia. rewrite (U_atom E 26 0x7fff8000 H26) by lia. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= m / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id (m / 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma eb_U_lim : forall E m, ew E 20 = Z_to_bv 64 m -> 0 <= m < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 20 0) (SLit 7)) (SLit 3)) = Z.land m 7 + 3.
Proof.
  intros E m H20 Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia.
  rewrite (U_atom E 20 m H20) by lia. rewrite U_lit by lia. pose proof (eb_land7 m ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma eb_ge0 : forall E n, ew E 32 = Z_to_bv 64 n -> 0 <= n <= 32 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 32 0)) = (n <=? 0).
Proof.
  intros E n H Hn. cbn [branch_taken]. rewrite !denot_lit_U. rewrite U_lit by lia.
  rewrite (U_atom E 32 n H) by lia. rewrite bv_lts_small by lia.
  destruct (Z.ltb_spec 0 n), (Z.leb_spec n 0); first [reflexivity | lia].
Qed.

(* the write window of the runs: the two slots in the caller's stack window *)
Ltac eb_awr U9 :=
  repeat (apply awr_ok_x_cons; [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val eb_slot eb_mk] in Hx;
    first [lia | rewrite U9 in Hx; left; split; [left; lia | lia]] |]);
  apply awr_ok_x_nil.

(* the bytes a run kept: everything off the slot window *)
Ltac eb_frame_tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end; cbv beta; lia|]);
  destruct Hin.

(* the registers a run left unchanged, among a list *)
Ltac eb_pr HS EREG :=
  let k := fresh "k" in let x := fresh "x" in let Hk := fresh "Hk" in let Hx := fresh "Hx" in
  intros k x Hk Hx;
  assert (Ex : x = Z_to_bv 5 k) by (subst k; symmetry; apply Z_to_bv_bv_unsigned);
  subst x; cbn [In] in Hk;
  repeat (destruct Hk as [<- | Hk]; [
    lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
      let n := eval vm_compute in (Z.to_nat kk) in
      let Hr := fresh "Hr" in
      prreg HS (Z_to_bv 5 kk) Hr; rewrite Hr, (EREG n ltac:(lia)); reflexivity
    end |]);
  destruct Hk.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws (the frame), link's listing values (the link instance: .str.4 / .str.7 are the image atoms
   A_OBJ 50 / A_OBJ 51), the start-up symbols (lib/A AD2l.PcapB_syms), the image's segments (LinkImgInst.v
   pi_link_segs: g_nl is writable at every memory), the relro window in the image (the top file) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.

(* g_nl is writable at every memory *)
Lemma eb_gnl_w : forall (m : word -> option byte) a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof.
  intros m a Ha. pose proof (LA_G_NL_writable m a ltac:(unfold NK_SIZE in Ha; lia)) as Hw.
  rewrite <- HSEGS in Hw. exact Hw.
Qed.

Section c.
Variable cx : umcx.
Variable fpos : Z.
Variables (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model).
Hypothesis HPRE : um_pre SK B cx.
Hypothesis HB : um_base SK B cx fpos ly3 S3 W3 ms3 md3.
Hypothesis HGK : um_gnl_kept cx W3 (ms_mem ms3).

#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).
#[local] Notation Ec := (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a).
#[local] Notation m3 := (ms_mem ms3).
#[local] Notation R3 := (ms_regs ms3).
#[local] Notation SLOT := (fun a => um_sp1 cx + 16 <= a < um_sp1 cx + 32).
(* a memory that differs from the cut's only at the two slots *)
#[local] Notation UNS m' := (forall a, 0 <= a < 2 ^ 64 -> ~ (um_sp1 cx + 16 <= a < um_sp1 cx + 32) ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m3 a).

Lemma eb_geo : um_sp0 cx - um_STK cx <= um_sp cx - 8768 /\ um_sp cx <= um_sp0 cx /\
  um_sp0 cx + um_XO cx <= 2 ^ 47 /\ um_sp cx - 176 <= um_sp1 cx <= um_sp cx - 160 /\ um_sp1 cx mod 32 = 0 /\
  0 <= um_STK cx /\ 0 <= um_XO cx /\ 140735332483072 + 8768 <= um_sp cx /\ YM05.alloc_ceiling <= um_sp cx - 8768 /\
  0 <= um_sp cx < 2 ^ 64.
Proof.
  pose proof (uw_geo SK B cx HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (uw_sp_rng cx). repeat split; lia.
Qed.

(* ---- 1. um_base at a later cut: only the slots changed ---- *)
Lemma eb_base : forall (R' : bvmap 5 word) pc' (m' : word -> option byte) md',
  AJ ly3 S3 W3 m' md' ->
  (forall k (x : bv 5), In k [2; 9; 8; 18; 19; 25; 20; 3; 4] -> bv_unsigned x = k -> getr R' x = getr R3 x) ->
  UNS m' ->
  (forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) m' a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  um_base SK B cx fpos ly3 S3 W3 (mkst R' pc' m' (seg_rom SEGS)) md'.
Proof.
  intros R' pc' m' md' HJ2 PR HFR HPRES Hfd' Hfs'.
  pose proof eb_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & Gsp).
  pose proof (uw_F SK B LAWS cx fpos ly3 S3 W3 ms3 md3 HB) as (F1 & F2 & F3 & F4).
  pose proof eb_consts as (_ & _ & _ & _ & _ & _ & _ & _ & C9 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & Hfr3 & Hnin & HfS & Hperm & HS1 & Hfa & B2 & B9 & B8 & B18 & B19 & B25
    & B20 & B3 & B4 & Bra & Bsv & Bfl & BFp & BSp & HK3 & Bfd & Bfs & Bro).
  assert (PR' : forall k (x : bv 5), In k [2; 9; 8; 18; 19; 25; 20; 3; 4] -> bv_unsigned x = k ->
    getr (ms_regs (mkst R' pc' m' (seg_rom SEGS))) x = getr R3 x) by exact PR.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HJ2|].
  split; [exact Hfr3|]. split; [exact Hnin|]. split; [exact HfS|]. split; [exact Hperm|].
  split; [exact HS1|]. split; [exact Hfa|].
  split; [etransitivity; [refine (PR' 2 _ _ _); [cbn; tauto | reflexivity] | exact B2]|].
  split; [etransitivity; [refine (PR' 9 _ _ _); [cbn; tauto | reflexivity] | exact B9]|].
  split; [etransitivity; [refine (PR' 8 _ _ _); [cbn; tauto | reflexivity] | exact B8]|].
  split; [etransitivity; [refine (PR' 18 _ _ _); [cbn; tauto | reflexivity] | exact B18]|].
  split; [etransitivity; [refine (PR' 19 _ _ _); [cbn; tauto | reflexivity] | exact B19]|].
  split; [etransitivity; [refine (PR' 25 _ _ _); [cbn; tauto | reflexivity] | exact B25]|].
  split; [etransitivity; [refine (PR' 20 _ _ _); [cbn; tauto | reflexivity] | exact B20]|].
  split; [etransitivity; [refine (PR' 3 _ _ _); [cbn; tauto | reflexivity] | exact B3]|].
  split; [etransitivity; [refine (PR' 4 _ _ _); [cbn; tauto | reflexivity] | exact B4]|].
  cbn [ms_mem mkst].
  split; [rewrite <- Bra; apply uw_rdword_ext; intros i Hi; apply HFR; lia|].
  split; [intros j Hj; rewrite <- (Bsv j Hj); apply uw_rdword_ext; intros i Hi; apply HFR; lia|].
  split.
  { rewrite <- Bfl. apply uw_rdword_ext. intros i Hi. unfold UM_FLAGPTR in *. apply HFR; lia. }
  split; [intros a Ha; exact (HPRES a (BFp a Ha))|].
  split; [intros a Ha; exact (HPRES a (BSp a Ha))|].
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) W3 m3 W3 m'
      (um_sp cx - 8768) (um_sp cx) Ec Ec SLOT (uw_par SK B cx HPRE) ltac:(lia) ltac:(lia) HK3).
    - intros a Ha Hx. exact (HFR a Ha Hx).
    - intros a _ Hp. exact (HPRES a Hp).
    - intros a H. exact H.
    - intros a Ha. right. lia. }
  split; [rewrite Hfd'; exact Bfd|].
  split; [rewrite Hfs'; exact Bfs|].
  intros a Hro Ho He. pose proof (uw_roP_img RELRO_IMG a Hro) as Hi. pose proof (pa_img_range a Hi) as Hir.
  assert (HIE : PcapImgEnd.pcap_img_end = 0x654000) by reflexivity.
  rewrite (HFR a ltac:(lia) ltac:(lia)). exact (Bro a Hro Ho He).
Qed.

(* ---- 2. g_nl and the Post's m = 0 arm ---- *)
Lemma eb_apost0 : forall (R' : bvmap 5 word) (m' : word -> option byte), um_mk cx = 0 ->
  um_gnl_kept cx W3 m' -> reac_served_unmark_all_apost SEGS (um_regs cx) (um_m0 cx) R' (rdW W3 m').
Proof.
  intros R' m' HM0 HG. split.
  - intros _ kbs ((Hb & _) & HL). split; [split|exact HL].
    + apply (uw_abytes_move SEGS _ _ _ _ Hb). intros x Hx. unfold um_m0. apply uw_mbyte_eq. apply HG.
      unfold NK_SIZE in *. lia.
    + intros i Hi. apply eb_gnl_w. unfold NK_SIZE in *. lia.
  - intros HM. exfalso. exact (HM HM0).
Qed.

(* ---- 3. round 0 of the loop ---- *)
Section d.
Hypothesis HM : um_mk cx <> 0.
Hypothesis HMK : um_marks_kept cx W3 m3.

(* a table string, at a memory that differs from the cut's only at the slots, is the call's *)
Lemma eb_str_kept : forall m', UNS m' ->
  forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
  au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at SEGS (um_m0 cx) p n2 ->
  forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte SEGS (rdW W3 m') x = mbyte SEGS (um_m0 cx) x.
Proof.
  intros m' UN i n2 ix p Hn Hp Hc x Hx.
  pose proof eb_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & Gsp).
  pose proof (uw_acstr_range SEGS _ _ _ Hc) as Hr.
  pose proof (uw_pnl SK B cx HPRE) as (_ & _ & _ & _ & _ & (HL & H80 & HIF) & _).
  destruct (HIF i n2 ix Hn) as (_ & p' & Hp' & Hp'0 & Hc' & _).
  pose proof (uw_acstr_range SEGS _ _ _ Hc') as Hr'.
  pose proof (uw_au64_unique SEGS _ _ _ _ Hp Hp') as Ep. rewrite !Z.mod_small in Ep by lia. subst p'.
  assert (Hi80 : Z.of_nat i < 80).
  { assert (i < length (um_tab cx))%nat by (apply nth_error_Some; congruence). lia. }
  destruct (uw_ptb SK B cx HPRE i n2 ix p Hn Hp ltac:(lia)) as (Hrt & Hg & He & _ & Hmk).
  pose proof (Hmk HM) as Hm.
  destruct Hrt as (_ & _ & T3 & _ & _ & _ & T7). unfold apart_frame in T7. fold (um_sp cx) in T7.
  transitivity (mbyte SEGS (rdW W3 m3) x).
  - apply uw_mbyte_eq. apply UN; lia.
  - unfold um_m0. apply uw_mbyte_eq.
    exact (uw_tab_kept SK B cx fpos ly3 S3 W3 ms3 md3 HPRE HM HB i n2 ix p Hn Hi80 Hp ltac:(lia) Hc Hg Hm x Hx).
Qed.

Lemma eb_kinv0 : forall m', UNS m' -> um_kinv cx (rdW W3 m') (um_kbs cx) 0.
Proof.
  intros m' UN.
  pose proof eb_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & Gsp).
  pose proof eb_consts as (C1 & C2 & _).
  pose proof (uw_pnl SK B cx HPRE) as (HNL0 & HWF0 & HOP0 & _ & _ & HIF0 & _).
  assert (KG : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W3 m') x = mbyte SEGS (um_m0 cx) x).
  { intros x Hx. transitivity (mbyte SEGS (rdW W3 m3) x).
    - apply uw_mbyte_eq. apply UN; lia.
    - unfold um_m0. apply uw_mbyte_eq. apply HGK. exact Hx. }
  split.
  { destruct HNL0 as ((Hb & _) & HL). split; [split|exact HL].
    - apply (uw_abytes_move SEGS _ _ _ _ Hb). intros x Hx. apply KG. lia.
    - intros i Hi. apply eb_gnl_w. lia. }
  split; [exact HWF0|].
  split.
  { apply (ut_aiftab_move SEGS _ _ _ _ HIF0 KG).
    intros i n2 ix p Hn Hp Hc x Hx. exact (eb_str_kept m' UN i n2 ix p Hn Hp Hc x Hx). }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [unfold um_U, unmark; reflexivity|].
  split; [exact HOP0|]. split; [reflexivity|]. split; [reflexivity|]. cbn [Z.of_nat]. lia.
Qed.

Lemma eb_marks_kept : forall m', UNS m' -> um_marks_kept cx W3 m'.
Proof.
  intros m' UN a Ha.
  pose proof eb_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & Gsp).
  pose proof (uw_mkf SK B cx HPRE HM) as (_ & _ & _ & _ & Mkf & _).
  pose proof (uw_mk_rng SK B cx HPRE HM) as (Mk1 & Mk2).
  unfold apart_frame in Mkf. fold (um_sp cx) in Mkf.
  rewrite (UN a ltac:(unfold MK_SIZE in *; lia) ltac:(unfold MK_SIZE in *; lia)). exact (HMK a Ha).
Qed.

End d.

(* ==========================================================================
   4. The m = 0 run: `beqz s4` to the RELEASE cut
   ========================================================================== *)
Lemma eb_zero : um_mk cx = 0 -> ms_pc_val ms3 = w64 (BASE + UM_CUT_BR) -> um_rel_obl SK B ->
  SRr SEGS W3 (mkCfg ms3 md3) (um_post SK B cx).
Proof.
  intros HM0 Hpc HREL.
  pose proof HB as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
  pose proof (uw_ms_eta ms3 (Z_to_bv 64 (BASE + UM_CUT_BR)) (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc Hpc) as Hms.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
    symmetry. apply Z.mod_small. lia. }
  assert (U20 : ew E 20 = Z_to_bv 64 (um_mk cx)).
  { transitivity (getr (ms_regs ms3) 20); [exact (EREG 20%nat ltac:(lia))|].
    transitivity (getr (um_regs cx) 10); [exact R20|].
    unfold um_mk, aarg, argZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (HS : st_ok_pi SEGS VAL E eb_ss0 (restrict (w_H W3) ms3)).
  { rewrite Hms. rewrite restrict_mkst_fx. unfold eb_ss0.
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - split; [exact I|]. split; [|exact I]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
      rewrite (U_atom E 20 (um_mk cx) U20) by (rewrite HM0; lia). rewrite U_lit by lia. rewrite HM0. reflexivity. }
  assert (SHOK : sh_ok SEGS ebBx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUNTO := paj_run_to_x SK B LAWS (um_G cx) (uw_pg SK B cx HPRE) (um_XO cx) (um_OUT cx)).
  clear Hms.
  (* +0x18c: beqz s4 (taken) *)
  paj_run_to_tok RUNTO HS HJ3 SHOK uwSpan (AF_reac_served_unmark_all + 0x350).
  { unfold eb_ss0. cbn [ss_mem]. apply awr_ok_x_nil. }
  pmkst HS.
  assert (Em : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF. intros (r & [] & _). }
  rewrite Em in HJ3 |- *.
  apply (HREL cx fpos ly3 S3 W3 _ _ HPRE).
  split; [reflexivity|].
  split; [cbn [ms_regs ms_mem mkst]; exact (eb_apost0 _ _ HM0 HGK)|].
  apply eb_base.
  - exact HJ3.
  - eb_pr HS EREG.
  - intros a _ _. reflexivity.
  - intros a Hp. exact Hp.
  - first [reflexivity | rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity].
  - first [reflexivity | rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity].
Qed.

(* ==========================================================================
   5. The m <> 0 runs: the check of m->n, then the TAIL cut (n = 0) or the loop set-up and the HEAD cut
   ========================================================================== *)
Lemma eb_nz : um_mk cx <> 0 -> um_marks_kept cx W3 m3 -> getr R3 26 = w64 SHADOW_OFF ->
  ms_pc_val ms3 = w64 (BASE + UM_CUT_BR) -> um_tail_obl SK B -> um_head_obl SK B 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (um_post SK B cx).
Proof.
  intros HM HMK R26 Hpc HTL HHD.
  pose proof eb_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & Gsp).
  pose proof eb_consts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & _).
  pose proof (uw_mkf SK B cx HPRE HM) as (Mk0 & Mkr & MkR & MkH & Mkf & Mkg & Mke & Mka & Mkw).
  pose proof (uw_mk_rng SK B cx HPRE HM) as (Mk1 & Mk2).
  pose proof (uw_F SK B LAWS cx fpos ly3 S3 W3 ms3 md3 HB) as (F1 & F2 & F3 & F4).
  unfold apart_frame in Mkf. fold (um_sp cx) in Mkf.
  unfold amem_range in Mkr. rewrite C9, C10, C11 in Mkr.
  assert (Hn : 0 <= um_n cx <= 32) by (destruct Mkw as (Hn & _); unfold um_n; rewrite C7 in Hn; lia).
  assert (Hlen : Z.of_nat (length (um_gbs cx)) = 516) by (destruct Mka as (_ & HL); rewrite C4 in HL; exact HL).
  pose proof HB as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & _ & _ & _ & _ & _ & _ & R2 & R9 & _ & _ & _ & R25 & R20 & _).
  pose proof HJ3 as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
  pose proof (uw_ms_eta ms3 (Z_to_bv 64 (BASE + UM_CUT_BR)) (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc Hpc) as Hms.
  remember (Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (um_n cx)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
    symmetry. apply Z.mod_small. lia. }
  assert (E32 : ew E 32 = Z_to_bv 64 (um_n cx)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ms_regs ms3) [Z_to_bv 64 (um_n cx)] 0). }
  assert (U9 : bv_unsigned (ew E 9) = um_sp1 cx).
  { rewrite (EREG 9%nat ltac:(lia)). change (Z_to_bv 5 (Z.of_nat 9)) with (Z_to_bv 5 9).
    transitivity (bv_unsigned (getr (ms_regs ms3) 9)); [reflexivity|]. rewrite R9. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (U20 : ew E 20 = Z_to_bv 64 (um_mk cx)).
  { transitivity (getr (ms_regs ms3) 20); [exact (EREG 20%nat ltac:(lia))|].
    transitivity (getr (um_regs cx) 10); [exact R20|].
    unfold um_mk, aarg, argZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (U20' : bv_unsigned (ew E 20) = um_mk cx) by (rewrite U20; apply unsigned_lit_small; lia).
  assert (U26 : ew E 26 = Z_to_bv 64 0x7fff8000).
  { transitivity (getr (ms_regs ms3) 26); [exact (EREG 26%nat ltac:(lia))|]. exact R26. }
  assert (U26' : bv_unsigned (ew E 26) = 0x7fff8000) by (rewrite U26; apply unsigned_lit_small; lia).
  assert (U25 : ew E 25 = Z_to_bv 64 (um_F cx fpos)).
  { transitivity (getr (ms_regs ms3) 25); [exact (EREG 25%nat ltac:(lia))|]. exact R25. }
  assert (E32' : bv_unsigned (ew E 32) = um_n cx) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (E291 : ew E 291 = Z_to_bv 64 0x213c0).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 291%nat with (A_OBJ 50).
    rewrite (lv_obj LV 50 ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (E292 : ew E 292 = Z_to_bv 64 0x214e0).
  { subst E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 292%nat with (A_OBJ 51).
    rewrite (lv_obj LV 51 ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (HS : st_ok_pi SEGS VAL E eb_ss1 (restrict (w_H W3) ms3)).
  { rewrite Hms. rewrite restrict_mkst_fx. unfold eb_ss1.
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold region_ok, eb_slot.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres3. lia.
      + unfold region_ok, eb_mk.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U20'. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (um_mk cx) 0 4 (SOff 32 0) (um_n cx)).
        * rewrite denot_lit_U, (U_atom E 32 (um_n cx) E32) by lia. reflexivity.
        * change (8 * Z.of_N 4) with 32. lia.
        * cbn. lia.
        * rewrite Z.add_0_r. apply eb_val_mem_n; [exact (uw_marks3 SK B cx W3 ms3 HPRE HM HMK) | lia].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val eb_slot eb_mk]. rewrite U9, U20'.
      split; [split; [lia | exact I] | split; exact I].
    - unfold eb_f1. split; [|split; [|exact I]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U20', U26', E32'.
        split; [split; [lia|]; split; [change (2 ^ 5) with 32; lia | lia]|].
        split; [split; [lia|]; split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]|].
        split; [split; [lia|]; split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]|].
        split; [split; [lia|]; split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia] | exact I].
      + cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_ne_U. rewrite (U_atom E 20 (um_mk cx) U20) by lia. rewrite U_lit by lia.
        apply negb_true_iff, Z.eqb_neq. exact HM. }
  assert (SHOK : sh_ok SEGS ebBx ebSH E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, ebSH. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, ebBx.
    cbn [she_m she_lo she_hi]. rewrite (U_atom E 26 0x7fff8000 U26) by lia.
    rewrite (U_atom E 20 (um_mk cx) U20) by lia. rewrite Z.add_0_r, Z.sub_0_r. split.
    - exact (proj1 (uw_shadow3 SK B LAWS TB cx fpos ly3 S3 W3 ms3 md3 HPRE HM HB (um_mk cx) MK_SIZE ltac:(lia)
        ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
                (uw_pg SK B cx HPRE) (uw_pj SK B cx HPRE) (uw_pajw SK B cx HPRE x (uw_wr_mk cx x HM Hx))); lia)
        MkR MkH)).
    - intros a Ha Hsh. lia. }
  pose (RUN := paj_run_x SK B LAWS (um_G cx) (uw_pg SK B cx HPRE) (um_XO cx) (um_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (um_G cx) (uw_pg SK B cx HPRE) (um_XO cx) (um_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  clear Hms.
  (* +0x18c .. +0x1a4: beqz s4; the shadow check of m (token); lw a0, 0(s4); blez a0 *)
  paj_run_tok RUN HS HJ3 SHOK uwSpan.
  { unfold eb_ss1. cbn [ss_mem]. eb_awr U9. }
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ SLOT HFr ltac:(eb_frame_tac)) as UN1.
  pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P1.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK uwSpan.
  - (* n = 0: blez taken, the TAIL cut *)
    rewrite (eb_ge0 E (um_n cx) E32 Hn) in Hc. apply Z.leb_le in Hc.
    paj_run_to_tok RUNTO HS HJ3 SHOK uwSpan (AF_reac_served_unmark_all + 0x340).
    { eb_awr U9. }
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ SLOT HFr ltac:(eb_frame_tac)) as UN2.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      assert (UN : UNS (ms_mem msc)) by (intros a Ha Hx; rewrite (UN2 a Ha Hx); exact (UN1 a Ha Hx));
      assert (P : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem msc) a)
        by (intros a Hp; exact (P2 a (P1 a Hp)))
    end.
    pmkst HS.
    apply (HTL cx fpos ly3 S3 W3 _ _ HPRE).
    split; [reflexivity|]. split; [exact HM|].
    split; [cbn [ms_mem mkst]; exact (eb_marks_kept HM HMK _ UN)|].
    split; [exists (um_kbs cx); cbn [ms_mem mkst]; replace (Z.to_nat (um_n cx)) with 0%nat by lia;
            exact (eb_kinv0 HM _ UN)|].
    apply eb_base.
    + exact HJ3.
    + eb_pr HS EREG.
    + exact UN.
    + exact P.
    + first [reflexivity | rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity | rewrite !(proj1 (wvb_fds_fs _ _ _)); reflexivity].
    + first [reflexivity | rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity | rewrite !(proj2 (wvb_fds_fs _ _ _)); reflexivity].
  - (* n > 0: the loop set-up, the HEAD cut, round 0 *)
    rewrite (eb_ge0 E (um_n cx) E32 Hn) in Hc. apply Z.leb_gt in Hc.
    paj_run_to_tok RUNTO HS HJ3 SHOK uwSpan (AF_reac_served_unmark_all + 0x1d8).
    { eb_awr U9. }
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ SLOT HFr ltac:(eb_frame_tac)) as UN2.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      assert (UN : UNS (ms_mem msc)) by (intros a Ha Hx; rewrite (UN2 a Ha Hx); exact (UN1 a Ha Hx));
      assert (P : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem msc) a)
        by (intros a Hp; exact (P2 a (P1 a Hp)));
      pose proof (st_ok_pi_region_nth E _ _ 0%nat _ HS eq_refl) as RG
    end.
    destruct RG as (_ & _ & _ & RC). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict mkst] in RC.
    rewrite U9 in RC.
    pose proof (Forall_inv RC) as C16'. pose proof (Forall_inv (Forall_inv_tail RC)) as C24'. clear RC.
    pmkst HS.
    apply (HHD cx fpos ly3 S3 W3 _ _ HPRE).
    split; [reflexivity|].
    split.
    { unfold um_loop. cbn [ms_regs ms_mem mkst].
      split; [exact HM|]. split; [cbn [Z.of_nat]; lia|].
      split.
      { prreg_raw HS (21%bv : bv 5) Hr. rewrite Hr, denot_lit_U.
        rewrite (U_atom_off E 25 (um_F cx fpos) 32 U25) by lia. rewrite C14. reflexivity. }
      split.
      { prreg_raw HS (22%bv : bv 5) Hr. rewrite Hr, denot_lit_U.
        rewrite (U_atom_off E 20 (um_mk cx) 4 U20) by lia. unfold w64. f_equal. rewrite C5, C6. lia. }
      split.
      { prreg_raw HS (23%bv : bv 5) Hr. rewrite Hr, denot_lit_U.
        rewrite (U_atom E 291 0x213c0 E291) by lia. rewrite C12. reflexivity. }
      split.
      { prreg_raw HS (24%bv : bv 5) Hr. rewrite Hr. cbn [sv_denot]. unfold w64.
        apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
      split.
      { prreg_raw HS (26%bv : bv 5) Hr. rewrite Hr, denot_lit_U.
        rewrite (eb_U_shadow E (um_mk cx) U20 U26) by lia. rewrite C8. reflexivity. }
      split.
      { prreg_raw HS (27%bv : bv 5) Hr. rewrite Hr. reflexivity. }
      split.
      { rewrite C15. apply rdword_of_val_mem; [|lia].
        exact (eb_chunk8_vm SEGS E _ _ 24 (SOff 292 0) 0x214e0 C24'
          ltac:(rewrite denot_lit_U, (U_atom E 292 0x214e0 E292) by lia; reflexivity) ltac:(lia)). }
      split.
      { rewrite C16. pose proof (eb_land7 (um_mk cx) ltac:(lia)).
        apply rdword_of_val_mem; [|lia].
        exact (eb_chunk8_vm SEGS E _ _ 16 _ (Z.land (um_mk cx) 7 + 3) C16'
          ltac:(rewrite denot_lit_U, (eb_U_lim E (um_mk cx) U20) by lia; reflexivity) ltac:(lia)). }
      exact (eb_marks_kept HM HMK _ UN). }
    split; [exists (um_kbs cx); cbn [ms_mem mkst]; exact (eb_kinv0 HM _ UN)|].
    apply eb_base.
    + exact HJ3.
    + eb_pr HS EREG.
    + exact UN.
    + exact P.
    + first [reflexivity | rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity | rewrite !(proj1 (wvb_fds_fs _ _ _)); reflexivity].
    + first [reflexivity | rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity | rewrite !(proj2 (wvb_fds_fs _ _ _)); reflexivity].
Qed.

End c.

Theorem um_entryB : um_rel_obl SK B -> um_tail_obl SK B -> um_head_obl SK B 0 -> um_br_obl SK B.
Proof.
  intros HREL HTL HHD cx fpos ly3 S3 W3 ms3 md3 HPRE (Hpc & R26 & HGK & HMKK & HB).
  destruct (Z.eq_dec (um_mk cx) 0) as [HM0 | HM].
  - exact (eb_zero cx fpos ly3 S3 W3 ms3 md3 HPRE HB HGK HM0 Hpc HREL).
  - exact (eb_nz cx fpos ly3 S3 W3 ms3 md3 HPRE HB HGK HM (HMKK HM) R26 Hpc HTL HHD).
Qed.

About um_entryB.
Print Assumptions um_entryB.

End b.
End a.
