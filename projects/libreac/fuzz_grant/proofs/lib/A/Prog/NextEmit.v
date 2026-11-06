(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE25.v. *)
(* The walk of reac_headamp_tx_next's emit block (fuzz_grant.asan 0x854a0 .. 0x85400, the
   ret): NextEmitDefs.nx_emit_spec.

   The block has no call.  It writes the channel, the parameter and the value of the record
   into the three bytes the caller holds, then the cursor's wait (444) or the replay width
   (437), and the silence counter (456), and returns 1.  Nine inline shadow checks of the
   memory-checking runtime guard those accesses; every one of them is discharged from the
   shadow entries of em_SH, so the obligation list of each run is empty and the error path,
   a call of one of the __asan_report_ entries, is not reached.

   The table's layout is a Theorem Labs lane's LAY_TX (lib/A/Prog/HeadampTxEffective.v) and the answer is
   Pau Aliagas's emit_res (lib/Prog/NextModel.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaRun PaShadow PaStep GrantSyms GrantList GrantAddr GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaJournal GrantPaLib GrantBase YC1g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
NextArith HeadampTxEffective HeadampTxNext NextReplayDefs NextEmitDefs KindOfLink1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at EMIT ------------------------------------------------------- *)

(* The shadow byte's address of the table's field at offset k, as the code builds it. *)
Definition SHX (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 k) (SLit 3)) (SOff 32 0).

(* The registers the scan leaves: sp below its own frame, t0 the shadow base, t1/t2/t3 the
   shadow bytes' addresses of 437, 444 and 440, a4/a5/a6 those fields' addresses and t6 the
   set array. *)
Definition sr_em : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (5%bv : bv 5) (SOff 32 0))
    (6%bv : bv 5) (SHX 437))
    (7%bv : bv 5) (SHX 444))
    (28%bv : bv 5) (SHX 440))
    (14%bv : bv 5) (SOff 10 444))
    (15%bv : bv 5) (SOff 10 437))
    (16%bv : bv 5) (SOff 10 440))
    (31%bv : bv 5) (SOff 10 144).

(* The ten callee-saved registers the prologue put below sp (atom 2 is sp - 80). *)
Definition STKR : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0
  [ YP09.mkChunk 72 (CVal 8 (SOff 33 0)); YP09.mkChunk 64 (CVal 8 (SOff 34 0));
    YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 48 (CVal 8 (SOff 36 0));
    YP09.mkChunk 40 (CVal 8 (SOff 37 0)); YP09.mkChunk 32 (CVal 8 (SOff 38 0));
    YP09.mkChunk 24 (CVal 8 (SOff 39 0)); YP09.mkChunk 16 (CVal 8 (SOff 40 0));
    YP09.mkChunk 8 (CVal 8 (SOff 41 0)); YP09.mkChunk 0 (CVal 8 (SOff 42 0)) ].
Definition T437 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 437 438 437 438 [YP09.mkChunk 437 (CVal 1 (SOff 48 0))].
Definition T440 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 440 444 440 440 [YP09.mkChunk 440 (CVal 4 (SOff 43 0))].
Definition T444 : YP09.region :=
  YP09.mkRegion (Some 10%nat) 444 448 444 448 [YP09.mkChunk 444 (CVal 4 (SOff 49 0))].
Definition T456 : YP09.region := YP09.mkRegion (Some 10%nat) 456 460 456 460 [].
Definition OUTC : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 1 [].
Definition OUTP : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [].
Definition OUTV : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [].
(* The cell the block reads: its value byte at 0 and its set byte at 144. *)
Definition RXE : YP09.region := YP09.mkRegion (Some 45%nat) 0 145 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 47 0)); YP09.mkChunk 144 (CVal 1 (SOff 46 0))].
Definition em_regions : list YP09.region :=
  [STKR; T437; T440; T444; T456; OUTC; OUTP; OUTV; RXE].

Definition EPTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition EOUT : afact := mkAF 4096 (2 ^ 47 - 1) 0.
(* tx + (j mod 3) + 3 * (c mod 64), the address of the cell the code builds. *)
Definition XA : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 8 0)) (SMd M_MUL (SOff 44 0) (SLit 3)).
Definition em_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46 - 80) (2 ^ 47 - 80) 4); (8%nat, mkAF 0 2 0); (10%nat, EPTR 4);
            (11%nat, EOUT); (12%nat, EOUT); (13%nat, EOUT); (19%nat, mkAF 0 509 0);
            (29%nat, mkAF 0 765 0); (32%nat, mkAF SB_NX SB_NX 0); (43%nat, mkAF 1 765 0);
            (44%nat, mkAF 0 63 0); (45%nat, EPTR 0); (46%nat, mkAF 0 255 0);
            (47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0); (49%nat, mkAF 0 4294967295 0) ]
          []
          [ (SAlu ALU_AND (SOff 19 0) (SLit 63), SOff 44 0); (XA, SOff 45 0) ].
Definition em_SH : list shent :=
  [ mkSHE 10 0 460; mkSHE 11 0 1; mkSHE 12 0 1; mkSHE 13 0 1; mkSHE 45 0 152 ].
Definition ss_em : sstate := mkSS EMIT sr_em em_regions None em_facts.

(* The channel the cell index uses: the code masks the channel to six bits. *)
Definition em_ch (T : list byte) (j : Z) : Z := (tb T 436 + j / 3) mod 64.

(* The atoms above the registers: the shadow base, the ten saved registers, the cursor the
   scan stored, the masked channel, the cell's address and its two bytes. *)
Definition em_extra (regs : bvmap 5 word) (tx j : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; bv_unsigned (getr regs 1); bv_unsigned (getr regs 8); bv_unsigned (getr regs 9);
      bv_unsigned (getr regs 18); bv_unsigned (getr regs 19); bv_unsigned (getr regs 20);
      bv_unsigned (getr regs 21); bv_unsigned (getr regs 22); bv_unsigned (getr regs 23);
      bv_unsigned (getr regs 24);
      j + 1; em_ch T j; tx + 3 * em_ch T j + j mod 3;
      tb (set4 T 440 (j + 1)) (144 + 3 * em_ch T j + j mod 3);
      tb (set4 T 440 (j + 1)) (3 * em_ch T j + j mod 3);
      tb (set4 T 440 (j + 1)) 437; u32at (set4 T 440 (j + 1)) 444 ].

(* The callee-saved registers, and what the epilogue leaves in them. *)
Definition CSR : list (bv 5) :=
  map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition CSE : list sv :=
  [ SOff 2 80; SOff 3 0; SOff 4 0; SOff 34 0; SOff 35 0; SOff 36 0; SOff 37 0; SOff 38 0;
    SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0; SOff 25 0; SOff 26 0; SOff 27 0 ].

(* ---- small arithmetic facts ------------------------------------------------------------ *)

Lemma em_bow0 : forall k, YP09.byte_of_word (Z_to_bv 64 0) k = Z_to_bv 8 0.
Proof.
  intros k. unfold YP09.byte_of_word. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma em_bow11 : forall d, 0 <= d < 4 ->
  YP09.byte_of_word (Z_to_bv 64 11) d = Z_to_bv 8 (nth (Z.to_nat d) [11; 0; 0; 0] 0).
Proof.
  intros d Hd. unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
    vm_compute; reflexivity.
Qed.

Lemma tb_setb_in : forall T k v, length T = 460%nat -> 0 <= k < 460 -> 0 <= v < 256 ->
  tb (setb T k v) k = v.
Proof.
  intros T k v HL Hk Hv. unfold tb, setb.
  rewrite (SegSetModel.nth_upd_bytes T (le1 (Z_to_bv 64 v)) (Z.to_nat k) (Z.to_nat k))
    by (rewrite length_le1; lia).
  rewrite length_le1.
  replace ((Z.to_nat k <=? Z.to_nat k)%nat && (Z.to_nat k <? Z.to_nat k + 1)%nat)%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat k - Z.to_nat k)%nat with 0%nat by lia.
  rewrite le1_byte_of_word. unfold YP09.byte_of_word.
  rewrite unsigned_lit_small by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

Lemma em_mod64 : forall c, 0 <= c -> c mod 256 <= 47 -> c mod 64 = c mod 256.
Proof.
  intros c H0 H47.
  assert (Hd : (c mod 256) mod 64 = c mod 64).
  { replace (c mod 256) with (c + (- (c / 256) * 4) * 64)
      by (pose proof (Z.div_mod c 256 ltac:(lia)); lia).
    apply Z_mod_plus_full. }
  rewrite <- Hd. apply Z.mod_small.
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)). lia.
Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition EM (regs regsj : bvmap 5 word) (tx j : Z) (T : list byte) : env :=
  Eimg (Ereg regsj (em_extra regs tx j T)).

Lemma denot_off0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
  rewrite zcanon_id by (apply u64_range). apply Z_to_bv_bv_unsigned.
Qed.

Lemma denot_SHX : forall (E : env) (tx k : Z),
  ew E 10 = Z_to_bv 64 tx -> ew E 32 = Z_to_bv 64 SB_NX ->
  0 <= tx -> 0 <= k -> tx + k < 2 ^ 47 ->
  sv_denot E (SHX k) = Z_to_bv 64 (SHADOW_OFF + (tx + k) / 8).
Proof.
  intros E tx k H10 H32 Ht Hk Htk. rewrite denot_lit_U. f_equal. unfold SHX.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_SRL (SOff 10 k) (SLit 3)) (SOff 32 0)). cbn [zalu_raw].
  rewrite U_srl3, (U_atom_off E 10 tx k H10 ltac:(lia) ltac:(lia)).
  rewrite (U_atom E 32 SB_NX H32) by (unfold SB_NX; lia).
  assert (Hq : 0 <= (tx + k) / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite zcanon_id by (unfold M64, SB_NX; lia). unfold SB_NX, SHADOW_OFF. lia.
Qed.

Lemma em_dflt_val : forall (E : env) (p : Z), 0 <= p < 256 -> ew E 8 = Z_to_bv 64 p ->
  sv_denot E (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1)) (SLit 5)) = w64 (dflt p).
Proof.
  intros E p Hp E8.
  assert (HI : U E (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1))
               = Z.b2z ((p + -2) mod 18446744073709551616 <? 1)).
  { rewrite U_SAlu. cbn [zalu_raw].
    rewrite U_SOff, E8, unsigned_lit_small by lia.
    rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
    unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
    destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z]; apply Z.mod_small; lia. }
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite HI.
  rewrite U_SLit, (zcanon_id 5) by (unfold M64; lia).
  change (Z.land 5 63) with 5.
  rewrite <- (dflt_code_all p ltac:(lia)).
  unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616. apply Z.mod_small.
  destruct ((p + -2) mod 18446744073709551616 <? 1); cbn [Z.b2z];
    rewrite Z.shiftl_mul_pow2 by lia; lia.
Qed.

Lemma em_aview_byte : forall (W : world SEGS) m a (v : Z), 0 <= v ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (YP09.byte_of_word (Z_to_bv 64 v) 0) ->
  aview SEGS (w_H W) m a = Some (v mod 256).
Proof.
  intros W m a v Hv HM. unfold aview. rewrite HM. cbn [option_map]. f_equal.
  unfold YP09.byte_of_word. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (v mod 18446744073709551616)
    with (v + (- (v / 18446744073709551616) * 72057594037927936) * 256)
    by (pose proof (Z.div_mod v 18446744073709551616 ltac:(lia)); lia).
  apply Z_mod_plus_full.
Qed.

(* A byte's shadow byte lies in no range this call writes, so the caller's "marked usable"
   still holds at the journal's memory. *)
Lemma em_ra_keep : forall (W : world SEGS) memc m (sp tx chp parp valp d p : Z),
  nx_same W memc m sp tx chp parp valp d ->
  tx <= d < tx + TX_SIZE ->
  2 ^ 46 <= sp -> 4096 <= tx -> in_app tx 460 ->
  4096 <= p -> p + 1 <= 2 ^ 47 ->
  ~ (SHADOW_OFF <= chp < SHADOW_OFF + 17592186044416) ->
  ~ (SHADOW_OFF <= parp < SHADOW_OFF + 17592186044416) ->
  ~ (SHADOW_OFF <= valp < SHADOW_OFF + 17592186044416) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 1 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p 1.
Proof.
  intros W memc m sp tx chp parp valp d p HS Hd Hsp Htx Hia Hp0 Hp1 Hc5 Hp5 Hv5 HRA.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hia as (Hia0 & Hia1).
  assert (Hq : 0 <= p / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  intros x Hx. assert (x = p) as -> by lia.
  destruct (HRA p ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (nx_same_aview W memc m sp tx chp parp valp d (SHADOW_OFF + p / 8));
    [exact HS | unfold SHADOW_OFF in *; lia | exact Hd
     | unfold NEXT_STK, SHADOW_OFF in *; lia |].
  unfold nx_touch, TX_SIZE, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  intros [Hz | [Hz | [Hz | Hz]]]; lia.
Qed.

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* A shadow entry for a range inside the table, named by an atom that is not the block's
   base (cgif's shent_of_block_at, lib/A/Prog/HeadampTxEffective.v:383). *)
Lemma em_shent : forall ly S (W : world SEGS) mem md (Ex : env) (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex BxN = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS BxN Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

(* A chunk of the stack region: one of the ten registers the prologue saved. *)
Lemma em_saved_chunk : forall (Ex : env) (W : world SEGS) m (regs : bvmap 5 word)
    (sp : Z) (n : nat) (off : Z) (r : bv 5),
  ew Ex n = Z_to_bv 64 (bv_unsigned (getr regs r)) ->
  val_mem SEGS (mrestrict (w_H W) m) (sp - NEXT_STK + off) 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok SEGS Ex (mrestrict (w_H W) m) (sp - NEXT_STK) (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros Ex W m regs sp n off r Hew Hval.
  pose proof (u64_range (getr regs r)) as Hr. unfold M64 in Hr.
  apply (chunk_ok_val SEGS Ex _ (sp - NEXT_STK) off 8 (SOff n 0) (bv_unsigned (getr regs r))).
  - rewrite denot_off0, Hew. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616. lia.
  - cbn. lia.
  - exact Hval.
Qed.

(* ---- the entry: the machine at EMIT is the symbolic state ss_em ------------------------ *)

Lemma em_entry :
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
         (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 (j + 1))) ->
  0 <= j < 3 * tb T 437 ->
  nx_at_emit regs regsj tx chp parp valp T j ->
  st_ok_pi SEGS VAL (EM regs regsj tx j T) ss_em
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + EMIT)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN em_SH (EM regs regsj tx j T) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T j HCTX HMID HSAVE HOBJ HJ3 HAT.
  destruct HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rc & Rp & Rv &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Htab & Wc & Wp & Wv & Hra & Hra4 & Hgp & Htp &
    H10 & H11 & H12 & H13 & HTl & HI & HTobj & Hpres).
  destruct Hspr as (Hsp46 & Hsp47).
  destruct HMID as (HJ & HSAME & HpresJ & HpresK).
  destruct HAT as (Hkeep & A2 & A5 & A6 & A7 & A28 & A8 & A19 & A10 & A11 & A12 & A13 &
    A14 & A15 & A16 & A29 & A31).
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  destruct HSAVE as (Sv1 & Sv8 & Sv9 & Sv18 & Sv19 & Sv20 & Sv21 & Sv22 & Sv23 & Sv24).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size TX_SIZE) with 460 in Htxceil, Htxia, Htxpres.
  pose proof (HeadampTxEffective.tb_range T 436) as R436.
  pose proof (HeadampTxEffective.tb_range T 437) as R437.
  assert (HLj : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
  assert (Hchr : 0 <= em_ch T j < 64)
    by (unfold em_ch; apply Z.mod_pos_bound; lia).
  assert (Hpr : 0 <= j mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (Hcr : 0 <= tb T 436 + j / 3 <= 509).
  { split; [pose proof (Z.div_pos j 3 ltac:(lia) ltac:(lia)); lia|].
    assert (j / 3 < 255) by (apply Z.div_lt_upper_bound; lia). lia. }
  set (CH := em_ch T j) in *. set (P := j mod 3) in *.
  set (T1 := set4 T 440 (j + 1)) in *.
  pose proof (HeadampTxEffective.tb_range T1 (144 + 3 * CH + P)) as R46.
  pose proof (HeadampTxEffective.tb_range T1 (3 * CH + P)) as R47.
  pose proof (u64_range (getr regs 1)) as U1. unfold M64 in U1.
  rewrite restrict_mkst_fx.
  set (E := EM regs regsj tx j T).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj (em_extra regs tx j T)) n)
    by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - NEXT_STK))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 2 2%bv eq_refl); exact A2).
  assert (E5 : ew E 5 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 5 5%bv eq_refl); exact A5).
  assert (E8 : ew E 8 = Z_to_bv 64 P)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 8 8%bv eq_refl); exact A8).
  assert (E10 : ew E 10 = Z_to_bv 64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl); exact A10).
  assert (E11 : ew E 11 = Z_to_bv 64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl); exact A11).
  assert (E12 : ew E 12 = Z_to_bv 64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl); exact A12).
  assert (E13 : ew E 13 = Z_to_bv 64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 13 13%bv eq_refl); exact A13).
  assert (E19 : ew E 19 = Z_to_bv 64 (tb T 436 + j / 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 19 19%bv eq_refl); exact A19).
  assert (E29 : ew E 29 = Z_to_bv 64 (3 * tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 29 29%bv eq_refl); exact A29).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (bv_unsigned (getr regs 1)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned (getr regs 8)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (bv_unsigned (getr regs 9)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (bv_unsigned (getr regs 18)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 (bv_unsigned (getr regs 19)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 5)).
  assert (E38 : ew E 38 = Z_to_bv 64 (bv_unsigned (getr regs 20)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 6)).
  assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned (getr regs 21)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 7)).
  assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned (getr regs 22)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 8)).
  assert (E41 : ew E 41 = Z_to_bv 64 (bv_unsigned (getr regs 23)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 9)).
  assert (E42 : ew E 42 = Z_to_bv 64 (bv_unsigned (getr regs 24)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 10)).
  assert (E43 : ew E 43 = Z_to_bv 64 (j + 1))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 11)).
  assert (E44 : ew E 44 = Z_to_bv 64 CH)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 12)).
  assert (E45 : ew E 45 = Z_to_bv 64 (tx + 3 * CH + P))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 13)).
  assert (E46 : ew E 46 = Z_to_bv 64 (tb T1 (144 + 3 * CH + P)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 14)).
  assert (E47 : ew E 47 = Z_to_bv 64 (tb T1 (3 * CH + P)))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 15)).
  assert (E48 : ew E 48 = Z_to_bv 64 (tb T1 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 16)).
  assert (E49 : ew E 49 = Z_to_bv 64 (u32at T1 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 17)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - NEXT_STK)
    by (rewrite E2; apply unsigned_lit_small; unfold NEXT_STK; lia).
  assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (Eu11 : bv_unsigned (ew E 11) = chp) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (Eu12 : bv_unsigned (ew E 12) = parp) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (Eu13 : bv_unsigned (ew E 13) = valp) by (rewrite E13; apply unsigned_lit_small; lia).
  assert (Eu45 : bv_unsigned (ew E 45) = tx + 3 * CH + P)
    by (rewrite E45; apply unsigned_lit_small; lia).
  assert (HUB : U E BxN = SHADOW_OFF).
  { unfold U, BxN. rewrite denot_off0, E32. rewrite unsigned_lit_small by (unfold SB_NX; lia).
    reflexivity. }
  assert (HBY : forall i, tx_fbyte i = true ->
            mbyte SEGS (mrestrict (w_H W) memj) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0)))
    by (exact (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ)).
  split.
  - unfold ss_em. apply pa_entry_st_ok_full.
    + (* the registers *)
      unfold sr_em.
      apply regs_ok_rereg; [|reflexivity|
        rewrite denot_lit_U, (U_atom_off E 10 tx 144 E10 ltac:(lia) ltac:(lia)); exact A31].
      apply regs_ok_rereg; [|reflexivity|
        rewrite denot_lit_U, (U_atom_off E 10 tx 440 E10 ltac:(lia) ltac:(lia)); exact A16].
      apply regs_ok_rereg; [|reflexivity|
        rewrite denot_lit_U, (U_atom_off E 10 tx 437 E10 ltac:(lia) ltac:(lia)); exact A15].
      apply regs_ok_rereg; [|reflexivity|
        rewrite denot_lit_U, (U_atom_off E 10 tx 444 E10 ltac:(lia) ltac:(lia)); exact A14].
      apply regs_ok_rereg; [|reflexivity|
        rewrite (denot_SHX E tx 440 E10 E32 ltac:(lia) ltac:(lia) ltac:(lia)); exact A28].
      apply regs_ok_rereg; [|reflexivity|
        rewrite (denot_SHX E tx 444 E10 E32 ltac:(lia) ltac:(lia) ltac:(lia)); exact A7].
      apply regs_ok_rereg; [|reflexivity|
        rewrite (denot_SHX E tx 437 E10 E32 ltac:(lia) ltac:(lia) ltac:(lia)); exact A6].
      apply regs_ok_rereg; [|reflexivity| rewrite denot_off0, E32; exact A5].
      subst E. unfold EM. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + (* the regions *)
      unfold em_regions, STKR, T437, T440, T444, T456, OUTC, OUTP, OUTV, RXE.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * (* the saved registers *)
        cbn [base_val]. rewrite Usp.
        split; [unfold NEXT_STK; lia|]. split; [unfold NEXT_STK; lia|].
        split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 33 72 1%bv E33).
           replace (spZ regs - NEXT_STK + 72) with (spZ regs - 8) by (unfold NEXT_STK; lia).
           exact Sv1.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 34 64 8%bv E34).
           replace (spZ regs - NEXT_STK + 64) with (spZ regs - 16) by (unfold NEXT_STK; lia).
           exact Sv8.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 35 56 9%bv E35).
           replace (spZ regs - NEXT_STK + 56) with (spZ regs - 24) by (unfold NEXT_STK; lia).
           exact Sv9.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 36 48 18%bv E36).
           replace (spZ regs - NEXT_STK + 48) with (spZ regs - 32) by (unfold NEXT_STK; lia).
           exact Sv18.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 37 40 19%bv E37).
           replace (spZ regs - NEXT_STK + 40) with (spZ regs - 40) by (unfold NEXT_STK; lia).
           exact Sv19.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 38 32 20%bv E38).
           replace (spZ regs - NEXT_STK + 32) with (spZ regs - 48) by (unfold NEXT_STK; lia).
           exact Sv20.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 39 24 21%bv E39).
           replace (spZ regs - NEXT_STK + 24) with (spZ regs - 56) by (unfold NEXT_STK; lia).
           exact Sv21.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 40 16 22%bv E40).
           replace (spZ regs - NEXT_STK + 16) with (spZ regs - 64) by (unfold NEXT_STK; lia).
           exact Sv22.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 41 8 23%bv E41).
           replace (spZ regs - NEXT_STK + 8) with (spZ regs - 72) by (unfold NEXT_STK; lia).
           exact Sv23.
        -- apply (em_saved_chunk E W memj regs (spZ regs) 42 0 24%bv E42).
           replace (spZ regs - NEXT_STK + 0) with (spZ regs - 80) by (unfold NEXT_STK; lia).
           exact Sv24.
      * (* 437 *)
        cbn [base_val]. rewrite Eu10. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). apply Htxpres. lia. }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 48 0) (tb T1 437)).
        -- rewrite denot_off0, E48. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. pose proof (HeadampTxEffective.tb_range T1 437). lia.
        -- cbn. lia.
        -- apply (nx_val1 (mrestrict (w_H W) memj) tx T1 437 HBY). vm_compute. reflexivity.
      * (* 440 *)
        cbn [base_val]. rewrite Eu10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 440 4 (SOff 43 0) (j + 1)).
        -- rewrite denot_off0, E43. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with 4294967296. lia.
        -- cbn. lia.
        -- replace (j + 1) with (u32at T1 440).
           ++ apply (nx_val4 (mrestrict (w_H W) memj) tx T1 440 HBY).
              intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
                vm_compute; reflexivity.
           ++ rewrite u32at_u32. subst T1. apply u32_set4; lia.
      * (* 444 *)
        cbn [base_val]. rewrite Eu10. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). apply Htxpres. lia. }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 444 4 (SOff 49 0) (u32at T1 444)).
        -- rewrite denot_off0, E49. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with 4294967296. pose proof (u32at_range T1 444). lia.
        -- cbn. lia.
        -- apply (nx_val4 (mrestrict (w_H W) memj) tx T1 444 HBY).
           intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
             vm_compute; reflexivity.
      * (* 456 *)
        cbn [base_val]. rewrite Eu10. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Htxpres. lia.
      * (* the channel byte *)
        cbn [base_val]. rewrite Eu11. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (chp + o) with chp by lia.
        apply (apresent_writable SEGS). apply HpresK. exact Pc.
      * (* the parameter byte *)
        cbn [base_val]. rewrite Eu12. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (parp + o) with parp by lia.
        apply (apresent_writable SEGS). apply HpresK. exact Pp.
      * (* the value byte *)
        cbn [base_val]. rewrite Eu13. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (valp + o) with valp by lia.
        apply (apresent_writable SEGS). apply HpresK. exact Pv.
      * (* the cell *)
        cbn [base_val]. rewrite Eu45. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons.
        -- apply (chunk_ok_val SEGS E _ (tx + 3 * CH + P) 0 1 (SOff 47 0) (tb T1 (3 * CH + P))).
           ++ rewrite denot_off0, E47. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 1)) with 256. lia.
           ++ cbn. lia.
           ++ replace (tx + 3 * CH + P + 0) with (tx + (3 * CH + P)) by lia.
              exact (tx_cell_val SEGS _ tx T1 (3 * CH + P) ltac:(lia) HOBJ).
        -- apply Forall_cons; [|apply Forall_nil].
           apply (chunk_ok_val SEGS E _ (tx + 3 * CH + P) 144 1 (SOff 46 0)
                    (tb T1 (144 + 3 * CH + P))).
           ++ rewrite denot_off0, E46. reflexivity.
           ++ change (2 ^ (8 * Z.of_N 1)) with 256. lia.
           ++ cbn. lia.
           ++ replace (tx + 3 * CH + P + 144) with (tx + (144 + 3 * CH + P)) by lia.
              exact (tx_cell_val SEGS _ tx T1 (144 + 3 * CH + P) ltac:(lia) HOBJ).
    + (* the regions are apart *)
      apply pairwise_disjoint_of_extents.
      unfold em_regions, STKR, T437, T440, T444, T456, OUTC, OUTP, OUTV, RXE, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite Usp, Eu10, Eu11, Eu12, Eu13, Eu45.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hsp46 Hsp47 Hceil C1 Htx4096 Htxceil Hc0 Hc1 Hc2 Hc3 Hp0 Hp1 Hp2 Hp3
        Hv0 Hv1 Hv2 Hv3 Dcp Dcv Dpv Hchr Hpr.
      clear. unfold TX_SIZE, NEXT_STK. intros.
      repeat match goal with |- _ /\ _ => split end; lia.
    + (* the atoms, and the two aliases *)
      split; [|split].
      * cbn [em_facts f_atoms atoms_ok]. unfold afact_ok, EPTR, EOUT.
        cbn [af_lo af_hi af_al2].
        pose proof (HeadampTxEffective.tb_range T1 437) as R48.
        pose proof (u32at_range T1 444) as R49.
        rewrite Usp, E8, E10, E11, E12, E13, E19, E29, E32, E43, E44, E45, E46, E47, E48, E49.
        rewrite !unsigned_lit_small by (unfold SB_NX; lia).
        change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
        assert (Hal : (spZ regs - 80) mod 16 = 0).
        { replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia.
          rewrite Z_mod_plus_full. exact Hsp16. }

        revert Hal Hsp46 Hsp47 Hceil C1 Htx16 Htx4096 Htxceil Hc0 Hc1 Hp0 Hp1 Hv0 Hv1
          Hcr HJ3 R437 R46 R47 R48 R49 Hchr Hpr.
        clear. unfold TX_SIZE, NEXT_STK, SB_NX. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [em_facts f_conds conds_ok]. exact I.
      * cbn [em_facts f_alias alias_ok]. split; [|split; [|exact I]].
        -- apply U_inj. rewrite (U_and_lit E (SOff 19 0) 63) by lia.
           rewrite (U_atom E 19 (tb T 436 + j / 3) E19 ltac:(lia)).
           rewrite (U_atom E 44 CH E44 ltac:(lia)).
           subst CH. unfold em_ch. apply land_mod64.
        -- apply U_inj. unfold XA.
           rewrite (U_SAlu E ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 8 0))
                      (SMd M_MUL (SOff 44 0) (SLit 3))). cbn [zalu_raw].
           rewrite (U_SAlu E ALU_ADD (SOff 10 0) (SOff 8 0)). cbn [zalu_raw].
           rewrite (U_SMd E M_MUL (SOff 44 0) (SLit 3)). cbn [zmd_raw].
           rewrite (U_atom E 10 tx E10 ltac:(lia)), (U_atom E 8 P E8 ltac:(lia)),
             (U_atom E 44 CH E44 ltac:(lia)), U_SLit.
           rewrite (U_atom E 45 (tx + 3 * CH + P) E45 ltac:(lia)).
           rewrite (zcanon_id 3) by (unfold M64; lia).
           rewrite (zcanon_id (tx + P)) by (unfold M64; lia).
           rewrite (zcanon_id (CH * 3)) by (unfold M64; lia).
           rewrite zcanon_id by (unfold M64; lia). lia.
  - (* the shadow entries *)
    unfold sh_ok, em_SH.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    + apply (shent_ok_of_block SEGS B LAWS lyc Sc W memj mdj E BxN 10 tx TX_SIZE 0 460 HARj Hg).
      * exact HUB.
      * unfold U. rewrite denot_off0, E10. apply unsigned_lit_small. lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 11 chp 1 chp 0 1).
      * exact (em_ra_keep W memc memj (spZ regs) tx chp parp valp (tx + 432) chp HSAME
                 ltac:(unfold TX_SIZE; lia) ltac:(lia) ltac:(lia) Htxia ltac:(lia) ltac:(lia)
                 Hc5 Hp5 Hv5 Rc).
      * exact HUB.
      * unfold U. rewrite denot_off0, E11. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 12 parp 1 parp 0 1).
      * exact (em_ra_keep W memc memj (spZ regs) tx chp parp valp (tx + 432) parp HSAME
                 ltac:(unfold TX_SIZE; lia) ltac:(lia) ltac:(lia) Htxia ltac:(lia) ltac:(lia)
                 Hc5 Hp5 Hv5 Rp).
      * exact HUB.
      * unfold U. rewrite denot_off0, E12. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 13 valp 1 valp 0 1).
      * exact (em_ra_keep W memc memj (spZ regs) tx chp parp valp (tx + 432) valp HSAME
                 ltac:(unfold TX_SIZE; lia) ltac:(lia) ltac:(lia) Htxia ltac:(lia) ltac:(lia)
                 Hc5 Hp5 Hv5 Rv).
      * exact HUB.
      * unfold U. rewrite denot_off0, E13. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
    + apply (em_shent lyc Sc W memj mdj E 45 (tx + 3 * CH + P) tx TX_SIZE 0 152 HARj Hg HUB).
      * unfold U. rewrite denot_off0, E45. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
Qed.

(* ---- what the walk keeps on the way ----------------------------------------------------- *)

(* The bytes outside the three fields this block writes, what it has not touched at all, and
   that nothing present became absent. *)
Definition em_inv (W : world SEGS) (memc m : word -> option byte)
    (sp tx chp parp valp : Z) (T1 : list byte) : Prop :=
  nx_same W memc m sp tx chp parp valp (tx + 432) /\
  (forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0))) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).

Lemma em_wrange : forall (Ex : env) (rs : smem) (tx chp parp valp a : Z),
  skeleton rs = skeleton em_regions ->
  bv_unsigned (ew Ex 10) = tx -> bv_unsigned (ew Ex 11) = chp ->
  bv_unsigned (ew Ex 12) = parp -> bv_unsigned (ew Ex 13) = valp ->
  in_wrange Ex rs a ->
  (tx + 437 <= a < tx + 438) \/ (tx + 444 <= a < tx + 448) \/ (tx + 456 <= a < tx + 460)
  \/ a = chp \/ a = parp \/ a = valp.
Proof.
  intros Ex rs tx chp parp valp a Hsk E10 E11 E12 E13 (r & Hin & Ha).
  assert (Hs : In (skel r) (skeleton em_regions))
    by (rewrite <- Hsk; apply in_map; exact Hin).
  unfold em_regions, STKR, T437, T440, T444, T456, OUTC, OUTP, OUTV, RXE, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]]]]];
    try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha.
  - lia.
  - rewrite E10 in Ha. lia.
  - lia.
  - rewrite E10 in Ha. lia.
  - rewrite E10 in Ha. lia.
  - rewrite E11 in Ha. lia.
  - rewrite E12 in Ha. lia.
  - rewrite E13 in Ha. lia.
  - lia.
Qed.

Lemma em_mbyte_frame : forall (H : word -> bool) (Ex : env) rs (m m' : word -> option byte) a,
  frame_of Ex rs (mrestrict H m) (mrestrict H m') ->
  ~ in_wrange Ex rs a -> 0 <= a < 2 ^ 64 ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H Ex rs m m' a HF Hn Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma em_inv_step : forall (Ex : env) (rs : smem) (W : world SEGS) memc m1 m2
    (sp tx chp parp valp : Z) (T1 : list byte),
  skeleton rs = skeleton em_regions ->
  bv_unsigned (ew Ex 10) = tx -> bv_unsigned (ew Ex 11) = chp ->
  bv_unsigned (ew Ex 12) = parp -> bv_unsigned (ew Ex 13) = valp ->
  0 <= tx -> tx + 460 < 2 ^ 64 ->
  ~ (tx <= chp < tx + 460) -> ~ (tx <= parp < tx + 460) -> ~ (tx <= valp < tx + 460) ->
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  em_inv W memc m1 sp tx chp parp valp T1 ->
  em_inv W memc m2 sp tx chp parp valp T1.
Proof.
  intros Ex rs W memc m1 m2 sp tx chp parp valp T1 Hsk E10 E11 E12 E13 Htx0 Htx1
    Hdc Hdp Hdv HF HG (HS & HK & HPK).
  split; [|split].
  - intros x Hst Htc. rewrite (HF x); [apply HS; assumption|].
    intros Hw. destruct (em_wrange Ex rs tx chp parp valp (bv_unsigned x)
      Hsk E10 E11 E12 E13 Hw) as [Hz|[Hz|[Hz|[Hz|[Hz|Hz]]]]];
      apply Htc; unfold nx_touch2; lia.
  - intros i Hi Hne H444 H456. pose proof (tx_fbyte_range i Hi) as Hir.
    rewrite <- (HK i Hi Hne H444 H456).
    apply (em_mbyte_frame (w_H W) Ex rs m1 m2 (tx + i) HF); [|lia].
    intros Hw. destruct (em_wrange Ex rs tx chp parp valp (tx + i)
      Hsk E10 E11 E12 E13 Hw) as [Hz|[Hz|[Hz|[Hz|[Hz|Hz]]]]]; lia.
  - intros a Ha. apply (apresent_grows (w_H W) m1 m2 a HG). apply HPK. exact Ha.
Qed.

(* ---- reading the result off the regions ------------------------------------------------- *)

Lemma denot_lit : forall (Ex : env) z, 0 <= z < 2 ^ 64 -> sv_denot Ex (SLit z) = Z_to_bv 64 z.
Proof. intros Ex z Hz. rewrite denot_lit_U, U_SLit, zcanon_id by (unfold M64; lia). reflexivity. Qed.

Lemma em_bow1 : forall v, 0 <= v < 256 -> YP09.byte_of_word (Z_to_bv 64 v) 0 = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma em_bow_u32 : forall T k d, 0 <= d < 4 ->
  YP09.byte_of_word (Z_to_bv 64 (u32at T k)) d = Z_to_bv 8 (tb T (k + d)).
Proof.
  intros T k d Hd. pose proof (u32at_range T k) as Hr.
  pose proof (HeadampTxEffective.tb_range T k). pose proof (HeadampTxEffective.tb_range T (k + 1)).
  pose proof (HeadampTxEffective.tb_range T (k + 2)). pose proof (HeadampTxEffective.tb_range T (k + 3)).
  unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia.
  - change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.add_0_r.
    unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 1) with 8. change (2 ^ 8) with 256. unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 2) with 16. change (2 ^ 16) with 65536. unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 3) with 24. change (2 ^ 24) with 16777216. unfold u32at. Z.div_mod_to_equations. lia.
Qed.

Lemma em_out : forall (Ex : env) (W : world SEGS) m (n : nat) (b : Z) cs
    (lo hi wlo whi : Z) (e : sv) (v : Z),
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v ->
  aview SEGS (w_H W) m b = Some (v mod 256).
Proof.
  intros Ex W m n b cs lo hi wlo whi e v HR Hb Hin He Hv.
  assert (Hm : mbyte SEGS (mrestrict (w_H W) m) (b + 0 + 0)
               = Some (YP09.byte_of_word (sv_denot Ex e) 0))
    by (apply (HeadampTxEffective.byte_of_region SEGS Ex _ n b cs lo hi wlo whi 0 1 e 0 HR Hb Hin);
        cbn; lia).
  rewrite He in Hm. replace (b + 0 + 0) with b in Hm by lia.
  apply em_aview_byte; [exact Hv | exact Hm].
Qed.

Lemma em_out_s : forall (Ex : env) (W : world SEGS) m (n : nat) (b : Z) cs
    (lo hi wlo whi : Z) (e : sv) (v : Z),
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v < 256 ->
  aview SEGS (w_H W) m b = Some v.
Proof.
  intros Ex W m n b cs lo hi wlo whi e v HR Hb Hin He Hv.
  rewrite (em_out Ex W m n b cs lo hi wlo whi e v HR Hb Hin He ltac:(lia)).
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma em_obj_of_bytes : forall (W : world SEGS) m (tx : Z) (T' : list byte),
  (forall i, tx_fbyte i = true ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (Z_to_bv 8 (tb T' i))) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T').
Proof.
  intros W m tx T' H. apply (proj2 (tx_obj_bytes SEGS _ tx _)).
  intros i Hi. rewrite <- tb_nth. apply H. exact Hi.
Qed.

(* The table when the block cleared the replay width (the cursor reached the end). *)
Lemma em_obj_w : forall (Ex : env) (W : world SEGS) m (tx : Z) (T1 : list byte) cs437 cs444 cs456,
  length T1 = 460%nat ->
  (forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0))) ->
  bv_unsigned (ew Ex 10) = tx ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 437 438 437 438 cs437) ->
  In (YP09.mkChunk 437 (CVal 1 (SLit 0))) cs437 ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 444 448 444 448 cs444) ->
  In (YP09.mkChunk 444 (CVal 4 (SOff 49 0))) cs444 ->
  ew Ex 49 = Z_to_bv 64 (u32at T1 444) ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 456 460 456 460 cs456) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) cs456 ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 (setb T1 437 0) 456 0)).
Proof.
  intros Ex W m tx T1 cs437 cs444 cs456 HL HK E10 HR437 I437 HR444 I444 E49 HR456 I456.
  assert (HLb : length (setb T1 437 0) = 460%nat) by (apply len_setb; lia).
  apply em_obj_of_bytes. intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hne].
  { replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs437 437 438 437 438 437 1
               (SLit 0) 0 HR437 E10 I437 ltac:(cbn; lia)).
    rewrite (denot_lit Ex 0 ltac:(lia)), (em_bow1 0 ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 437 HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_setb_in; lia. }
  destruct (Z_le_gt_dec 444 i) as [Hge | Hlt]; [destruct (Z_lt_ge_dec i 448) as [Hlt4 | Hge4] |].
  { replace (tx + i) with (tx + 444 + (i - 444)) by lia.
    rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs444 444 448 444 448 444 4
               (SOff 49 0) (i - 444) HR444 E10 I444 ltac:(cbn; lia)).
    rewrite denot_off0, E49, (em_bow_u32 T1 444 (i - 444) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite (tb_setb_out T1 437 0 i HL ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5].
    - replace (tx + i) with (tx + 456 + (i - 456)) by lia.
      rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs456 456 460 456 460 456 4
                 (SLit 0) (i - 456) HR456 E10 I456 ltac:(cbn; lia)).
      rewrite (denot_lit Ex 0 ltac:(lia)), em_bow0. f_equal. f_equal.
      replace i with (456 + (i - 456)) by lia.
      rewrite (tb_set4_in (setb T1 437 0) 456 0 (i - 456) HLb ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia)).
      assert (i - 456 = 0 \/ i - 456 = 1 \/ i - 456 = 2 \/ i - 456 = 3)
        as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity.
    - rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- tb_nth. f_equal. f_equal.
      rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      symmetry. apply tb_setb_out; lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5]; [lia|].
    rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- tb_nth. f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_setb_out; lia. }
Qed.

(* The table when the block set the cursor's wait instead. *)
Lemma em_obj_wait : forall (Ex : env) (W : world SEGS) m (tx : Z) (T1 : list byte) cs437 cs444 cs456,
  length T1 = 460%nat ->
  (forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0))) ->
  bv_unsigned (ew Ex 10) = tx ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 437 438 437 438 cs437) ->
  In (YP09.mkChunk 437 (CVal 1 (SOff 48 0))) cs437 ->
  ew Ex 48 = Z_to_bv 64 (tb T1 437) ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 444 448 444 448 cs444) ->
  In (YP09.mkChunk 444 (CVal 4 (SLit 11))) cs444 ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 456 460 456 460 cs456) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) cs456 ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 (set4 T1 444 11) 456 0)).
Proof.
  intros Ex W m tx T1 cs437 cs444 cs456 HL HK E10 HR437 I437 E48 HR444 I444 HR456 I456.
  assert (HLb : length (set4 T1 444 11) = 460%nat) by (apply len_set4; lia).
  pose proof (HeadampTxEffective.tb_range T1 437) as R437.
  apply em_obj_of_bytes. intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hne].
  { replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs437 437 438 437 438 437 1
               (SOff 48 0) 0 HR437 E10 I437 ltac:(cbn; lia)).
    rewrite denot_off0, E48, (em_bow1 (tb T1 437) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 437 HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_set4_out; lia. }
  destruct (Z_le_gt_dec 444 i) as [Hge | Hlt]; [destruct (Z_lt_ge_dec i 448) as [Hlt4 | Hge4] |].
  { replace (tx + i) with (tx + 444 + (i - 444)) by lia.
    rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs444 444 448 444 448 444 4
               (SLit 11) (i - 444) HR444 E10 I444 ltac:(cbn; lia)).
    rewrite (denot_lit Ex 11 ltac:(lia)), (em_bow11 (i - 444) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    replace i with (444 + (i - 444)) by lia.
    rewrite (tb_set4_in T1 444 11 (i - 444) HL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (i - 444 = 0 \/ i - 444 = 1 \/ i - 444 = 2 \/ i - 444 = 3)
      as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5].
    - replace (tx + i) with (tx + 456 + (i - 456)) by lia.
      rewrite (HeadampTxEffective.byte_of_region SEGS Ex _ 10%nat tx cs456 456 460 456 460 456 4
                 (SLit 0) (i - 456) HR456 E10 I456 ltac:(cbn; lia)).
      rewrite (denot_lit Ex 0 ltac:(lia)), em_bow0. f_equal. f_equal.
      replace i with (456 + (i - 456)) by lia.
      rewrite (tb_set4_in (set4 T1 444 11) 456 0 (i - 456) HLb ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia)).
      assert (i - 456 = 0 \/ i - 456 = 1 \/ i - 456 = 2 \/ i - 456 = 3)
        as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity.
    - rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- tb_nth. f_equal. f_equal.
      rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      symmetry. apply tb_set4_out; lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5]; [lia|].
    rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- tb_nth. f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_set4_out; lia. }
Qed.

(* ---- the registers the epilogue restores ------------------------------------------------ *)

Lemma em_preserved : forall (E Ex : env) ss (ms : machine_state) (H : word -> bool)
    (regs : bvmap 5 word),
  st_ok_pi SEGS VAL Ex ss (restrict H ms) ->
  map (sr_get (ss_regs ss)) CSR = CSE ->
  (forall n, (n < 512)%nat -> ew Ex n = ew E n) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  ew E 2 = Z_to_bv 64 (spZ regs - NEXT_STK) ->
  ew E 3 = getr regs 3 -> ew E 4 = getr regs 4 ->
  ew E 25 = getr regs 25 -> ew E 26 = getr regs 26 -> ew E 27 = getr regs 27 ->
  ew E 34 = getr regs 8 -> ew E 35 = getr regs 9 -> ew E 36 = getr regs 18 ->
  ew E 37 = getr regs 19 -> ew E 38 = getr regs 20 -> ew E 39 = getr regs 21 ->
  ew E 40 = getr regs 22 -> ew E 41 = getr regs 23 -> ew E 42 = getr regs 24 ->
  aregs_preserved regs (ms_regs ms).
Proof.
  intros E Ex ss ms H regs HS Hmap HAG Hsp E2 E3 E4 E25 E26 E27 E34 E35 E36 E37 E38 E39 E40 E41 E42.
  pose proof (u64_range (getr regs 2)) as U2. unfold M64 in U2.
  assert (Hget : forall (rr : bv 5), getr (ms_regs ms) rr = sv_denot Ex (sr_get (ss_regs ss) rr))
    by (intros rr; exact (st_ok_pi_restrict_reg H Ex ss ms rr HS)).
  unfold CSR, CSE in Hmap. cbn [map] in Hmap.
  injection Hmap as M2 M3 M4 M8 M9 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27.
  assert (Hoff : forall (rr : bv 5) (n : nat), sr_get (ss_regs ss) rr = SOff n 0 ->
                   (n < 512)%nat -> getr (ms_regs ms) rr = ew E n).
  { intros rr n Hrr Hn. rewrite (Hget rr), Hrr, denot_off0, (HAG n Hn). reflexivity. }
  intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite (Hget (Z_to_bv 5 2)), M2.
    rewrite denot_lit_U, (U_atom_off Ex 2 (spZ regs - NEXT_STK) 80
      ltac:(rewrite (HAG 2%nat ltac:(lia)); exact E2) ltac:(unfold NEXT_STK in *; lia)
      ltac:(unfold spZ, NEXT_STK in *; lia)).
    replace (spZ regs - NEXT_STK + 80) with (spZ regs) by (unfold NEXT_STK; lia).
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite (Hoff (Z_to_bv 5 3) 3%nat M3 ltac:(lia)). exact E3.
  - rewrite (Hoff (Z_to_bv 5 4) 4%nat M4 ltac:(lia)). exact E4.
  - rewrite (Hoff (Z_to_bv 5 8) 34%nat M8 ltac:(lia)). exact E34.
  - rewrite (Hoff (Z_to_bv 5 9) 35%nat M9 ltac:(lia)). exact E35.
  - assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
            \/ r = 26 \/ r = 27) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]
      by lia.
    + rewrite (Hoff (Z_to_bv 5 18) 36%nat M18 ltac:(lia)). exact E36.
    + rewrite (Hoff (Z_to_bv 5 19) 37%nat M19 ltac:(lia)). exact E37.
    + rewrite (Hoff (Z_to_bv 5 20) 38%nat M20 ltac:(lia)). exact E38.
    + rewrite (Hoff (Z_to_bv 5 21) 39%nat M21 ltac:(lia)). exact E39.
    + rewrite (Hoff (Z_to_bv 5 22) 40%nat M22 ltac:(lia)). exact E40.
    + rewrite (Hoff (Z_to_bv 5 23) 41%nat M23 ltac:(lia)). exact E41.
    + rewrite (Hoff (Z_to_bv 5 24) 42%nat M24 ltac:(lia)). exact E42.
    + rewrite (Hoff (Z_to_bv 5 25) 25%nat M25 ltac:(lia)). exact E25.
    + rewrite (Hoff (Z_to_bv 5 26) 26%nat M26 ltac:(lia)). exact E26.
    + rewrite (Hoff (Z_to_bv 5 27) 27%nat M27 ltac:(lia)). exact E27.
Qed.

(* ---- the end of every path -------------------------------------------------------------- *)

Lemma em_eff_range : forall T t ch p, 0 <= eff T t ch p < 256.
Proof.
  intros T t ch p. unfold eff. destruct (3 <=? p); [lia|].
  destruct ((t =? 0) || (48 <=? ch))%bool; [apply dflt_range|].
  destruct (tb T (144 + 3 * ch + p) =? 0); [apply dflt_range | apply HeadampTxEffective.tb_range].
Qed.

Lemma em_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2 (tx chp parp valp : Z) (T T' : list byte) (c p v : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  next_model T tx = (1, (c, p, v), T') ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved regs regs2 ->
  nx_same W memc mem2 (spZ regs) tx chp parp valp (tx + 432) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  getr regs2 10 = w64 1 ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals T') ->
  aview SEGS (w_H W) mem2 chp = Some c ->
  aview SEGS (w_H W) mem2 parp = Some p ->
  aview SEGS (w_H W) mem2 valp = Some v ->
  tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
    tx chp parp valp T T' c p v HCTX HMOD HJ2 HP HSAME HPK H10 HO Hac Hap Hav.
  destruct HCTX as (HAR & Hg & Hoc & Hop & Hov & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Hspr & Hceil & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres).
  apply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2
    tx chp parp valp (tx + 432) T T' 1 c p v).
  - unfold TX_SIZE. lia.
  - exact HAR.
  - exact Hg.
  - exact Hoc.
  - exact Hop.
  - exact Hov.
  - exact Hspr.
  - exact Hceil.
  - exact HMOD.
  - exact HJ2.
  - exact HP.
  - exact HSAME.
  - intros a Ha. apply HPK. apply Hpres. exact Ha.
  - exact HPK.
  - exact H10.
  - exact HO.
  - intros _. split; [exact Hac | split; [exact Hap | exact Hav]].
Qed.

(* ---- the walk itself --------------------------------------------------------------------- *)

Ltac em_env H :=
  cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact H.

Ltac em_agree :=
  let n := fresh "n" in let Hn := fresh "Hn" in
  intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity.

Ltac em_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac em_region HS i H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with
    | Some ?rr =>
      pose proof (st_ok_pi_region_nth Ex ss (restrict Hh ms) i rr HS
                    ltac:(vm_compute; reflexivity)) as H;
      cbn [restrict ms_mem] in H
    end
  end.

(* the bytes a run may write are the table's three fields and the caller's three bytes *)
Ltac em_awr E10v E11v E12v E13v Htabv Hcv Hpv Hvv chpv parpv valpv :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  apply awr_ok_cons_ro; [azlit_tac|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat _);
    [reflexivity | em_env E10v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply Htabv; unfold TX_SIZE; lia |];
  apply awr_ok_cons_ro; [azlit_tac|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat _);
    [reflexivity | em_env E10v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply Htabv; unfold TX_SIZE; lia |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat _);
    [reflexivity | em_env E10v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply Htabv; unfold TX_SIZE; lia |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 11%nat _);
    [reflexivity | em_env E11v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with chpv by lia; exact Hcv |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat _);
    [reflexivity | em_env E12v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with parpv by lia; exact Hpv |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 13%nat _);
    [reflexivity | em_env E13v
     | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with valpv by lia; exact Hvv |];
  apply awr_ok_cons_ro; [azlit_tac|];
  apply awr_ok_nil.

(* carry the walk's invariant over one run *)
Ltac em_adv E10v E11v E12v E13v :=
  lazymatch goal with
  | [ HFR : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
      HGR : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2),
      HIV : em_inv ?Wv ?memcv ?m1 ?spv ?txv ?chpv ?parpv ?valpv ?T1v |- _ ] =>
    let H2 := fresh "HINV" in
    assert (H2 : em_inv Wv memcv m2 spv txv chpv parpv valpv T1v)
      by (apply (em_inv_step Ex rs Wv memcv m1 m2 spv txv chpv parpv valpv T1v);
          [ vm_compute; reflexivity | em_env E10v | em_env E11v | em_env E12v | em_env E13v
          | lia | lia | lia | lia | lia | exact HFR | exact HGR | exact HIV ]);
    clear HIV HFR HGR; rename H2 into HINV
  end.

Theorem pb_nx_emit : nx_emit_spec B.
Proof.
unfold nx_emit_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T j HCTX HMID HSAVE HOBJ HJ3 HCAR HMODEL HAT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (em_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
  tx chp parp valp T j HCTX HMID HSAVE HOBJ HJ3 HAT) as [HS SHOK].
pose proof HCTX as HCTX0.
destruct HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rc & Rp & Rv &
  Hspr & Hceil & Hsp16 & Hslo & Hshi & Htab & Wc & Wp & Wv & Hra & Hra4 & Hgp & Htp &
  H10 & H11 & H12 & H13 & HTl & HI & HTobj & Hpres).
destruct Hspr as (Hsp46 & Hsp47).
destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
unfold TX_SIZE in Hc2, Hp2, Hv2.
destruct HMID as (HJ & HSAME0 & HpresJ & HpresK0).
destruct HAT as (Hkeepgp & A2 & A5 & A6 & A7 & A28 & A8 & A19 & A10 & A11 & A12 & A13 &
  A14 & A15 & A16 & A29 & A31).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARj.
destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
  as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size TX_SIZE) with 460 in Htxceil, Htxia, Htxpres.
pose proof (HeadampTxEffective.tb_range T 436) as R436.
pose proof (HeadampTxEffective.tb_range T 437) as R437.
assert (HLj : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
assert (Hchr : 0 <= em_ch T j < 64) by (unfold em_ch; apply Z.mod_pos_bound; lia).
assert (Hpr : 0 <= j mod 3 < 3) by (apply Z.mod_pos_bound; lia).
assert (Hcr : 0 <= tb T 436 + j / 3 <= 509).
{ split; [pose proof (Z.div_pos j 3 ltac:(lia) ltac:(lia)); lia|].
  assert (j / 3 < 255) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hcm : 0 <= (tb T 436 + j / 3) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
set (CH := em_ch T j) in *. set (P := j mod 3) in *. set (T1 := set4 T 440 (j + 1)) in *.
set (CM := (tb T 436 + j / 3) mod 256) in *.
pose proof (HeadampTxEffective.tb_range T1 (144 + 3 * CH + P)) as R46.
pose proof (HeadampTxEffective.tb_range T1 (3 * CH + P)) as R47.
pose proof (em_eff_range T1 tx CM P) as Rv2.
pose proof (dflt_range P) as Rdf.
set (E := EM regs regsj tx j T) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EM; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj (em_extra regs tx j T)) n)
  by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - NEXT_STK))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 2 2%bv eq_refl); exact A2).
assert (E8 : ew E 8 = Z_to_bv 64 P)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 8 8%bv eq_refl); exact A8).
assert (E10' : ew E 10 = Z_to_bv 64 tx)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 10 10%bv eq_refl); exact A10).
assert (E19 : ew E 19 = Z_to_bv 64 (tb T 436 + j / 3))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 19 19%bv eq_refl); exact A19).
assert (E29 : ew E 29 = Z_to_bv 64 (3 * tb T 437))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 29 29%bv eq_refl); exact A29).
assert (E43 : ew E 43 = Z_to_bv 64 (j + 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 11)).
assert (E46 : ew E 46 = Z_to_bv 64 (tb T1 (144 + 3 * CH + P)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 14)).
assert (E47 : ew E 47 = Z_to_bv 64 (tb T1 (3 * CH + P)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 15)).
assert (E48 : ew E 48 = Z_to_bv 64 (tb T1 437))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 16)).
assert (E49 : ew E 49 = Z_to_bv 64 (u32at T1 444))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 17)).
assert (G33 : ew E 33 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 1);
      apply Z_to_bv_bv_unsigned).
assert (G34 : ew E 34 = getr regs 8)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 2);
      apply Z_to_bv_bv_unsigned).
assert (G35 : ew E 35 = getr regs 9)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 3);
      apply Z_to_bv_bv_unsigned).
assert (G36 : ew E 36 = getr regs 18)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 4);
      apply Z_to_bv_bv_unsigned).
assert (G37 : ew E 37 = getr regs 19)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 5);
      apply Z_to_bv_bv_unsigned).
assert (G38 : ew E 38 = getr regs 20)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 6);
      apply Z_to_bv_bv_unsigned).
assert (G39 : ew E 39 = getr regs 21)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 7);
      apply Z_to_bv_bv_unsigned).
assert (G40 : ew E 40 = getr regs 22)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 8);
      apply Z_to_bv_bv_unsigned).
assert (G41 : ew E 41 = getr regs 23)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 9);
      apply Z_to_bv_bv_unsigned).
assert (G42 : ew E 42 = getr regs 24)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regsj _ 10);
      apply Z_to_bv_bv_unsigned).
assert (G3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl);
      apply (Hkeepgp 3%bv); cbn [In]; auto 10).
assert (G4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl);
      apply (Hkeepgp 4%bv); cbn [In]; auto 10).
assert (G25 : ew E 25 = getr regs 25)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 25 25%bv eq_refl);
      apply (Hkeepgp 25%bv); cbn [In]; auto 10).
assert (G26 : ew E 26 = getr regs 26)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 26 26%bv eq_refl);
      apply (Hkeepgp 26%bv); cbn [In]; auto 10).
assert (G27 : ew E 27 = getr regs 27)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl);
      apply (Hkeepgp 27%bv); cbn [In]; auto 10).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (Eu11 : bv_unsigned (ew E 11) = chp)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl), A11;
      apply unsigned_lit_small; lia).
assert (Eu12 : bv_unsigned (ew E 12) = parp)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl), A12;
      apply unsigned_lit_small; lia).
assert (Eu13 : bv_unsigned (ew E 13) = valp)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 13 13%bv eq_refl), A13;
      apply unsigned_lit_small; lia).
assert (HINV : em_inv W memc memj (spZ regs) tx chp parp valp T1).
{ split; [exact HSAME0|]. split; [|exact HpresK0].
  intros i Hi _ _ _. exact (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ i Hi). }
clear HSAME0 HpresK0 HOBJ.
unfold cfg_at. change (w64 (BASE + EMIT)) with (Z_to_bv 64 (BASE + EMIT)).
paj_run_tok RUN HS HJ SHOK BspanN;
  [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
em_adv Eu10 Eu11 Eu12 Eu13.
psrr_branch_tok RUN BR HS SHOK BspanN.
- (* 47 < the channel: the record's value is the parameter's default *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
    rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_and_lit Ex (SOff 19 0) 255),
      (U_atom Ex 19 (tb T 436 + j / 3) ltac:(em_env E19) ltac:(lia)), land_mod256 in Hc
      by (unfold M64; lia)
  end.
  apply Z.ltb_lt in Hc. rename Hc into Hb1.
  assert (HV : eff T1 tx CM P = dflt P) by (apply eff_ch; lia).
  paj_run_tok RUN HS HJ SHOK BspanN;
    [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
  em_adv Eu10 Eu11 Eu12 Eu13.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  + (* the cursor reached the width: the width is cleared *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
        (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
      unfold sx64 in Hc;
      rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
        (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
    end.
    apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK BspanN;
      [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
    em_adv Eu10 Eu11 Eu12 Eu13.
    em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
    em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
    em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
    em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
      apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
               tx chp parp valp T (set4 (setb T1 437 0) 456 0) CM P (eff T1 tx CM P));
      [ exact HCTX0
      | rewrite HMODEL; unfold emit_res;
        rewrite (proj2 (Z.ltb_ge (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
      | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
      | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                 ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
      | exact (proj1 HINV)
      | exact (proj2 (proj2 HINV))
      | exact R10
      | apply (em_obj_w Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                 HR437 ltac:(cbn [In]; auto) HR444 ltac:(cbn [In]; auto) ltac:(em_env E49)
                 HR456 ltac:(cbn [In]; auto))
      | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                 ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                 ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
      | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                 ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                 ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
      | rewrite HV;
        exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1
                 (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1)) (SLit 5)) (dflt P) HRV
                 ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                 ltac:(apply em_dflt_val; [lia | em_env E8]) ltac:(lia)) ]
    end.
  + (* the cursor has not reached the width: the wait is set *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
        (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
      unfold sx64 in Hc;
      rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
        (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
    end.
    apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK BspanN;
      [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
    em_adv Eu10 Eu11 Eu12 Eu13.
    em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
    em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
    em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
    em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
      intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
      apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
               tx chp parp valp T (set4 (set4 T1 444 11) 456 0) CM P (eff T1 tx CM P));
      [ exact HCTX0
      | rewrite HMODEL; unfold emit_res;
        rewrite (proj2 (Z.ltb_lt (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
      | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
      | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                 ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
      | exact (proj1 HINV)
      | exact (proj2 (proj2 HINV))
      | exact R10
      | apply (em_obj_wait Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                 HR437 ltac:(cbn [In]; auto) ltac:(em_env E48)
                 HR444 ltac:(cbn [In]; auto) HR456 ltac:(cbn [In]; auto))
      | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                 ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                 ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
      | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                 ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                 ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
      | rewrite HV;
        exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1
                 (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1)) (SLit 5)) (dflt P) HRV
                 ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                 ltac:(apply em_dflt_val; [lia | em_env E8]) ltac:(lia)) ]
    end.
- (* the channel is below 48: the block reads the cell *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
    rewrite branch_ltu_U, U_SLit, (zcanon_id 47), (U_and_lit Ex (SOff 19 0) 255),
      (U_atom Ex 19 (tb T 436 + j / 3) ltac:(em_env E19) ltac:(lia)), land_mod256 in Hc
      by (unfold M64; lia)
  end.
  apply Z.ltb_ge in Hc. rename Hc into Hb1.
  assert (HCM : CH = CM) by (unfold CH, CM, em_ch; apply em_mod64; lia).
  assert (Htx0 : tx <> 0) by lia.
  paj_run_tok RUN HS HJ SHOK BspanN;
    [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
  em_adv Eu10 Eu11 Eu12 Eu13.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  + (* the cell was never set: the default *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      rewrite branch_eq_U, (U_atom Ex 46 (tb T1 (144 + 3 * CH + P)) ltac:(em_env E46) ltac:(lia)),
        U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia)
    end.
    apply Z.eqb_eq in Hc. rename Hc into Hb2.
    assert (HV : eff T1 tx CM P = dflt P).
    { rewrite (eff_cell T1 tx CM P ltac:(lia) Htx0 ltac:(lia)).
      rewrite <- HCM, Hb2. reflexivity. }
    paj_run_tok RUN HS HJ SHOK BspanN;
      [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
    em_adv Eu10 Eu11 Eu12 Eu13.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    * lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
          (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
        unfold sx64 in Hc;
        rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
          (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
      end.
      apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
      em_adv Eu10 Eu11 Eu12 Eu13.
      em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
      em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
      em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
      em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
        apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
                 tx chp parp valp T (set4 (setb T1 437 0) 456 0) CM P (eff T1 tx CM P));
        [ exact HCTX0
        | rewrite HMODEL; unfold emit_res;
          rewrite (proj2 (Z.ltb_ge (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
        | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
        | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                   ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
        | exact (proj1 HINV)
        | exact (proj2 (proj2 HINV))
        | exact R10
        | apply (em_obj_w Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                   HR437 ltac:(cbn [In]; auto) HR444 ltac:(cbn [In]; auto) ltac:(em_env E49)
                   HR456 ltac:(cbn [In]; auto))
        | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                   ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
        | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                   ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
        | rewrite HV;
          exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1
                   (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1)) (SLit 5)) (dflt P) HRV
                   ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                   ltac:(apply em_dflt_val; [lia | em_env E8]) ltac:(lia)) ]
      end.
    * lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
          (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
        unfold sx64 in Hc;
        rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
          (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
      end.
      apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
      em_adv Eu10 Eu11 Eu12 Eu13.
      em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
      em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
      em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
      em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
        apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
                 tx chp parp valp T (set4 (set4 T1 444 11) 456 0) CM P (eff T1 tx CM P));
        [ exact HCTX0
        | rewrite HMODEL; unfold emit_res;
          rewrite (proj2 (Z.ltb_lt (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
        | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
        | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                   ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
        | exact (proj1 HINV)
        | exact (proj2 (proj2 HINV))
        | exact R10
        | apply (em_obj_wait Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                   HR437 ltac:(cbn [In]; auto) ltac:(em_env E48)
                   HR444 ltac:(cbn [In]; auto) HR456 ltac:(cbn [In]; auto))
        | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                   ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
        | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                   ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
        | rewrite HV;
          exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1
                   (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 8 (-2)) (SLit 1)) (SLit 5)) (dflt P) HRV
                   ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                   ltac:(apply em_dflt_val; [lia | em_env E8]) ltac:(lia)) ]
      end.
  + (* the cell was set: its value *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      rewrite branch_eq_U, (U_atom Ex 46 (tb T1 (144 + 3 * CH + P)) ltac:(em_env E46) ltac:(lia)),
        U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia)
    end.
    apply Z.eqb_neq in Hc. rename Hc into Hb2.
    assert (HV : eff T1 tx CM P = tb T1 (3 * CH + P)).
    { rewrite (eff_cell T1 tx CM P ltac:(lia) Htx0 ltac:(lia)).
      rewrite <- HCM, (proj2 (Z.eqb_neq (tb T1 (144 + 3 * CH + P)) 0) Hb2). reflexivity. }
    paj_run_tok RUN HS HJ SHOK BspanN;
      [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
    em_adv Eu10 Eu11 Eu12 Eu13.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    * lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
          (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
        unfold sx64 in Hc;
        rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
          (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
      end.
      apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
      em_adv Eu10 Eu11 Eu12 Eu13.
      em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
      em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
      em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
      em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
        apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
                 tx chp parp valp T (set4 (setb T1 437 0) 456 0) CM P (eff T1 tx CM P));
        [ exact HCTX0
        | rewrite HMODEL; unfold emit_res;
          rewrite (proj2 (Z.ltb_ge (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
        | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
        | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                   ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
        | exact (proj1 HINV)
        | exact (proj2 (proj2 HINV))
        | exact R10
        | apply (em_obj_w Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                   HR437 ltac:(cbn [In]; auto) HR444 ltac:(cbn [In]; auto) ltac:(em_env E49)
                   HR456 ltac:(cbn [In]; auto))
        | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                   ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
        | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                   ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
        | rewrite HV;
          exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1 (SOff 47 0) (tb T1 (3 * CH + P)) HRV
                   ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E47) ltac:(lia)) ]
      end.
    * lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        rewrite bt_ge_Sg, (Sg_atom Ex 43 (j + 1) ltac:(em_env E43) ltac:(lia)),
          (Sg_atom Ex 29 (3 * tb T 437) ltac:(em_env E29) ltac:(lia)) in Hc;
        unfold sx64 in Hc;
        rewrite (proj2 (Z.ltb_lt (j + 1) (2 ^ 63)) ltac:(lia)),
          (proj2 (Z.ltb_lt (3 * tb T 437) (2 ^ 63)) ltac:(lia)) in Hc
      end.
      apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [em_awr Eu10 Eu11 Eu12 Eu13 Htab Wc Wp Wv chp parp valp |].
      em_adv Eu10 Eu11 Eu12 Eu13.
      em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
      em_region HS 5%nat HRC. em_region HS 6%nat HRP. em_region HS 7%nat HRV.
      em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(rewrite denot_off0; em_env G33) R1.
      em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10.
      lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
        intros matX; cbn [ms_regs ms_mem]; rewrite R1, Hra;
        apply (em_fin STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _
                 tx chp parp valp T (set4 (set4 T1 444 11) 456 0) CM P (eff T1 tx CM P));
        [ exact HCTX0
        | rewrite HMODEL; unfold emit_res;
          rewrite (proj2 (Z.ltb_lt (j + 1) (3 * tb T 437)) ltac:(lia)); reflexivity
        | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
        | apply (em_preserved E Ex _ _ _ regs HS ltac:(vm_compute; reflexivity) ltac:(em_agree)
                   ltac:(lia) E2 G3 G4 G25 G26 G27 G34 G35 G36 G37 G38 G39 G40 G41 G42)
        | exact (proj1 HINV)
        | exact (proj2 (proj2 HINV))
        | exact R10
        | apply (em_obj_wait Ex W _ tx T1 _ _ _ HLj (proj1 (proj2 HINV)) ltac:(em_env Eu10)
                   HR437 ltac:(cbn [In]; auto) ltac:(em_env E48)
                   HR444 ltac:(cbn [In]; auto) HR456 ltac:(cbn [In]; auto))
        | exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 19 0) (tb T 436 + j / 3) HRC
                   ltac:(em_env Eu11) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E19) ltac:(lia))
        | exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 8 0) P HRP
                   ltac:(em_env Eu12) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E8) ltac:(lia))
        | rewrite HV;
          exact (em_out_s Ex W _ 13%nat valp _ 0 1 0 1 (SOff 47 0) (tb T1 (3 * CH + P)) HRV
                   ltac:(em_env Eu13) ltac:(cbn [In]; auto)
                   ltac:(rewrite denot_off0; em_env E47) ltac:(lia)) ]
      end.
Qed.

End H.
End F.
End D.
