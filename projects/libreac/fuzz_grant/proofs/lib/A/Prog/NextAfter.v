(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextAfter), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE3m.v. *)
(* reac_headamp_tx_next (fuzz_grant.asan 0x850cc) on the ASan build: the segment of its walk
   from AFTR (0x85228), where the edge scan over the 144 cells found none changed, to the next
   cut or to the return. C source src/reac_headamp_tx.c:137-146.

   The segment reads replay_width (offset 437). If it is 0 the code jumps to the re-assert
   tail RSWP (0x85374). Otherwise it reads replay_wait (444); if that is positive it stores
   replay_wait - 1 and returns 0 (the ret at 0x85400). Otherwise it reads replay_idx (440):
   if replay_idx >= 3 * replay_width it stores replay_width := 0 and falls into RSWP;
   otherwise it reads replay_base (436) and replay_set_only (448), sets up the replay scan's
   constants and reaches the scan's head LOOPR (0x852e4). The two cuts after this one are
   a Theorem Labs lane's nx_resweep_spec and nx_rloop_spec (lib/A/Prog/NextReplayDefs.v), taken here as
   hypotheses; the table's new state is Pau Aliagas's after_scan (lib/Prog/NextModel.v).

   The walk starts from a symbolic state seated at AFTR (nx_seat_aftr): atom 2 is the
   caller's stack pointer, so the machine's sp is that atom less 80, and the ten registers the
   prologue saved are the chunks of the stack region (atoms 1, 8, 9, 18..24, the caller's
   registers), which the epilogue reads back; atoms 34..38 are the five fields this segment
   reads; atoms 43..62 hold the registers the segment does not know (the walk never reads
   them). The table is held as two regions: offsets 436..437 with replay_width the one byte
   it may write, and 440..448 with replay_wait the four bytes it may write. The stack region
   has no writable window: the segment writes no byte of its own frame.

   The memory-checking runtime: every access of this segment is to the table at a constant
   offset, so the shadow entry for the table's 460 bytes (shadow byte at (a >> 3) + 0x7fff8000
   marked usable for each byte of the block) makes the walk discharge the shadow check of each
   instrumented access. The error path (a call of an __asan_report_ function) is not reached
   from any of these checks (the access, the shadow byte read, the branch, the report entry):
     replay_width, lbu at 0x8523c: shadow read 0x85234, branch 0x85238 to errpath_load1 0x58914;
     replay_width, sb at 0x85370: shadow read 0x85368, branch 0x8536c to errpath_store1 0x58c34;
     replay_wait, lw at 0x85258: shadow read 0x85250, branch 0x85254 to errpath_load4 0x58a54;
     replay_wait, sw at 0x85270: shadow read 0x85260, branch 0x85264 to errpath_store4 0x58d74;
     replay_idx, lw at 0x8528c: shadow read 0x85284, branch 0x85288 to errpath_load4 0x58a54;
     replay_base, lbu at 0x852c0: shadow read 0x852a8, branch 0x852ac to errpath_load1 0x58914;
     replay_set_only, lbu at 0x852c8: shadow read 0x852bc, branch 0x852c4 to errpath_load1
     0x58914. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaJournal GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
NextArith HeadampTxEffective HeadampTxNext YC1g NextReplayDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at AFTR. *)
Definition STKA : YP09.region := YP09.mkRegion (Some 2%nat) (-80) 0 (-80) (-80)
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)) ].
Definition TXA : YP09.region := YP09.mkRegion (Some 10%nat) 436 438 437 438
  [ YP09.mkChunk 436 (CVal 1 (SOff 34 0)); YP09.mkChunk 437 (CVal 1 (SOff 35 0)) ].
Definition TXB : YP09.region := YP09.mkRegion (Some 10%nat) 440 449 444 448
  [ YP09.mkChunk 440 (CVal 4 (SOff 36 0)); YP09.mkChunk 444 (CVal 4 (SOff 37 0));
    YP09.mkChunk 448 (CVal 1 (SOff 38 0)) ].
Definition ra_regs : list YP09.region := [ STKA; TXA; TXB ].
Definition ra_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTRN 4);
    (32%nat, mkAF SB_NX SB_NX 0);
    (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
    (36%nat, mkAF 0 2147483647 0); (37%nat, mkAF 0 11 0); (38%nat, mkAF 0 1 0) ].
Definition ra_SH : list shent := [ mkSHE 10 0 460 ].
Definition sr_a : list sv :=
  [ SLit 0; SOff 43 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 32 0; SOff 44 0; SOff 45 0;
    SOff 46 0; SOff 47 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 48 0; SOff 49 0;
    SOff 50 0; SOff 51 0; SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0; SOff 56 0; SOff 57 0;
    SOff 58 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 59 0; SOff 60 0; SOff 61 0; SOff 62 0 ].
Definition ss_a : sstate := mkSS AFTR sr_a ra_regs None (mkFacts ra_atoms [] []).

(* Atoms 32..42 as in nx_extra, then the registers at AFTR the segment does not know. *)
Definition ra_extra (regsA : bvmap 5 word) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; u32at T 432; tb T 436; tb T 437; s32at T 440; s32at T 444;
      tb T 448; tb T 449; tb T 450; u32at T 452; u32at T 456 ]
  ++ [ getr regsA 1; getr regsA 6; getr regsA 7; getr regsA 8; getr regsA 9;
       getr regsA 14; getr regsA 15; getr regsA 16; getr regsA 17; getr regsA 18;
       getr regsA 19; getr regsA 20; getr regsA 21; getr regsA 22; getr regsA 23;
       getr regsA 24; getr regsA 28; getr regsA 29; getr regsA 30; getr regsA 31 ].

(* The bytes of the table the segment may write: replay_width and replay_wait. *)
Definition ra_win (tx a : Z) : Prop := a = tx + 437 \/ (tx + 444 <= a < tx + 448).

(* Denotations of the expressions the walk leaves in registers and chunks. *)
Lemma den0 : forall (E : env) n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma denk : forall (E : env) n v k, bv_unsigned (ew E n) = v -> sv_denot E (SOff n k) = w64 (v + k).
Proof. intros E n v k H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma den_shadow : forall (E : env) tx k, bv_unsigned (ew E 10) = tx -> ew E 32 = w64 SB_NX ->
  0 <= tx + k < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 k) (SLit 3)) (SOff 32 0))
  = w64 (SHADOW_OFF + (tx + k) / 8).
Proof.
  intros E tx k U10 E32 Hr. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, U_SLit, U10, E32. unfold w64.
  rewrite unsigned_lit_small by (unfold SB_NX; lia).
  unfold zcanon, M64.
  change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite (Z.mod_small (tx + k)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= (tx + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small ((tx + k) / 8)) by lia.
  rewrite (Z.mod_small (SB_NX + 0)) by (unfold SB_NX; lia).
  rewrite Z.mod_small by (unfold SB_NX; lia).
  unfold SHADOW_OFF, SB_NX. lia.
Qed.

Lemma den_mul3 : forall (E : env) x, ew E 35 = w64 x -> 0 <= x < 256 ->
  sv_denot E (SMd M_MUL (SOff 35 0) (SLit 3)) = w64 (3 * x).
Proof.
  intros E x H Hx. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom E 35 x H) by lia.
  unfold zcanon, M64. rewrite (Z.mod_small 3) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* The three branches the walk stops at, as conditions on the table's fields. *)
Lemma bt_eq0 : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v H Hv. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.

Lemma bt_ge : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_ge. unfold w64.
  rewrite !YO0c.lit64_small by lia. rewrite !YO0b.s64_small by lia. reflexivity.
Qed.

(* The bytes of a field value. *)
Lemma bw_tb : forall T k, YP09.byte_of_word (Z_to_bv 64 (tb T k)) 0 = nth (Z.to_nat k) T (Z_to_bv 8 0).
Proof.
  intros T k. unfold YP09.byte_of_word. pose proof (HeadampTxEffective.tb_range T k).
  rewrite unsigned_lit_small by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z_to_bv8_tb.
Qed.

Lemma bw_u32 : forall T k j, 0 <= j < 4 ->
  YP09.byte_of_word (Z_to_bv 64 (u32at T k)) j = nth (Z.to_nat (k + j)) T (Z_to_bv 8 0).
Proof.
  intros T k j Hj. unfold YP09.byte_of_word. pose proof (u32at_range T k) as Hu.
  rewrite unsigned_lit_small by lia. rewrite <- Z_to_bv8_tb.
  pose proof (HeadampTxEffective.tb_range T k). pose proof (HeadampTxEffective.tb_range T (k + 1)).
  pose proof (HeadampTxEffective.tb_range T (k + 2)). pose proof (HeadampTxEffective.tb_range T (k + 3)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3) as [-> | [-> | [-> | ->]]] by lia; unfold u32at.
  - rewrite !Z.add_0_r. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
    Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 1)) with 256. Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 2)) with 65536. Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.

(* Writing back the cursor's own value leaves the table's bytes as they are. *)
Lemma set4_self_nth : forall T k i, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= i < 460 ->
  nth (Z.to_nat i) (set4 T k (u32 T k)) (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0).
Proof.
  intros T k i HL Hk Hk4 Hi. rewrite <- !Z_to_bv8_tb. f_equal.
  pose proof (u32_range T k) as Hu.
  pose proof (NextLemmas.tb_range T k). pose proof (NextLemmas.tb_range T (k + 1)).
  pose proof (NextLemmas.tb_range T (k + 2)). pose proof (NextLemmas.tb_range T (k + 3)).
  destruct (Z_lt_le_dec i k) as [Hlo | Hlo]; [apply tb_set4_out; lia|].
  destruct (Z_lt_le_dec i (k + 4)) as [Hhi | Hhi]; [|apply tb_set4_out; lia].
  replace i with (k + (i - k)) by lia.
  rewrite (tb_set4_in T k (u32 T k) (i - k)) by lia.
  assert (i - k = 0 \/ i - k = 1 \/ i - k = 2 \/ i - k = 3) as [E | [E | [E | E]]] by lia;
    rewrite E; unfold u32.
  - change (Z.to_nat 0) with 0%nat. cbn [nth]. rewrite ?Z.add_0_r. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 1) with 1%nat. cbn [nth]. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 2) with 2%nat. cbn [nth]. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 3) with 3%nat. cbn [nth]. Z.div_mod_to_equations. lia.
Qed.

Lemma walk_set4_self : forall n T t bs o total j, length T = 460%nat ->
  walk T t bs o total j (S n) = walk (set4 T 440 j) t bs o total j (S n).
Proof.
  intros n T t bs o total j HL. cbn [walk].
  rewrite set4_set4 by (first [exact HL | lia]). reflexivity.
Qed.

(* Clearing replay_width keeps the table's invariant. *)
Lemma I1_setb437 : forall T, I1 T -> length T = 460%nat -> I1 (setb T 437 0).
Proof.
  intros T HI HL. apply (I1_step T); [exact HI | |].
  - split; [apply len_setb; lia|]. split; [intros i Hi; apply tb_setb_out; lia|].
    split; [intros i Hi; left; apply tb_setb_out; lia|]. apply u32_setb_out; lia.
  - pose proof (I1_scal T HI) as (S1 & S2 & (S3a & S3b & S3c & S3d) & S4).
    unfold scal. rds. dec.
    split; [left; reflexivity|]. split; [exact S2|].
    split; [split; [exact S3a|]; split; [intros X; exfalso; apply X; reflexivity|];
            split; [exact S3c | exact S3d]|].
    exact S4.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition EA (regs regsA : bvmap 5 word) (T : list byte) : env := Eimg (Ereg regs (ra_extra regsA T)).

(* What the segment's runs leave alike: every byte but the two fields it may write. *)
Definition ra_meq (W : world SEGS) (m1 m2 : word -> option byte) (tx : Z) : Prop :=
  forall x : word, ~ ra_win tx (bv_unsigned x) -> mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

Definition ra_pres (W : world SEGS) (m1 m2 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a.

Lemma ra_meq_refl : forall W m tx, ra_meq W m m tx.
Proof. intros W m tx x _. reflexivity. Qed.

Lemma ra_meq_trans : forall W m1 m2 m3 tx, ra_meq W m1 m2 tx -> ra_meq W m2 m3 tx -> ra_meq W m1 m3 tx.
Proof. intros W m1 m2 m3 tx H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma ra_inw : forall (E : env) (rs : smem) (tx a : Z),
  skeleton rs = skeleton ra_regs -> bv_unsigned (ew E 10) = tx ->
  in_wrange E rs a -> ra_win tx a.
Proof.
  intros E rs tx a Hsk U10 Hw.
  destruct (in_wrange_skeleton E rs ra_regs a Hsk Hw) as (r & Hin & Ha).
  unfold ra_regs in Hin. cbn [In] in Hin. unfold ra_win.
  destruct Hin as [<- | [<- | [<- | []]]]; unfold STKA, TXA, TXB in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U10 in Ha; lia.
Qed.

Lemma ra_meq_of_frame : forall (E : env) (rs : smem) (W : world SEGS) m1 m2 tx,
  skeleton rs = skeleton ra_regs -> bv_unsigned (ew E 10) = tx ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> ra_meq W m1 m2 tx.
Proof.
  intros E rs W m1 m2 tx Hsk U10 HF x Hx. apply HF. intros Hw. apply Hx.
  exact (ra_inw E rs tx _ Hsk U10 Hw).
Qed.

Lemma ra_grows : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | first [reflexivity | exact E2]].
Qed.

Lemma ra_pres_step : forall (W : world SEGS) m0 m1 m2,
  ra_pres W m0 m1 -> mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> ra_pres W m0 m2.
Proof. intros W m0 m1 m2 HP HG a Ha. exact (ra_grows W m1 m2 a HG (HP a Ha)). Qed.

Lemma ra_mbyte : forall W m1 m2 tx a, ra_meq W m1 m2 tx -> 0 <= a < 2 ^ 64 -> ~ ra_win tx a ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof.
  intros W m1 m2 tx a HM Ha Hn. unfold mbyte. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma ra_val : forall W m1 m2 tx a n v, ra_meq W m1 m2 tx -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= tx + 437 \/ tx + 448 <= a) ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
  intros W m1 m2 tx a n v HM Ha Hn Hd HV kk Hk.
  rewrite (ra_mbyte W m1 m2 tx (a + Z.of_nat kk) HM) by (unfold ra_win; lia). exact (HV kk Hk).
Qed.

Lemma ra_saved : forall W m1 m2 (regs : bvmap 5 word) tx,
  ra_meq W m1 m2 tx -> 0 <= tx -> tx + 460 <= spZ regs - NEXT_STK -> spZ regs <= 2 ^ 47 ->
  nx_saved W m1 regs (spZ regs) -> nx_saved W m2 regs (spZ regs).
Proof.
  intros W m1 m2 regs tx HM H0 H1 H2 HS. unfold NEXT_STK in H1.
  destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold nx_saved. repeat split; (eapply ra_val; [exact HM | | | | eassumption]);
    try change (Z.of_nat 8) with 8; lia.
Qed.

Lemma ra_same : forall W memc m1 m2 sp tx chp parp valp,
  nx_same W memc m1 sp tx chp parp valp (tx + 432) -> ra_meq W m1 m2 tx ->
  nx_same W memc m2 sp tx chp parp valp (tx + 432).
Proof.
  intros W memc m1 m2 sp tx chp parp valp HS HM x H1 H2.
  rewrite (HM x); [exact (HS x H1 H2)|]. intros Hx. apply H2. unfold nx_touch2. left.
  unfold ra_win in Hx. lia.
Qed.

Lemma ra_obj_eq : forall m tx T T',
  (forall i, 0 <= i < 460 -> nth (Z.to_nat i) T' (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0)) ->
  obj_at SEGS m tx LAY_TX (tx_vals T) -> obj_at SEGS m tx LAY_TX (tx_vals T').
Proof.
  intros m tx T T' H HO. apply (proj2 (tx_obj_bytes SEGS _ _ _)). intros i Hi.
  rewrite H by (apply tx_fbyte_range; exact Hi). exact (proj1 (tx_obj_bytes SEGS _ _ _) HO i Hi).
Qed.

(* The table after a run: the two fields from the regions' chunks, every other byte kept. *)
Lemma ra_table : forall (E : env) (W : world SEGS) m0 m (tx : Z) (T T' : list byte) cs1 cs2 e1 e2,
  obj_at SEGS (mrestrict (w_H W) m0) tx LAY_TX (tx_vals T) ->
  ra_meq W m0 m tx -> 0 <= tx -> tx + 460 <= 2 ^ 64 ->
  bv_unsigned (ew E 10) = tx ->
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 436 438 437 438 cs1) ->
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 10%nat) 440 449 444 448 cs2) ->
  In (YP09.mkChunk 437 (CVal 1 e1)) cs1 -> In (YP09.mkChunk 444 (CVal 4 e2)) cs2 ->
  (forall i, 0 <= i < 460 -> i <> 437 -> ~ (444 <= i < 448) ->
     nth (Z.to_nat i) T' (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0)) ->
  YP09.byte_of_word (sv_denot E e1) 0 = nth (Z.to_nat 437) T' (Z_to_bv 8 0) ->
  (forall j, 0 <= j < 4 ->
     YP09.byte_of_word (sv_denot E e2) j = nth (Z.to_nat (444 + j)) T' (Z_to_bv 8 0)) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T').
Proof.
  intros E W m0 m tx T T' cs1 cs2 e1 e2 HO HM H0 H1 U10 R1 R2 I1 I2 Hout B1 B2.
  apply (proj2 (tx_obj_bytes SEGS _ tx T')). intros i Hi.
  pose proof (tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hn].
  - replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (byte_of_region SEGS E _ 10%nat tx cs1 436 438 437 438 437 1 e1 0 R1 U10 I1 ltac:(cbn; lia)).
    rewrite B1. reflexivity.
  - destruct (Z_lt_le_dec i 444) as [Hlo | Hlo]; [| destruct (Z_lt_le_dec i 448) as [Hhi | Hhi]].
    + rewrite (ra_mbyte W m0 m tx (tx + i) HM) by (unfold ra_win; lia).
      rewrite (proj1 (tx_obj_bytes SEGS _ tx T) HO i Hi). rewrite Hout by lia. reflexivity.
    + replace (tx + i) with (tx + 444 + (i - 444)) by lia.
      rewrite (byte_of_region SEGS E _ 10%nat tx cs2 440 449 444 448 444 4 e2 (i - 444) R2 U10 I2
                 ltac:(cbn; lia)).
      rewrite B2 by lia. replace (444 + (i - 444)) with i by lia. reflexivity.
    + rewrite (ra_mbyte W m0 m tx (tx + i) HM) by (unfold ra_win; lia).
      rewrite (proj1 (tx_obj_bytes SEGS _ tx T) HO i Hi). rewrite Hout by lia. reflexivity.
Qed.

Lemma ra_chunk_saved : forall (E : env) m sp n off (r : bv 5) (regs : bvmap 5 word),
  ew E n = getr regs r -> val_mem SEGS m (sp + off) 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok SEGS E m sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E m sp n off r regs H HV.
  apply (chunk_ok_val SEGS E m sp off 8 (SOff n 0) (bv_unsigned (getr regs r)));
    [ cbn [sv_denot]; rewrite H, Z.add_0_r; reflexivity
    | exact (bv_unsigned_in_range 64 (getr regs r))
    | cbn; lia | exact HV ].
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RLOOP : nx_rloop_spec B.
Hypothesis RSWEEP : nx_resweep_spec B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* The engine's write permission at each run: the segment's writable windows are two fields
   of the table, which the caller lets the call write. *)
Lemma ra_awr : forall (E : env) (rs : smem) STK sp0 FP ly S lyc Sc own tx,
  skeleton rs = skeleton ra_regs -> bv_unsigned (ew E 10) = tx ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E rs STK sp0 FP ly S lyc Sc own tx Hsk U10 HW a Ha. apply HW.
  pose proof (ra_inw E rs tx a Hsk U10 Ha) as Hw. unfold ra_win in Hw. unfold TX_SIZE. lia.
Qed.

Ltac ra_env_facts E HE regs regsA T tx chp parp valp Q10 Q11 Q12 Q13 :=
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ra_extra regsA T)) n)
    by (intros n Hn; rewrite HE; unfold EA; apply Eimg_low; exact Hn);
  assert (E1 : ew E 1 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl));
  assert (E3 : ew E 3 = getr regs 3)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regs 4)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
  assert (E25 : ew E 25 = getr regs 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl));
  assert (E26 : ew E 26 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl));
  assert (E27 : ew E 27 = getr regs 27)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl));
  assert (E10 : ew E 10 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Q10);
  assert (E11 : ew E 11 = w64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Q11);
  assert (E12 : ew E 12 = w64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact Q12);
  assert (E13 : ew E 13 = w64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact Q13);
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0));
  assert (E34 : ew E 34 = w64 (tb T 436))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2));
  assert (E35 : ew E 35 = w64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3));
  assert (E36 : ew E 36 = w64 (s32at T 440))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4));
  assert (E37 : ew E 37 = w64 (s32at T 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5));
  assert (E38 : ew E 38 = w64 (tb T 448))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).

(* The symbolic state at AFTR, from the registers there and the table's bytes. *)
Lemma nx_seat_aftr : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsA : bvmap 5 word) memA mdA (tx chp parp valp : Z) (T : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) ->
  nx_saved W memA regs (spZ regs) ->
  nx_keep_gp regs regsA ->
  obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
  getr regsA 2 = w64 (spZ regs - NEXT_STK) -> getr regsA 5 = w64 SB_NX ->
  getr regsA 10 = w64 tx -> getr regsA 11 = w64 chp ->
  getr regsA 12 = w64 parp -> getr regsA 13 = w64 valp ->
  st_ok_pi SEGS VAL (EA regs regsA T) ss_a
    (restrict (w_H W) (mkst regsA (Z_to_bv 64 (BASE + AFTR)) memA (seg_rom SEGS)))
  /\ sh_ok SEGS BxN ra_SH (EA regs regsA T) (mrestrict (w_H W) memA).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA tx chp parp valp T
    HCTX HMID HSAV HKEEP HOBJ R2 R5 R10 R11 R12 R13.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof (proj1 HJ) as HARj.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memA mdA tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  pose proof HI as (P1 & P2 & P3 & (P4a & P4b) & P5 & P6 & (P7a & P7b & P7c & P7d) & P8).
  pose proof (s32at_small T 440 P7a) as R36.
  pose proof (HeadampTxEffective.tb_range T 436) as R34.
  pose proof (HeadampTxEffective.tb_range T 437) as R35.
  pose proof (HeadampTxEffective.tb_range T 448) as R38.
  pose proof (u32at_range T 440). pose proof (u32at_range T 444).
  assert (E440 : s32at T 440 = u32at T 440) by (apply s32at_u32at; exact P7a).
  assert (E444 : s32at T 444 = u32at T 444) by (apply s32at_u32at; lia).
  pose proof (proj1 (tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  remember (EA regs regsA T) as E eqn:HE.
  ra_env_facts E HE regs regsA T tx chp parp valp Q10 Q11 Q12 Q13.
  assert (E8 : ew E 8 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E18 : ew E 18 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
  assert (E19 : ew E 19 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  assert (E20 : ew E 20 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
  assert (E21 : ew E 21 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
  assert (E22 : ew E 22 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
  assert (E23 : ew E 23 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)).
  assert (E24 : ew E 24 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
  (* the register file at AFTR, register by register *)
  assert (K3 : ew E 3 = getr regsA 3) by (rewrite E3; symmetry; apply HKEEP; now left).
  assert (K4 : ew E 4 = getr regsA 4) by (rewrite E4; symmetry; apply HKEEP; right; now left).
  assert (K25 : ew E 25 = getr regsA 25)
    by (rewrite E25; symmetry; apply HKEEP; right; right; now left).
  assert (K26 : ew E 26 = getr regsA 26)
    by (rewrite E26; symmetry; apply HKEEP; right; right; right; now left).
  assert (K27 : ew E 27 = getr regsA 27)
    by (rewrite E27; symmetry; apply HKEEP; right; right; right; right; now left).
  assert (K5 : ew E 32 = getr regsA 5) by (rewrite E32, R5; reflexivity).
  assert (K10 : ew E 10 = getr regsA 10) by (rewrite E10, R10; reflexivity).
  assert (K11 : ew E 11 = getr regsA 11) by (rewrite E11, R11; reflexivity).
  assert (K12 : ew E 12 = getr regsA 12) by (rewrite E12, R12; reflexivity).
  assert (K13 : ew E 13 = getr regsA 13) by (rewrite E13, R13; reflexivity).
  assert (X43 : ew E 43 = getr regsA 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
  assert (X44 : ew E 44 = getr regsA 6) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
  assert (X45 : ew E 45 = getr regsA 7) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
  assert (X46 : ew E 46 = getr regsA 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 14)).
  assert (X47 : ew E 47 = getr regsA 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 15)).
  assert (X48 : ew E 48 = getr regsA 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 16)).
  assert (X49 : ew E 49 = getr regsA 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 17)).
  assert (X50 : ew E 50 = getr regsA 16) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 18)).
  assert (X51 : ew E 51 = getr regsA 17) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 19)).
  assert (X52 : ew E 52 = getr regsA 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 20)).
  assert (X53 : ew E 53 = getr regsA 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 21)).
  assert (X54 : ew E 54 = getr regsA 20) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 22)).
  assert (X55 : ew E 55 = getr regsA 21) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 23)).
  assert (X56 : ew E 56 = getr regsA 22) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 24)).
  assert (X57 : ew E 57 = getr regsA 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 25)).
  assert (X58 : ew E 58 = getr regsA 24) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 26)).
  assert (X59 : ew E 59 = getr regsA 28) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 27)).
  assert (X60 : ew E 60 = getr regsA 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 28)).
  assert (X61 : ew E 61 = getr regsA 30) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 29)).
  assert (X62 : ew E 62 = getr regsA 31) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 30)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (U10 : bv_unsigned (ew E 10) = tx)
    by (rewrite E10; apply unsigned_lit_small; unfold NEXT_STK in *; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX) by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (U34 : bv_unsigned (ew E 34) = tb T 436) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = tb T 437) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = s32at T 440) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = s32at T 444) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = tb T 448) by (rewrite E38; apply unsigned_lit_small; lia).
  split.
  - rewrite restrict_mkst_fx. unfold ss_a. apply pa_entry_st_ok_full.
    + apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
      repeat (destruct Hr as [<-|Hr];
        [ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?rr) =>
            let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end;
          first [ rewrite getr_zero; reflexivity
                | symmetry; apply den0; assumption
                | rewrite R2; cbn [sv_denot]; rewrite Usp; unfold w64, NEXT_STK; f_equal; lia ]
        | ]).
      destruct Hr.
    + vm_compute. reflexivity.
    + unfold ra_regs, STKA, TXA, TXB.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (ra_chunk_saved E _ (spZ regs) 1 (-8) 1%bv regs E1).
           replace (spZ regs + -8) with (spZ regs - 8) by lia. exact S1.
        -- apply (ra_chunk_saved E _ (spZ regs) 8 (-16) 8%bv regs E8).
           replace (spZ regs + -16) with (spZ regs - 16) by lia. exact S2.
        -- apply (ra_chunk_saved E _ (spZ regs) 9 (-24) 9%bv regs E9).
           replace (spZ regs + -24) with (spZ regs - 24) by lia. exact S3.
        -- apply (ra_chunk_saved E _ (spZ regs) 18 (-32) 18%bv regs E18).
           replace (spZ regs + -32) with (spZ regs - 32) by lia. exact S4.
        -- apply (ra_chunk_saved E _ (spZ regs) 19 (-40) 19%bv regs E19).
           replace (spZ regs + -40) with (spZ regs - 40) by lia. exact S5.
        -- apply (ra_chunk_saved E _ (spZ regs) 20 (-48) 20%bv regs E20).
           replace (spZ regs + -48) with (spZ regs - 48) by lia. exact S6.
        -- apply (ra_chunk_saved E _ (spZ regs) 21 (-56) 21%bv regs E21).
           replace (spZ regs + -56) with (spZ regs - 56) by lia. exact S7.
        -- apply (ra_chunk_saved E _ (spZ regs) 22 (-64) 22%bv regs E22).
           replace (spZ regs + -64) with (spZ regs - 64) by lia. exact S8.
        -- apply (ra_chunk_saved E _ (spZ regs) 23 (-72) 23%bv regs E23).
           replace (spZ regs + -72) with (spZ regs - 72) by lia. exact S9.
        -- apply (ra_chunk_saved E _ (spZ regs) 24 (-80) 24%bv regs E24).
           replace (spZ regs + -80) with (spZ regs - 80) by lia. exact S10.
      * rewrite U10. split; [lia|]. split; [unfold NEXT_STK in *; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hgpres (tx + o) ltac:(lia)))|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 436 1 (SOff 34 0) (tb T 436));
             [ exact (den0 E 34 _ E34) | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memA) tx T 436 HBY); vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 35 0) (tb T 437));
             [ exact (den0 E 35 _ E35) | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memA) tx T 437 HBY); vm_compute; reflexivity ].
      * rewrite U10. split; [lia|]. split; [unfold NEXT_STK in *; lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hgpres (tx + o) ltac:(lia)))|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 440 4 (SOff 36 0) (u32at T 440));
             [ rewrite (den0 E 36 _ E36), E440; reflexivity | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memA) tx T 440 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 444 4 (SOff 37 0) (u32at T 444));
             [ rewrite (den0 E 37 _ E37), E444; reflexivity | cbn; lia | cbn; lia
             | apply (nx_val4 (mrestrict (w_H W) memA) tx T 444 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 448 1 (SOff 38 0) (tb T 448));
             [ exact (den0 E 38 _ E38) | cbn; lia | cbn; lia
             | apply (nx_val1 (mrestrict (w_H W) memA) tx T 448 HBY); vm_compute; reflexivity ].
    + apply pairwise_disjoint_of_extents.
      unfold ra_regs, STKA, TXA, TXB, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold NEXT_STK in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [ra_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U32, U34, U35, U36, U37, U38.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold TX_SIZE, NEXT_STK, SB_NX in *.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, ra_SH. constructor; [|constructor].
    apply (shent_ok_of_block SEGS B LAWS lyc Sc W memA mdA E BxN 10 tx TX_SIZE 0 460 HARj Hg).
    + unfold U, BxN. rewrite (den0 E 32 _ E32). unfold w64, SHADOW_OFF, SB_NX.
      apply unsigned_lit_small. lia.
    + unfold U. rewrite (den0 E 10 _ E10). unfold w64. apply unsigned_lit_small. unfold NEXT_STK in *. lia.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

Ltac ra_awr_tac U10 Hwtab :=
  lazymatch goal with |- awr_ok ?Ey ?rs _ _ _ _ _ _ _ =>
    eapply (ra_awr Ey rs); [vm_compute; reflexivity | exact U10 | exact Hwtab] end.

(* After a run: the bytes outside the two fields stay, and what was present stays present. *)
Ltac ra_carry E U10 :=
  lazymatch goal with
  | HFr : frame_of E ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HM : ra_meq ?W ?m0 ?m1 ?tx, HPR : ra_pres ?W ?m0 ?m1 |- _ =>
      let HM' := fresh "HM" in let HPR' := fresh "HPR" in
      pose proof (ra_meq_trans W m0 m1 m2 tx HM
                    (ra_meq_of_frame E rs W m1 m2 tx ltac:(vm_compute; reflexivity) U10 HFr)) as HM';
      pose proof (ra_pres_step W m0 m1 m2 HPR HG) as HPR';
      clear HM HPR HFr HG; rename HM' into HM; rename HPR' into HPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

Ltac ra_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac ra_region HS i H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth_error (ss_mem ssx) i) in
    lazymatch r with Some ?rr =>
      pose proof (st_ok_pi_region_nth Ex ssx msx i rr HS ltac:(vm_compute; reflexivity)) as H
    end
  end;
  cbn [restrict ms_mem] in H.

Ltac ra_inlist := repeat (first [left; reflexivity | right]).

Ltac ra_mid HJ HSAME HM HPR HpresS HpresK :=
  unfold nx_mid; split; [exact HJ|]; split; [exact (ra_same _ _ _ _ _ _ _ _ _ HSAME HM)|];
  split; [intros a Ha; exact (HPR a (HpresS a Ha)) | intros a Ha; exact (HPR a (HpresK a Ha))].

Definition nx_after_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsA : bvmap 5 word) memA mdA (tx chp parp valp : Z) (T : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) ->
  nx_saved W memA regs (spZ regs) ->
  nx_keep_gp regs regsA ->
  obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
  ~ (u32at T 432 = 0 /\ tb T 437 = 0) ->
  (forall l, 0 <= l < 144 -> tb T (288 + l) = 0) ->
  getr regsA 2 = w64 (spZ regs - NEXT_STK) -> getr regsA 5 = w64 SB_NX ->
  getr regsA 10 = w64 tx -> getr regsA 11 = w64 chp ->
  getr regsA 12 = w64 parp -> getr regsA 13 = w64 valp ->
  SRr SEGS W (cfg_at SEGS (BASE + AFTR) regsA memA mdA)
    (tnext_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).

Theorem nx_after : nx_after_spec.
Proof.
  unfold nx_after_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA tx chp parp valp T
    HCTX HMID HSAV HKEEP HOBJ Hact Hz R2 R5 R10 R11 R12 R13.
  destruct (nx_seat_aftr STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA
    tx chp parp valp T HCTX HMID HSAV HKEEP HOBJ R2 R5 R10 R11 R12 R13) as [HS SHOK].
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & _ & _ & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  pose proof HI as (P1 & P2 & P3 & (P4a & P4b) & P5 & P6 & (P7a & P7b & P7c & P7d) & P8).
  pose proof (s32at_small T 440 P7a) as R36.
  pose proof (HeadampTxEffective.tb_range T 436) as R34.
  pose proof (HeadampTxEffective.tb_range T 437) as R35.
  pose proof (HeadampTxEffective.tb_range T 448) as R38.
  assert (E440 : s32at T 440 = u32at T 440) by (apply s32at_u32at; exact P7a).
  assert (E444 : s32at T 444 = u32at T 444) by (apply s32at_u32at; lia).
  remember (EA regs regsA T) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold EA; apply Eimg_env).
  ra_env_facts E HE regs regsA T tx chp parp valp Q10 Q11 Q12 Q13.
  assert (HAE : env_agree 32 (Ereg regs (ra_extra regsA T)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE; reflexivity]).
  clear HE EL.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (U10 : bv_unsigned (ew E 10) = tx)
    by (rewrite E10; apply unsigned_lit_small; unfold NEXT_STK in *; lia).
  assert (U37 : bv_unsigned (ew E 37) = s32at T 444) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (HM : ra_meq W memA memA tx) by apply ra_meq_refl.
  assert (HPR : ra_pres W memA memA) by (intros a Ha; exact Ha).
  unfold cfg_at. change (w64 (BASE + AFTR)) with (Z_to_bv 64 (BASE + AFTR)).
  (* the run to the test of replay_width, 0x85240 *)
  paj_run_tok RUN HS HJ SHOK BspanN; [ra_awr_tac U10 Hwtab |].
  ra_carry E U10.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* replay_width = 0: the code jumps to the re-assert tail *)
    rewrite (bt_eq0 E 35 (tb T 437) E35 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hw0.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN RSWP; [ra_awr_tac U10 Hwtab |].
    ra_carry E U10.
    ra_region HS 1%nat HRA. ra_region HS 2%nat HRB.
    ra_reg HS (2%bv : bv 5) (w64 (spZ regs - NEXT_STK))
      ltac:(rewrite (denk E 2 _ (-80) Usp); unfold w64, NEXT_STK; f_equal; lia) G2.
    ra_reg HS (3%bv : bv 5) (getr regs 3) ltac:(exact (den0 E 3 _ E3)) G3.
    ra_reg HS (4%bv : bv 5) (getr regs 4) ltac:(exact (den0 E 4 _ E4)) G4.
    ra_reg HS (25%bv : bv 5) (getr regs 25) ltac:(exact (den0 E 25 _ E25)) G25.
    ra_reg HS (26%bv : bv 5) (getr regs 26) ltac:(exact (den0 E 26 _ E26)) G26.
    ra_reg HS (27%bv : bv 5) (getr regs 27) ltac:(exact (den0 E 27 _ E27)) G27.
    ra_reg HS (5%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G5.
    ra_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
      ltac:(apply den_shadow; [exact U10 | exact E32 | unfold NEXT_STK in *; lia]) G6.
    ra_reg HS (10%bv : bv 5) (w64 tx) ltac:(exact (den0 E 10 _ E10)) G10.
    ra_reg HS (15%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 10 tx 437 U10)) G15.
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
      refine (RSWEEP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                tx chp parp valp T T HCTX _ _ _ _ _ _ _ _ _) end.
    + ra_mid HJ HSAME HM HPR HpresS HpresK.
    + exact (ra_saved W memA _ regs tx HM ltac:(lia) ltac:(lia) ltac:(lia) HSAV).
    + eapply (ra_table E W memA _ tx T T _ _ _ _ HOBJ HM);
        [ lia | unfold NEXT_STK in *; lia | exact U10 | exact HRA | exact HRB | ra_inlist | ra_inlist
        | intros i _ _ _; reflexivity
        | rewrite (den0 E 35 _ E35); exact (bw_tb T 437)
        | intros j Hj; rewrite (den0 E 37 _ E37); unfold w64; rewrite E444; exact (bw_u32 T 444 j Hj) ].
    + exact HTL.
    + exact HI.
    + exact Hw0.
    + intros l Hl. reflexivity.
    + rewrite (nx_model_after T tx Hact Hz). apply nx_after_w0. exact Hw0.
    + unfold nx_at_rswp, nx_keep_gp.
      split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption|].
      repeat split; assumption.
  - rewrite (bt_eq0 E 35 (tb T 437) E35 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hw.
    (* the run to the test of replay_wait, 0x8525c *)
    paj_run_tok RUN HS HJ SHOK BspanN; [ra_awr_tac U10 Hwtab |].
    ra_carry E U10.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* replay_wait <= 0 *)
      rewrite (bt_ge E (SLit 0) (SOff 37 0) 0 (s32at T 444) eq_refl (den0 E 37 _ E37)
                 ltac:(lia) ltac:(lia)) in Hc.
      apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hwait.
      (* the run to the test of replay_idx, 0x85298 *)
      paj_run_tok RUN HS HJ SHOK BspanN; [ra_awr_tac U10 Hwtab |].
      ra_carry E U10.
      psrr_branch_tok RUN BR HS SHOK BspanN.
      * (* replay_idx >= 3 * replay_width: replay_width := 0, then the re-assert tail *)
        rewrite (bt_ge E (SOff 36 0) (SMd M_MUL (SOff 35 0) (SLit 3)) (s32at T 440) (3 * tb T 437)
                   (den0 E 36 _ E36) (den_mul3 E (tb T 437) E35 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hidx.
        paj_run_to_tok RUNTO HS HJ SHOK BspanN RSWP; [ra_awr_tac U10 Hwtab |].
        ra_carry E U10.
        ra_region HS 1%nat HRA. ra_region HS 2%nat HRB.
        ra_reg HS (2%bv : bv 5) (w64 (spZ regs - NEXT_STK))
          ltac:(rewrite (denk E 2 _ (-80) Usp); unfold w64, NEXT_STK; f_equal; lia) G2.
        ra_reg HS (3%bv : bv 5) (getr regs 3) ltac:(exact (den0 E 3 _ E3)) G3.
        ra_reg HS (4%bv : bv 5) (getr regs 4) ltac:(exact (den0 E 4 _ E4)) G4.
        ra_reg HS (25%bv : bv 5) (getr regs 25) ltac:(exact (den0 E 25 _ E25)) G25.
        ra_reg HS (26%bv : bv 5) (getr regs 26) ltac:(exact (den0 E 26 _ E26)) G26.
        ra_reg HS (27%bv : bv 5) (getr regs 27) ltac:(exact (den0 E 27 _ E27)) G27.
        ra_reg HS (5%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G5.
        ra_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
          ltac:(apply den_shadow; [exact U10 | exact E32 | unfold NEXT_STK in *; lia]) G6.
        ra_reg HS (10%bv : bv 5) (w64 tx) ltac:(exact (den0 E 10 _ E10)) G10.
        ra_reg HS (15%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 10 tx 437 U10)) G15.
        rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
          refine (RSWEEP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                    tx chp parp valp T (setb T 437 0) HCTX _ _ _ _ _ _ _ _ _) end.
        -- ra_mid HJ HSAME HM HPR HpresS HpresK.
        -- exact (ra_saved W memA _ regs tx HM ltac:(lia) ltac:(lia) ltac:(lia) HSAV).
        -- eapply (ra_table E W memA _ tx T (setb T 437 0) _ _ _ _ HOBJ HM);
             [ lia | unfold NEXT_STK in *; lia | exact U10 | exact HRA | exact HRB | ra_inlist | ra_inlist
             | intros i Hi H1 H2; rewrite <- !Z_to_bv8_tb; f_equal;
               apply tb_setb_out; [exact HTL | lia | lia | lia]
             | rewrite <- Z_to_bv8_tb, (tb_setb_if T 437 0 437 HTL ltac:(lia) ltac:(lia)); reflexivity
             | intros j Hj; rewrite (den0 E 37 _ E37); unfold w64; rewrite E444, (bw_u32 T 444 j Hj);
               rewrite <- !Z_to_bv8_tb; f_equal; symmetry;
               apply tb_setb_out; [exact HTL | lia | lia | lia] ].
        -- apply len_setb; [exact HTL | lia].
        -- exact (I1_setb437 T HI HTL).
        -- rewrite (tb_setb_if T 437 0 437 HTL ltac:(lia) ltac:(lia)). reflexivity.
        -- intros l Hl. apply tb_setb_out; [exact HTL | lia | lia | lia].
        -- rewrite (nx_model_after T tx Hact Hz). apply nx_after_done; [exact Hw | exact Hwait | exact Hidx].
        -- unfold nx_at_rswp, nx_keep_gp.
           split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption|].
           repeat split; assumption.
      * (* replay_idx < 3 * replay_width: on to the replay scan's head *)
        rewrite (bt_ge E (SOff 36 0) (SMd M_MUL (SOff 35 0) (SLit 3)) (s32at T 440) (3 * tb T 437)
                   (den0 E 36 _ E36) (den_mul3 E (tb T 437) E35 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
        apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hidx.
        paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPR; [ra_awr_tac U10 Hwtab |].
        ra_carry E U10.
        ra_region HS 1%nat HRA. ra_region HS 2%nat HRB.
        ra_reg HS (2%bv : bv 5) (w64 (spZ regs - NEXT_STK))
          ltac:(rewrite (denk E 2 _ (-80) Usp); unfold w64, NEXT_STK; f_equal; lia) G2.
        ra_reg HS (3%bv : bv 5) (getr regs 3) ltac:(exact (den0 E 3 _ E3)) G3.
        ra_reg HS (4%bv : bv 5) (getr regs 4) ltac:(exact (den0 E 4 _ E4)) G4.
        ra_reg HS (25%bv : bv 5) (getr regs 25) ltac:(exact (den0 E 25 _ E25)) G25.
        ra_reg HS (26%bv : bv 5) (getr regs 26) ltac:(exact (den0 E 26 _ E26)) G26.
        ra_reg HS (27%bv : bv 5) (getr regs 27) ltac:(exact (den0 E 27 _ E27)) G27.
        ra_reg HS (5%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G5.
        ra_reg HS (6%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
          ltac:(apply den_shadow; [exact U10 | exact E32 | unfold NEXT_STK in *; lia]) G6.
        ra_reg HS (7%bv : bv 5) (w64 (SHADOW_OFF + (tx + 444) / 8))
          ltac:(apply den_shadow; [exact U10 | exact E32 | unfold NEXT_STK in *; lia]) G7.
        ra_reg HS (28%bv : bv 5) (w64 (SHADOW_OFF + (tx + 440) / 8))
          ltac:(apply den_shadow; [exact U10 | exact E32 | unfold NEXT_STK in *; lia]) G28.
        ra_reg HS (8%bv : bv 5) (w64 (s32 T 440)) ltac:(exact (den0 E 36 _ E36)) G8.
        ra_reg HS (9%bv : bv 5) (w64 (tb T 436)) ltac:(exact (den0 E 34 _ E34)) G9.
        ra_reg HS (10%bv : bv 5) (w64 tx) ltac:(exact (den0 E 10 _ E10)) G10.
        ra_reg HS (11%bv : bv 5) (w64 chp) ltac:(exact (den0 E 11 _ E11)) G11.
        ra_reg HS (12%bv : bv 5) (w64 parp) ltac:(exact (den0 E 12 _ E12)) G12.
        ra_reg HS (13%bv : bv 5) (w64 valp) ltac:(exact (den0 E 13 _ E13)) G13.
        ra_reg HS (14%bv : bv 5) (w64 (tx + 444)) ltac:(exact (denk E 10 tx 444 U10)) G14.
        ra_reg HS (15%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 10 tx 437 U10)) G15.
        ra_reg HS (16%bv : bv 5) (w64 (tx + 440)) ltac:(exact (denk E 10 tx 440 U10)) G16.
        ra_reg HS (18%bv : bv 5) (w64 (tb T 448)) ltac:(exact (den0 E 38 _ E38)) G18.
        ra_reg HS (20%bv : bv 5) (w64 1431655766) ltac:(reflexivity) G20.
        ra_reg HS (21%bv : bv 5) (w64 47) ltac:(reflexivity) G21.
        ra_reg HS (29%bv : bv 5) (w64 (3 * tb T 437)) ltac:(apply den_mul3; [exact E35 | lia]) G29.
        ra_reg HS (30%bv : bv 5) (w64 3) ltac:(reflexivity) G30.
        ra_reg HS (31%bv : bv 5) (w64 (tx + 144)) ltac:(exact (denk E 10 tx 144 U10)) G31.
        lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
          assert (HO : obj_at SEGS (mrestrict (w_H W) (ms_mem msx)) tx LAY_TX (tx_vals T)) end.
        { eapply (ra_table E W memA _ tx T T _ _ _ _ HOBJ HM);
            [ lia | unfold NEXT_STK in *; lia | exact U10 | exact HRA | exact HRB | ra_inlist | ra_inlist
            | intros i _ _ _; reflexivity
            | rewrite (den0 E 35 _ E35); exact (bw_tb T 437)
            | intros j Hj; rewrite (den0 E 37 _ E37); unfold w64; rewrite E444; exact (bw_u32 T 444 j Hj) ]. }
        rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
        assert (Hnz : 0 < 3 * tb T 437 - s32 T 440) by (change (s32 T 440) with (s32at T 440); lia).
        destruct (Z.to_nat (3 * tb T 437 - s32 T 440)) as [|n'] eqn:Hn; [lia|].
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
          refine (RLOOP (Datatypes.S n') STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                    tx chp parp valp T (s32 T 440) HCTX _ _ _ _ _ _ _ _ _) end.
        -- ra_mid HJ HSAME HM HPR HpresS HpresK.
        -- exact (ra_saved W memA _ regs tx HM ltac:(lia) ltac:(lia) ltac:(lia) HSAV).
        -- apply (ra_obj_eq _ tx T); [|exact HO].
           intros i Hi. change (s32 T 440) with (s32at T 440). rewrite E440.
           change (u32at T 440) with (u32 T 440). apply set4_self_nth; [exact HTL | lia | lia | lia].
        -- exact Hw.
        -- change (s32 T 440) with (s32at T 440). lia.
        -- change (s32 T 440) with (s32at T 440). lia.
        -- rewrite <- Hn. rewrite Z2Nat.id by lia. reflexivity.
        -- rewrite (nx_model_after T tx Hact Hz), (nx_after_walk T tx Hw Hwait Hidx), Hn.
           apply walk_set4_self. exact HTL.
        -- unfold nx_at_loopr, nx_keep_gp.
           split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; assumption|].
           repeat split; assumption.
    + (* replay_wait > 0: replay_wait := replay_wait - 1, and the call returns 0 *)
      rewrite (bt_ge E (SLit 0) (SOff 37 0) 0 (s32at T 444) eq_refl (den0 E 37 _ E37)
                 ltac:(lia) ltac:(lia)) in Hc.
      apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hwait.
      paj_run_tok RUN HS HJ SHOK BspanN; [ra_awr_tac U10 Hwtab |].
      ra_carry E U10.
      ra_region HS 1%nat HRA. ra_region HS 2%nat HRB.
      ra_reg HS (1%bv : bv 5) (getr regs 1) ltac:(exact (den0 E 1 _ E1)) G1.
      ra_reg HS (10%bv : bv 5) (w64 0) ltac:(reflexivity) G10.
      pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs (ra_extra regsA T) HS HAE
                    ltac:(vm_compute; reflexivity)) as HP.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros matB. cbn [ms_regs ms_mem]. rewrite G1, Hret.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        apply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx)
                 (ms_mem msx) _ tx chp parp valp (tx + 432) T (set4 T 444 (s32 T 444 - 1)) 0 0 0 0) end.
      * unfold TX_SIZE. lia.
      * exact HAR.
      * exact Hg.
      * exact Hoc.
      * exact Hop.
      * exact Hov.
      * exact Hspr.
      * exact Hceil.
      * rewrite (nx_model_after T tx Hact Hz), (nx_after_wait T tx Hw Hwait). reflexivity.
      * apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
      * exact HP.
      * exact (ra_same _ _ _ _ _ _ _ _ _ HSAME HM).
      * intros a Ha. exact (HPR a (HpresS a Ha)).
      * intros a Ha. exact (HPR a (HpresK a Ha)).
      * exact G10.
      * eapply (ra_table E W memA _ tx T (set4 T 444 (s32 T 444 - 1)) _ _ _ _ HOBJ HM);
          [ lia | unfold NEXT_STK in *; lia | exact U10 | exact HRA | exact HRB | ra_inlist | ra_inlist
          | intros i Hi H1 H2; rewrite <- !Z_to_bv8_tb; f_equal;
            apply tb_set4_out; [exact HTL | lia | lia | lia | lia]
          | rewrite (den0 E 35 _ E35); unfold w64; rewrite (bw_tb T 437);
            rewrite <- !Z_to_bv8_tb; f_equal; symmetry;
            apply tb_set4_out; [exact HTL | lia | lia | lia | lia]
          | intros j Hj; rewrite (denk E 37 (s32at T 444) (-1) U37); unfold w64;
            replace (s32at T 444 + -1) with (u32at (set4 T 444 (s32 T 444 - 1)) 444);
            [ exact (bw_u32 _ 444 j Hj)
            | rewrite u32at_u32, u32_set4; [change (s32 T 444) with (s32at T 444); lia
                                            | exact HTL | lia | lia
                                            | change (s32 T 444) with (s32at T 444); lia] ] ].
      * intros H01. discriminate H01.
Qed.

End h.
End f.
End d.
