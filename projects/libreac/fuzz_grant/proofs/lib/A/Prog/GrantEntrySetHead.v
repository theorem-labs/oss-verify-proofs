(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetHead), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The head of a turn of the set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan build: the slots 0x80aa4 .. 0x80b54 (fuzz/fuzz_grant.c:201-210), from the
   loop's head GIn to the three returns of reac_headamp_tx_set, GA0, GA1 and GA2
   (GrantEntrySetDefs.v).

   The turn loads the bytes left (slot 120) and the shadow offset (slot 152), then reads
   the cell: no byte (bytes left 0: the call at 0x80b08 with 0 0 0), one byte (the call at
   0x80bb4 with ch 0 0), two bytes (the call at 0x80b54 with ch param 0, slot 120 := 0) or
   three bytes (the call at 0x80b54 with ch param value, slot 120 := bytes left - 3). Each
   byte read is checked against its shadow byte at (a >> 3) + 0x7fff8000 first; the
   input bytes the cell reads lie in the caller's input block, so the memory-checking
   runtime's report (the slow paths at 0x80c84, 0x80c90 and 0x80cb4, which end in a call
   of __asan_report_load1) is not reached: the walk's shadow entry for the input cursor
   covers exactly the bytes read, from range_addressable_of_block. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective HeadampTxSet.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel HeadampSched reac_headamp_tx_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic state at 0x80aa4 ---- *)
(* The atoms: the entry registers (0 .. 31); 32 the bytes left (slot 120), 33 and 34 the
   addresses of set_to and was_set (slots 136, 144), as R_stk has them; 35, 36, 37 the
   channel, parameter and value of the cell (0 for a byte past the end). *)
(* The cell's bytes the turn reads: nb of them (0 .. 3) at the input cursor s5 (x21). *)
Definition R_in (nb : nat) : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 (Z.of_nat nb) 0 0
    (firstn nb [YP09.mkChunk 0 (CVal 1 (SOff 35 0)); YP09.mkChunk 1 (CVal 1 (SOff 36 0));
                YP09.mkChunk 2 (CVal 1 (SOff 37 0))]).
Definition rs_h (nb : nat) : smem := match nb with O => [R_stk] | _ => [R_stk; R_in nb] end.
(* The bytes left, as each case knows them: exactly 0, 1, 2, or 3 and more. *)
Definition AF32 (nb : nat) : afact :=
  match nb with O => mkAF 0 0 0 | S O => mkAF 1 1 0 | S (S O) => mkAF 2 2 0 | _ => mkAF 3 (2 ^ 26) 0 end.
Definition F_h (nb : nat) : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, PTRA 0); (32%nat, AF32 nb);
            (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0) ] [] [].
Definition ss_h (nb : nat) : sstate := mkSS 0x3f4 sr_atoms (rs_h nb) None (F_h nb).
(* The shadow entry of the cell's bytes: the nb bytes at the input cursor are marked
   usable. *)
Definition SH_h (nb : nat) : list shent := match nb with O => [] | _ => [mkSHE 21 0 (Z.of_nat nb)] end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SETH : theadamp_tx_set_spec B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the environment of the walk ---- *)
Definition hd_xs (cx : ecx) (fp : Z) (i : nat) : list Z :=
  [c_n cx - Z.of_nat (gpos (c_pl cx) i); gF cx fp + GO_SET; gF cx fp + GO_WAS;
   gc (c_pl cx) i; gq (c_pl cx) i; gv (c_pl cx) i].

Lemma hd_E : forall cx fp (i : nat) (regs : bvmap 5 word) E,
  E = Eimg (Ereg regs (map (Z_to_bv 64) (hd_xs cx fp i))) ->
  ew E 32 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) i)) /\ ew E 33 = w64 (gF cx fp + GO_SET) /\
  ew E 34 = w64 (gF cx fp + GO_WAS) /\ ew E 35 = w64 (gc (c_pl cx) i) /\
  ew E 36 = w64 (gq (c_pl cx) i) /\ ew E 37 = w64 (gv (c_pl cx) i) /\
  (forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r) /\
  img_env VAL A_LIM E.
Proof.
  intros cx fp i regs E HE.
  assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (map (Z_to_bv 64) (hd_xs cx fp i)) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  split; [exact (EX 0%nat ltac:(lia))|]. split; [exact (EX 1%nat ltac:(lia))|].
  split; [exact (EX 2%nat ltac:(lia))|]. split; [exact (EX 3%nat ltac:(lia))|].
  split; [exact (EX 4%nat ltac:(lia))|]. split; [exact (EX 5%nat ltac:(lia))|].
  split; [intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr|].
  subst E. apply Eimg_env.
Qed.

(* ---- the input bytes the cell reads ---- *)
Lemma hd_byte : forall (m : word -> option byte) (pl : list byte) a (j : nat),
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) pl) -> (j < length pl)%nat ->
  val_mem SEGS m (a + Z.of_nat j) 1 (GrantSlotPlan.pbz pl j).
Proof.
  intros m pl a j H Hj. destruct (H j ltac:(rewrite length_map; exact Hj)) as [Hv _].
  unfold GrantSlotPlan.pbz.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by (rewrite length_map; exact Hj).
  rewrite map_nth in Hv. exact Hv.
Qed.

Lemma hd_chunk_ok : forall cx (E : env) (m : word -> option byte) (p idx : nat) (off : Z) (n : nat),
  garr8 SEGS m (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  (idx < length (c_pl cx))%nat -> Z.of_nat idx = Z.of_nat p + off ->
  ew E n = Z_to_bv 64 (GrantSlotPlan.pbz (c_pl cx) idx) ->
  YP09.chunk_ok SEGS E m (c_p cx + Z.of_nat p) (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
  intros cx E m p idx off n Hin Hidx Hoff HE.
  pose proof (bv_unsigned_in_range 8 (nth idx (c_pl cx) (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply (chunk_ok_val SEGS E m (c_p cx + Z.of_nat p) off 1 (SOff n 0) (GrantSlotPlan.pbz (c_pl cx) idx)).
  - apply gsv0; [exact HE | unfold GrantSlotPlan.pbz; lia].
  - unfold GrantSlotPlan.pbz. cbn. lia.
  - cbn. lia.
  - replace (c_p cx + Z.of_nat p + off) with (c_p cx + Z.of_nat idx) by lia.
    exact (hd_byte m (c_pl cx) (c_p cx) idx Hin Hidx).
Qed.

(* ---- the call of reac_headamp_tx_set ---- *)
(* The bytes the set may write lie in the table. *)
Lemma hd_fp_in : forall t c q v a, 0 <= c -> 0 <= q < 256 -> 0 <= v < 256 ->
  inFP (set_fp t c q v) a -> t <= a < t + 460.
Proof.
  intros t c q v a Hc Hq Hv H. unfold set_fp in H.
  destruct ((c <? 48) && legalb q v)%bool eqn:EA; [|destruct (inFP_nil a H)].
  apply andb_true_iff in EA as [E1 E2]. apply Z.ltb_lt in E1.
  pose proof (SegSetModel.legalb_legal q v ltac:(lia) ltac:(lia) E2) as Hleg.
  destruct (SegSetModel.legal_bound _ _ Hleg) as [Hq3 _].
  rewrite !inFP_cons in H. destruct H as [H|[H|[H|[H|H]]]]; [lia | lia | lia | lia | destruct (inFP_nil a H)].
Qed.

(* The table is a block this function allocated: it is not one of the caller's. *)
Lemma hd_tmp : forall cx ly3 S3 W3 mem md t, AR SEGS B ly3 S3 W3 mem md -> gblk1 B cx ly3 S3 t ->
  forall a, t <= a < t + 460 -> in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a.
Proof.
  intros cx ly3 S3 W3 mem md t HAR Hbl a Ha. exists t, 460.
  split; [unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity|].
  split; [|change (req_size 460) with 460; lia].
  intros Hin. apply in_split in Hin as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (t, 460) (t, 460) l1 l2 [] HAR
    ltac:(unfold gblk1 in Hbl; rewrite Hbl, El, <- app_assoc; reflexivity)) as HD.
  unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD. change (req_size 460) with 460 in HD. lia.
Qed.

(* The turn's memory after the run to the call and the call: everything the turn's facts
   speak about is kept but slot 120 and the table, which are given anew. *)
Lemma hd_gmem_tr : forall cx fp t ly3 W3 (ms ms' : machine_state) T ws st v T' v',
  glayout cx fp t ly3 -> length ws = 144%nat -> length st = 144%nat ->
  (forall a, gkeep_at cx fp t a -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) -> ~ (t <= a < t + 460) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gslot cx W3 ms' 120 v' -> gtabb W3 ms' t T' ->
  gmem cx fp W3 ms t T ws st v -> gmem cx fp W3 ms' t T' ws st v'.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st v T' v' HL Hlw Hls HK H120' HT'
    (Hsv & Hsh & Hfl & Hin & Hmid & H64 & H120 & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= c_sp1 cx + 120 \/ c_sp1 cx + 128 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply HK; [left; lia | lia | lia]. }
  assert (GAK : forall p L, (forall a, p <= a < p + Z.of_nat (length L) ->
       gkeep_at cx fp t a /\ ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) /\ ~ (t <= a < t + 460)) ->
     garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) p L).
  { intros p L Hp H. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') p L); [|exact H].
    intros a Ha. destruct (Hp a Ha) as (H1 & H2 & H3). apply HK; assumption. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  unfold gmem, gsaved, gshadow, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | lia | apply Hsv, Hj]. }
  split.
  { intros j Hj. pose proof Hj as Hj'. rewrite GSH_tables_len in Hj'. unfold GE_NSH in Hj'.
    rewrite HK; [apply Hsh, Hj | right; right; right; left; lia | lia | lia]. }
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK; [right; right; left; lia | lia | lia]. }
  split.
  { apply GAK; [|exact Hin]. intros a Ha. rewrite length_map in Ha.
    assert (Ecn : c_n cx = Z.of_nat (length (c_pl cx))) by reflexivity.
    assert (Hn0 : 0 < c_n cx) by lia.
    destruct (L16 Hn0) as (P1 & P2 & P3 & P4 & P5).
    split; [right; left; lia | split; lia]. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split; [apply RDK; [lia | lia | lia | exact H64]|]. split; [exact H120'|].
  split; [exact HT'|].
  split; [apply GAK; [|exact Hws] | apply GAK; [|exact Hst]]; intros a Ha; rewrite length_map in Ha;
    unfold GO_WAS, GO_SET in *; (split; [right; right; left; lia | split; lia]).
Qed.

(* The call at BASE + AF_reac_headamp_tx_set with the table and the cell in a0 .. a3,
   from a memory that agrees with the turn's memory but on slot 120: it returns to
   BASE + retk with the set's answer in a0 and the table the set left. *)
Lemma hd_call : forall (POST : ecx -> world SEGS -> config -> Prop) cx fp k ly3 S3 W3 (i : nat) t
    (regs : bvmap 5 word) mem md retk (ms3 : machine_state) v120 v120',
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (gc (c_pl cx) i) -> getr regs 12 = w64 (gq (c_pl cx) i) ->
  getr regs 13 = w64 (gv (c_pl cx) i) ->
  gmem cx fp W3 ms3 t (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) v120 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
     aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 120) = Some v120' ->
  (forall regs2 mem2 md2,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved regs regs2 ->
     getr regs2 10 = w64 (if gacc (c_pl cx) i then 0 else -1) ->
     gmem cx fp W3 (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) t
       (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) v120' ->
     SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_set)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
  intros POST cx fp k ly3 S3 W3 i t regs mem md retk ms3 v120 v120' HB HJ HFR Hbl R1 Hrk Hrk2 R2 R8 R3 R4
    R10 R11 R12 R13 HM HK H120' HC.
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof HJ as (HAR & _).
  pose proof HM as ((Hra & Hsv) & _ & _ & _ & _ & _ & _ & HT & _).
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (KS : forall a, c_sp1 cx + 128 <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; apply HK; lia).
  assert (Hra' : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx))).
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8)); [exact Hra|].
    intros j Hj. apply KS. lia. }
  assert (Hs0 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (Hsv 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16)); [exact H0|].
    intros j Hj. apply KS. lia. }
  assert (HinT : In (t, TX_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (HTC : gtabb W3 (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_set)) mem (seg_rom SEGS)) t (gTi (c_pl cx) i)).
  { intros j Hj H1 H2 H3. cbn [ms_mem mkst]. rewrite HK by lia. apply HT; assumption. }
  assert (HFPin : forall a, inFP (set_fp t (gc (c_pl cx) i) (gq (c_pl cx) i) (gv (c_pl cx) i)) a -> t <= a < t + 460)
    by (intros a Ha; exact (hd_fp_in t (gc (c_pl cx) i) (gq (c_pl cx) i) (gv (c_pl cx) i) a
          ltac:(lia) ltac:(lia) ltac:(lia) Ha)).
  eapply (gcall B MT LAWS TSET_STK (set_fp t (gc (c_pl cx) i) (gq (c_pl cx) i) (gv (c_pl cx) i))
    (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
       getr regs' 10 = w64 (if ((gc (c_pl cx) i <? 48) && legalb (gq (c_pl cx) i) (gv (c_pl cx) i))%bool then 0 else -1) /\
       obj_at SEGS (mrestrict (w_H W3) mem') t LAY_TX
         (tx_vals (if ((gc (c_pl cx) i <? 48) && legalb (gq (c_pl cx) i) (gv (c_pl cx) i))%bool
                   then reac_headamp_tx_set_c.set_T (gTi (c_pl cx) i) (gc (c_pl cx) i) (gq (c_pl cx) i) (gv (c_pl cx) i)
                   else gTi (c_pl cx) i)))
    _ retk POST cx fp k ly3 S3 W3 regs mem md HB HJ R2 R8 R3 R4 R1 Hrk Hrk2 Hra' Hs0
    ltac:(unfold TSET_STK, ESTACK; lia)
    ltac:(intros a Ha; exact (hd_tmp cx ly3 S3 W3 mem md t HAR Hbl a (HFPin a Ha)))).
  - intros HPRE. exact (SETH ly3 S3 W3 regs mem md (gch cx) t (gc (c_pl cx) i) (gq (c_pl cx) i) (gv (c_pl cx) i)
      (gTi (c_pl cx) i) HPRE R10 R11 R12 R13 ltac:(lia) ltac:(lia) ltac:(lia) HinT LT (gtabb_obj W3 _ t _ HTC)).
  - intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & H10 & HO).
    assert (KC : forall a, gkeep_at cx fp t a -> ~ (t <= a < t + 460) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem a)
      by (intros a Ha Ht; exact (gkeep_callT B MT LAWS cx fp k ly3 S3 W3 mem md TSET_STK _ mem2 md2 t HB HJ HFR Hbl
            ltac:(unfold TSET_STK, ESTACK; lia) HFPin HJc a Ha (fun Hf => Ht (HFPin a Hf)))).
    apply (HC regs2 mem2 md2 HJ2 HP).
    + rewrite H10. unfold gacc. reflexivity.
    + destruct (gtables_S (c_pl cx) i) as (ET & _ & _).
      apply (hd_gmem_tr cx fp t ly3 W3 ms3 (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS))
        (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) v120 (gTi (c_pl cx) (S i)) v120' HL LW LS); [| | | exact HM].
      * intros a Ha Hs Ht. cbn [ms_mem mkst]. rewrite (KC a Ha Ht). apply HK; [|exact Hs].
        destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [lia | | lia | unfold SHADOW_OFF in L11; lia | lia].
        assert (Hn0 : 0 < c_n cx) by lia. destruct (L16 Hn0) as (P1 & P2 & _). lia.
      * unfold gslot. cbn [ms_mem mkst].
        rewrite (rdword_tr (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) mem2) (c_sp1 cx + 120)); [exact H120'|].
        intros j Hj. apply KC; [left; lia | lia].
      * rewrite ET. unfold gacc.
        exact (obj_gtabb W3 (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) t _ HO).
Qed.

(* ---- the seat at 0x80aa4 ---- *)
Lemma hd_seat : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 (i : nat) t T ws st (nb : nat) E,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t -> c_n cx < 2 ^ 26 ->
  getr (ms_regs ms3) 9 = w64 (c_sp1 cx) ->
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)) ->
  gmem cx fp W3 ms3 t T ws st (c_n cx - Z.of_nat (gpos (c_pl cx) i)) ->
  (nb <= 3)%nat -> (gpos (c_pl cx) i + nb <= length (c_pl cx))%nat ->
  (if (nb <? 3)%nat then c_n cx - Z.of_nat (gpos (c_pl cx) i) = Z.of_nat nb
   else 3 <= c_n cx - Z.of_nat (gpos (c_pl cx) i)) ->
  ((0 < nb)%nat -> GrantSlotPlan.pbz (c_pl cx) (gpos (c_pl cx) i) = gc (c_pl cx) i) ->
  ((1 < nb)%nat -> GrantSlotPlan.pbz (c_pl cx) (S (gpos (c_pl cx) i)) = gq (c_pl cx) i) ->
  ((2 < nb)%nat -> GrantSlotPlan.pbz (c_pl cx) (S (S (gpos (c_pl cx) i))) = gv (c_pl cx) i) ->
  E = Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) (hd_xs cx fp i))) ->
  st_ok_pi SEGS VAL E (ss_h nb)
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 0x3f4)) (ms_mem ms3) (seg_rom SEGS))) /\
  sh_ok SEGS GBx (SH_h nb) E (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 i t T ws st nb E HB HJ HFR Hbl Hn R9 R21 HM Hnb Hlen H32 HB0 HB1 HB2 HE.
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gpos_le (c_pl cx) i) as Hpl.
  pose proof HM as (_ & _ & _ & Hin & Hmid & _ & H120 & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
  pose proof HB as (_ & _ & _ & Hpn & _).
  destruct (hd_E cx fp i (ms_regs ms3) E HE) as (E32 & E33 & E34 & E35 & E36 & E37 & ER & HEI).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i))) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
  assert (Hv120 : 0 <= c_n cx - Z.of_nat (gpos (c_pl cx) i) < 2 ^ 26) by (unfold c_n in *; lia).
  assert (Hp21 : 4096 <= c_p cx + Z.of_nat (gpos (c_pl cx) i) <= 140737479966720).
  { destruct Hpn as [[Hn0 Hp0] | [Hn1 _]].
    - unfold c_n in Hn0. rewrite Hp0. unfold GE_EMPTY. lia.
    - destruct (L16 (proj1 Hn1)) as (P1 & P2 & _). unfold c_n in *. lia. }
  assert (Hinl : (0 < nb)%nat -> c_p cx + Z.of_nat (gpos (c_pl cx) i) + Z.of_nat nb <= alloc_ceiling).
  { intros Hnb0. destruct Hpn as [[Hn0 _] | [Hn1 _]]; [unfold c_n in Hn0; lia|].
    destruct (L16 (proj1 Hn1)) as (P1 & P2 & _). unfold c_n in *. lia. }
  pose proof (R_stk_ok cx fp t ly3 W3 ms3 E (c_n cx - Z.of_nat (gpos (c_pl cx) i)) HL HSP E9 E32 E33 E34 Hv120 H120 Hmid) as RSTK.
  assert (RIN : (0 < nb)%nat -> region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (R_in nb)).
  { intros Hnb0.
    destruct Hpn as [[Hn0 _] | [Hn1 HinP]]; [unfold c_n in Hn0; lia|].
    destruct (L16 (proj1 Hn1)) as (P1 & P2 & P3 & P4 & P5).
    unfold region_ok, R_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E21. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [unfold c_n in *; lia|]. split; [intros o Ho; lia|].
    destruct nb as [|[|[|[|nb]]]]; [lia | | | | lia]; cbn [firstn];
      repeat apply Forall_cons; try apply Forall_nil.
    all: first
      [ apply (hd_chunk_ok cx E _ (gpos (c_pl cx) i) (gpos (c_pl cx) i) 0 35);
          [exact Hin | lia | lia | rewrite E35, <- HB0 by lia; reflexivity]
      | apply (hd_chunk_ok cx E _ (gpos (c_pl cx) i) (S (gpos (c_pl cx) i)) 1 36);
          [exact Hin | lia | lia | rewrite E36, <- HB1 by lia; reflexivity]
      | apply (hd_chunk_ok cx E _ (gpos (c_pl cx) i) (S (S (gpos (c_pl cx) i))) 2 37);
          [exact Hin | lia | lia | rewrite E37, <- HB2 by lia; reflexivity] ]. }
  split.
  - rewrite restrict_mkst_fx. unfold ss_h. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + destruct nb as [|[|[|[|nb]]]]; [vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | lia].
    + destruct nb as [|[|[|[|nb]]]]; [| | | | lia]; cbn [rs_h];
        repeat apply Forall_cons; try apply Forall_nil; first [exact RSTK | apply RIN; lia].
    + destruct nb as [|[|[|[|nb]]]]; [| | | | lia]; apply pairwise_disjoint_of_extents;
        unfold rs_h, R_stk, R_in, extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?E9, ?E21; unfold w64; rewrite ?unsigned_lit_small by lia;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
        splits; try exact I; try (specialize (Hinl ltac:(lia))); lia.
    + split; [|split; exact I].
      destruct nb as [|[|[|[|nb]]]]; [| | | | lia]; cbn [F_h AF32 f_atoms atoms_ok]; unfold afact_ok, PTRA;
        cbn [af_lo af_hi af_al2]; rewrite E9, E21, E32, E35, E36, E37; unfold w64;
        rewrite !unsigned_lit_small by lia; change (2 ^ 5) with 32; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
        cbn in H32; splits; lia.
  - destruct nb as [|[|[|[|nb]]]]; [apply Forall_nil | | | | lia];
      (constructor; [|apply Forall_nil]);
      (destruct Hpn as [[Hn0 _] | [Hn1 HinP]]; [unfold c_n in Hn0; lia|]);
      destruct (L16 (proj1 Hn1)) as (P1 & P2 & P3 & P4 & P5);
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq];
      (assert (HinP3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; left; exact HinP));
      unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; unfold GBx;
      rewrite U_lit by (unfold GSB; lia); rewrite (U_atom E 21 _ E21) by lia;
      (split;
       [ rewrite <- (aview_rd_of SEGS); replace GSB with SHADOW_OFF by reflexivity;
         apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx));
         [exact HAR | exact HinP3 | lia | unfold c_n in *; lia]
       | intros a Ha; unfold kLowShadowBeg, kHighMemBeg, GSB in *; lia ]).
Qed.

(* ---- reading the run back ---- *)
Ltac hd_cur HS := lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?m) => m
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m end.

(* The run may write the window of the region at s1 (slot 120, in this function's
   machine frame); the cell's bytes are read-only. *)
Ltac hd_awr cx E9 :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
  | cbn [YP09.r_wlo]; unfold GE_STK; lia
  | cbn [YP09.r_whi]; lia
  | ];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]);
  apply awr_ok_nil.

(* The windows of the walk's regions: slot 120 only (the cell's bytes are read-only). *)
Ltac hd_win E9 :=
  let x := fresh "x" in let r := fresh "r" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in
  intros x (r & Hr & Hx); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [Hr | Hr];
          [ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
            first [ lia
                  | cbn [ew ewset Nat.eqb] in Hx; rewrite E9 in Hx; unfold w64 in Hx;
                    rewrite unsigned_lit_small in Hx by lia; lia ]
          | ]);
  try destruct Hr.

(* The runs from 0x80aa4 kept every byte but slot 120. *)
Ltac hd_keep cx E9 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
  intros a Ha Hw;
  repeat match goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- aview _ _ ?m1 _ = _ =>
      rewrite (frame_wins Ex rs Hh m0 m1 (fun z => c_sp1 cx + 120 <= z < c_sp1 cx + 128) HFr);
      [ | hd_win E9 | exact Ha | exact Hw ]
  end;
  reflexivity.

(* Slot 120 after the run, from the walk's region at s1. *)
Ltac hd_slot HS W3 E9 E32 cx e v :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let r0 := eval vm_compute in (nth_error (ss_mem ssx) 0) in
    lazymatch r0 with Some ?R0 =>
      let FR0 := fresh "FR0" in
      pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 0 R0 HS ltac:(vm_compute; reflexivity)) as FR0;
      cbn [ms_mem restrict] in FR0;
      assert (S120 : rdword (aview SEGS (w_H W3) (ms_mem msx)) (c_sp1 cx + 120) = Some v);
      [ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msx)); [|lia];
        eapply (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N e v FR0);
        [ cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; apply unsigned_lit_small; lia
        | left; reflexivity
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite ?E32; try unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia
        | cbn; lia | cbn; lia ]
      | clear FR0 ]
    end end.

(* A register the run left as the entry register's atom. *)
Ltac hd_rr HS ER r n Q := prreg HS r Q; rewrite (ER n r eq_refl) in Q.

(* The branch the cell's length rules out. *)
Ltac hd_nobr E32 :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, U_SOff, U_SLit in Hc;
    cbn [ew ewset Nat.eqb] in Hc; rewrite E32 in Hc; unfold w64 in Hc;
    rewrite unsigned_lit_small in Hc by lia; rewrite !zcanon_id in Hc by (unfold M64; lia);
    lazymatch type of Hc with context [?x =? ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) in Hc by lia | rewrite (proj2 (Z.eqb_neq x y)) in Hc by lia ] end;
    cbn [negb] in Hc; discriminate Hc
  end.

(* The registers the run to the call leaves as the entry registers' atoms. *)
Ltac hd_rrG HS ER r n G Q := prreg HS r Q; rewrite (ER n r eq_refl), G in Q.
Ltac hd_regs HS ER G2 G8 G9 G3 G4 G20 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q22 Q27 :=
  hd_rrG HS ER (2%bv : bv 5) 2%nat G2 Q2; hd_rrG HS ER (8%bv : bv 5) 8%nat G8 Q8;
  hd_rrG HS ER (9%bv : bv 5) 9%nat G9 Q9; hd_rrG HS ER (3%bv : bv 5) 3%nat G3 Q3;
  hd_rrG HS ER (4%bv : bv 5) 4%nat G4 Q4;
  hd_rr HS ER (19%bv : bv 5) 19%nat Q19; hd_rr HS ER (20%bv : bv 5) 20%nat Q20;
  hd_rr HS ER (22%bv : bv 5) 22%nat Q22; hd_rr HS ER (27%bv : bv 5) 27%nat Q27;
  prreg HS (10%bv : bv 5) Q10; rewrite (ER 20%nat (20%bv : bv 5) eq_refl), G20 in Q10;
  prreg HS (1%bv : bv 5) Q1.

(* The callee-saved registers across the call. *)
Ltac hd_pres HP regs regs2 :=
  assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia));
  assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia));
  assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia));
  assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia));
  assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia));
  assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia));
  assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia));
  assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia));
  assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia));
  assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia));
  assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia));
  assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia));
  assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia));
  assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).

(* ---- HEAD: 0x80aa4 → the call of reac_headamp_tx_set → GA0 | GA1 | GA2 ---- *)
Lemma ge_set_head : seg_head_stmt B MT.
Proof.
  intros POST n H0 H1 H2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (HG & H27n & Hnb).
  destruct (of_set B MT cx fp k acc ly3 S3 W3 ms3 md3 HG)
    as (i & t & HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hi & R19 & R20 & R21 & R22 & R27 & HM).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  assert (Hns : GrantSlotPlan.nset (c_pl cx) = Z.of_nat i + Z.of_nat (S n)).
  { pose proof (SegSetModel.rd8_range (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) as Hnr.
    change (fst (GrantSlotPlan.rd8 (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))))
      with (GrantSlotPlan.nset (c_pl cx)) in Hnr.
    pose proof H27n as H27c. rewrite R27 in H27c. apply (f_equal (@bv_unsigned 64)) in H27c. unfold w64 in H27c.
    rewrite !unsigned_lit_small in H27c by lia. lia. }
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gpos_le (c_pl cx) i) as Hpl.
  remember (Eimg (Ereg (ms_regs ms3) (map (Z_to_bv 64) (hd_xs cx fp i)))) as E eqn:HE.
  destruct (hd_E cx fp i (ms_regs ms3) E HE) as (E32 & E33 & E34 & E35 & E36 & E37 & ER & HEI).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact G9).
  assert (E21 : ew E 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i))) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
  assert (Ecn : c_n cx = Z.of_nat (length (c_pl cx))) by reflexivity.
  assert (Hv120 : 0 <= c_n cx - Z.of_nat (gpos (c_pl cx) i) < 2 ^ 26) by lia.
  assert (Hp21 : 0 <= c_p cx + Z.of_nat (gpos (c_pl cx) i) + 3 < 2 ^ 64).
  { pose proof HB as (_ & _ & _ & Hpn & _). destruct Hpn as [[Hn0 Hp0] | [Hn1 _]].
    - rewrite Hp0. unfold GE_EMPTY. lia.
    - destruct (L16 (proj1 Hn1)) as (P1 & P2 & _). unfold c_n in *. lia. }
  rewrite (gmach_mkst cx ms3 _ HMA). unfold GP_set.
  pose proof (gcell_cases (c_pl cx) i) as HCC. cbv zeta in HCC.
  destruct HCC as [(Hl3 & Hcell & Hps) | [(Hl2 & Hcell & Hps) | [(Hl1 & Hcell & Hps) | (Hl0 & Hcell & Hps)]]].
  - (* three bytes or more: slot 120 := bytes left - 3, the call at 0x80b54, GA2 *)
    assert (Ec : gc (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (gpos (c_pl cx) i)) by (unfold gc; rewrite Hcell; reflexivity).
    assert (Eq : gq (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (S (gpos (c_pl cx) i))) by (unfold gq; rewrite Hcell; reflexivity).
    assert (Ev : gv (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (S (S (gpos (c_pl cx) i)))) by (unfold gv; rewrite Hcell; reflexivity).
    destruct (hd_seat cx fp k ly3 S3 W3 ms3 md3 i t _ _ _ 3 E HB HJ HFR Hbl Hn G9 R21 HM ltac:(lia) ltac:(lia)
      ltac:(cbn; lia) ltac:(intros; symmetry; exact Ec) ltac:(intros; symmetry; exact Eq)
      ltac:(intros; symmetry; exact Ev) HE) as [HS SHOK].
    paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
    pmkst HS. rewrite pa_sigma_reac_headamp_tx_set.
    let msF := hd_cur HS in
    assert (HKR : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
       aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (hd_keep cx E9).
    hd_slot HS W3 E9 E32 cx (SOff 32 (-3)) (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))).
    hd_regs HS ER G2 G8 G9 G3 G4 R20 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q22 Q27.
    prreg HS (11%bv : bv 5) Q11. rewrite E35 in Q11.
    prreg HS (12%bv : bv 5) Q12. rewrite E36 in Q12.
    prreg HS (13%bv : bv 5) Q13. rewrite E37 in Q13.
    prreg HS (18%bv : bv 5) Q18. rewrite E35 in Q18.
    prreg HS (23%bv : bv 5) Q23. rewrite E36 in Q23.
    prreg HS (24%bv : bv 5) Q24. rewrite E37 in Q24.
    prreg HS (26%bv : bv 5) Q26. rewrite E21 in Q26. unfold w64 in Q26. rewrite unsigned_lit_small in Q26 by lia.
    let msF := hd_cur HS in
    apply (hd_call POST cx fp k ly3 S3 W3 i t (ms_regs msF) (ms_mem msF) _ 0x4a8 ms3
      (c_n cx - Z.of_nat (gpos (c_pl cx) i)) (c_n cx - Z.of_nat (gpos (c_pl cx) (S i)))
      HB HJ HFR Hbl Q1 ltac:(lia) eq_refl Q2 Q8 Q3 Q4 Q10 Q11 Q12 Q13 HM HKR S120).
    intros regs2 mem2 md2 HJ2 HP H10 HM2.
    apply (H2 i cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x4a8)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
    let msF := hd_cur HS in hd_pres HP (ms_regs msF) regs2.
    exists t. unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
    rewrite P2, P3, P4, P8, P9, P18, P19, P20, P22, P23, P24, P26, P27.
    rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q22, Q23, Q24, Q26, Q27.
    splits; try reflexivity; try assumption; try lia.
    rewrite Hps. unfold w64. f_equal. lia.
  - (* two bytes: slot 120 := 0, the call at 0x80b54 with value 0, GA2 *)
    assert (Ec : gc (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (gpos (c_pl cx) i)) by (unfold gc; rewrite Hcell; reflexivity).
    assert (Eq : gq (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (S (gpos (c_pl cx) i))) by (unfold gq; rewrite Hcell; reflexivity).
    assert (Ev : gv (c_pl cx) i = 0) by (unfold gv; rewrite Hcell; reflexivity).
    assert (Hv2 : c_n cx - Z.of_nat (gpos (c_pl cx) i) = 2) by (unfold c_n; lia).
    destruct (hd_seat cx fp k ly3 S3 W3 ms3 md3 i t _ _ _ 2 E HB HJ HFR Hbl Hn G9 R21 HM ltac:(lia) ltac:(lia)
      ltac:(cbn; lia) ltac:(intros; symmetry; exact Ec) ltac:(intros; symmetry; exact Eq)
      ltac:(intros; lia) HE) as [HS SHOK].
    paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
    psrr_branch_tok RUN BR HS SHOK GBspan.
    + exfalso. hd_nobr E32.
    + paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
      pmkst HS. rewrite pa_sigma_reac_headamp_tx_set.
      let msF := hd_cur HS in
      assert (HKR : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
         aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (hd_keep cx E9).
      hd_slot HS W3 E9 E32 cx (SLit 0) (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))).
      hd_regs HS ER G2 G8 G9 G3 G4 R20 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q22 Q27.
      prreg HS (11%bv : bv 5) Q11. rewrite E35 in Q11.
      prreg HS (12%bv : bv 5) Q12. rewrite E36 in Q12.
      prreg HS (13%bv : bv 5) Q13.
      prreg HS (18%bv : bv 5) Q18. rewrite E35 in Q18.
      prreg HS (23%bv : bv 5) Q23. rewrite E36 in Q23.
      prreg HS (24%bv : bv 5) Q24.
      prreg HS (26%bv : bv 5) Q26. rewrite E21 in Q26. unfold w64 in Q26. rewrite unsigned_lit_small in Q26 by lia.
      let msF := hd_cur HS in
      assert (Q13' : getr (ms_regs msF) 13 = w64 (gv (c_pl cx) i)) by (rewrite Q13, Ev; reflexivity).
      let msF := hd_cur HS in
      apply (hd_call POST cx fp k ly3 S3 W3 i t (ms_regs msF) (ms_mem msF) _ 0x4a8 ms3
        (c_n cx - Z.of_nat (gpos (c_pl cx) i)) (c_n cx - Z.of_nat (gpos (c_pl cx) (S i)))
        HB HJ HFR Hbl Q1 ltac:(lia) eq_refl Q2 Q8 Q3 Q4 Q10 Q11 Q12 Q13' HM HKR S120).
      intros regs2 mem2 md2 HJ2 HP H10 HM2.
      apply (H2 i cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x4a8)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msF := hd_cur HS in hd_pres HP (ms_regs msF) regs2.
      exists t. unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      rewrite P2, P3, P4, P8, P9, P18, P19, P20, P22, P23, P24, P26, P27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q22, Q23, Q24, Q26, Q27.
      splits; try reflexivity; try assumption; try lia.
      * rewrite Ev. reflexivity.
      * rewrite Hps. unfold w64. f_equal. lia.
  - (* one byte: the call at 0x80bb4 with ch 0 0, GA1 *)
    assert (Ec : gc (c_pl cx) i = GrantSlotPlan.pbz (c_pl cx) (gpos (c_pl cx) i)) by (unfold gc; rewrite Hcell; reflexivity).
    assert (Eq : gq (c_pl cx) i = 0) by (unfold gq; rewrite Hcell; reflexivity).
    assert (Ev : gv (c_pl cx) i = 0) by (unfold gv; rewrite Hcell; reflexivity).
    assert (Hv1 : c_n cx - Z.of_nat (gpos (c_pl cx) i) = 1) by (unfold c_n; lia).
    destruct (hd_seat cx fp k ly3 S3 W3 ms3 md3 i t _ _ _ 1 E HB HJ HFR Hbl Hn G9 R21 HM ltac:(lia) ltac:(lia)
      ltac:(cbn; lia) ltac:(intros; symmetry; exact Ec) ltac:(intros; lia) ltac:(intros; lia) HE) as [HS SHOK].
    paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
    psrr_branch_tok RUN BR HS SHOK GBspan.
    + paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
      pmkst HS. rewrite pa_sigma_reac_headamp_tx_set.
      let msF := hd_cur HS in
      assert (HKR : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
         aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (hd_keep cx E9).
      hd_slot HS W3 E9 E32 cx (SOff 32 0) (c_n cx - Z.of_nat (gpos (c_pl cx) i)).
      hd_regs HS ER G2 G8 G9 G3 G4 R20 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q22 Q27.
      prreg HS (11%bv : bv 5) Q11. rewrite E35 in Q11.
      prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13.
      prreg HS (18%bv : bv 5) Q18. rewrite E35 in Q18.
      prreg HS (26%bv : bv 5) Q26. rewrite E21 in Q26. unfold w64 in Q26. rewrite unsigned_lit_small in Q26 by lia.
      let msF := hd_cur HS in
      assert (Q12' : getr (ms_regs msF) 12 = w64 (gq (c_pl cx) i)) by (rewrite Q12, Eq; reflexivity).
      let msF := hd_cur HS in
      assert (Q13' : getr (ms_regs msF) 13 = w64 (gv (c_pl cx) i)) by (rewrite Q13, Ev; reflexivity).
      let msF := hd_cur HS in
      apply (hd_call POST cx fp k ly3 S3 W3 i t (ms_regs msF) (ms_mem msF) _ 0x508 ms3
        (c_n cx - Z.of_nat (gpos (c_pl cx) i)) (c_n cx - Z.of_nat (gpos (c_pl cx) i))
        HB HJ HFR Hbl Q1 ltac:(lia) eq_refl Q2 Q8 Q3 Q4 Q10 Q11 Q12' Q13' HM HKR S120).
      intros regs2 mem2 md2 HJ2 HP H10 HM2.
      apply (H1 i cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x508)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msF := hd_cur HS in hd_pres HP (ms_regs msF) regs2.
      exists t. unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      rewrite P2, P3, P4, P8, P9, P18, P19, P20, P22, P26, P27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q22, Q26, Q27.
      splits; try reflexivity; try assumption; try lia.
      rewrite Hps. unfold w64. f_equal. lia.
    + exfalso. hd_nobr E32.
  - (* no byte: the call at 0x80b08 with 0 0 0, GA0 *)
    assert (Ec : gc (c_pl cx) i = 0) by (unfold gc; rewrite Hcell; reflexivity).
    assert (Eq : gq (c_pl cx) i = 0) by (unfold gq; rewrite Hcell; reflexivity).
    assert (Ev : gv (c_pl cx) i = 0) by (unfold gv; rewrite Hcell; reflexivity).
    assert (Hv0' : c_n cx - Z.of_nat (gpos (c_pl cx) i) = 0) by (unfold c_n; lia).
    destruct (hd_seat cx fp k ly3 S3 W3 ms3 md3 i t _ _ _ 0 E HB HJ HFR Hbl Hn G9 R21 HM ltac:(lia) ltac:(lia)
      ltac:(cbn; lia) ltac:(intros; lia) ltac:(intros; lia) ltac:(intros; lia) HE) as [HS SHOK].
    paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
    psrr_branch_tok RUN BR HS SHOK GBspan.
    + paj_run_tok RUN HS HJ SHOK GBspan; [hd_awr cx E9 |].
      pmkst HS. rewrite pa_sigma_reac_headamp_tx_set.
      let msF := hd_cur HS in
      assert (HKR : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
         aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (hd_keep cx E9).
      hd_slot HS W3 E9 E32 cx (SOff 32 0) (c_n cx - Z.of_nat (gpos (c_pl cx) i)).
      hd_regs HS ER G2 G8 G9 G3 G4 R20 Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q19 Q20 Q22 Q27.
      hd_rr HS ER (21%bv : bv 5) 21%nat Q21.
      prreg HS (11%bv : bv 5) Q11.
      prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13. rewrite E32 in Q13.
      let msF := hd_cur HS in
      assert (Q11' : getr (ms_regs msF) 11 = w64 (gc (c_pl cx) i)) by (rewrite Q11, Ec; reflexivity).
      let msF := hd_cur HS in
      assert (Q12' : getr (ms_regs msF) 12 = w64 (gq (c_pl cx) i)) by (rewrite Q12, Eq; reflexivity).
      let msF := hd_cur HS in
      assert (Q13' : getr (ms_regs msF) 13 = w64 (gv (c_pl cx) i)) by (rewrite Q13, Ev, Hv0'; reflexivity).
      let msF := hd_cur HS in
      apply (hd_call POST cx fp k ly3 S3 W3 i t (ms_regs msF) (ms_mem msF) _ 0x45c ms3
        (c_n cx - Z.of_nat (gpos (c_pl cx) i)) (c_n cx - Z.of_nat (gpos (c_pl cx) i))
        HB HJ HFR Hbl Q1 ltac:(lia) eq_refl Q2 Q8 Q3 Q4 Q10 Q11' Q12' Q13' HM HKR S120).
      intros regs2 mem2 md2 HJ2 HP H10 HM2.
      apply (H0 i cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x45c)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
      let msF := hd_cur HS in hd_pres HP (ms_regs msF) regs2.
      exists t. unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      rewrite P2, P3, P4, P8, P9, P19, P20, P21, P22, P27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q19, Q20, Q21, Q22, Q27.
      splits; try reflexivity; try assumption; try lia.
    + exfalso. hd_nobr E32.
Qed.

End a.
