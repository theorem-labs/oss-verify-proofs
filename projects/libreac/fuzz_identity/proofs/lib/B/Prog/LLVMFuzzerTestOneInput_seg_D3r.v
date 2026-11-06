(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* seg_D3r of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): inv_ignored -> inv_tail, the ignored-record
   branch +0x7b4 .. +0xe24 (0x80f28 .. 0x81598). The record was ignored by reac_identity_ingest (rec_r = 0), so
   the harness re-checks that nothing changed: the bcmp at 0x80f34 (`before` against `id`, 38 bytes, equal
   because the identity is unchanged) and the three "an accepted record would have been seen" checks of the
   firmware (0x80f44..), REAC-version (0x8154c..) and model-name (0x81560..) cases, none of which aborts
   (d3r_fw, d3r_ver, d3r_name refute the aborting side from the plain model). The two runs (the bcmp call
   d3r_call, the checks d3r_rest) store nothing outside the bcmp wrapper's own stack window [mf - 2*ESTACK, mf),
   so inv_tail is inv_ignored's state re-stated at the end. seg_D3r_stmt is fixed in LLVMFuzzerTestOneInput_inv.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address arithmetic of
   this segment (the shadow addresses of the frame's variables, the machine frame's alignment) needs it, so this
   file turns it back on (as lib/A/Prog/LLVMFuzzerTestOneInput_D6.v does). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* rec_hwb is always eight bytes (the frame slot is eight wide). *)
Lemma d3r_hwb_len : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.
(* ---- the model: what a record that reac_identity_ingest ignores (rec_r = 0) leaves and rules out ----------- *)
(* The identity is unchanged (RcIdentModel.ING_ignored). *)
Lemma d3r_id_same : forall inp i, SlotModel.rec_r inp i = 0 -> SlotModel.rec_id inp (S i) = SlotModel.rec_id inp i.
Proof. intros inp i Hr. cbn [SlotModel.rec_id]. apply RcIdentModel.ING_ignored. exact Hr. Qed.
(* An ignored REAC-version record has fewer than eight bytes (ing_version accepts eight or more). *)
Lemma d3r_ver : forall inp i, SlotModel.rec_r inp i = 0 ->
  SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION -> SlotModel.rec_k inp i < 8.
Proof.
intros inp i Hr Ha. destruct (Z_lt_le_dec (SlotModel.rec_k inp i) 8) as [H|H]; [exact H|]. exfalso.
pose proof (SlotModel.rec_pl_length inp i) as Hl. unfold SlotModel.rec_r in Hr. rewrite Ha in Hr.
rewrite SlotModel.ING_ver_dispatch in Hr. unfold RcIdentModel.ing_version in Hr.
replace (RcIdentModel.REAC_VER_LEN <=? length (SlotModel.rec_pl inp i))%nat with true in Hr
  by (symmetry; apply Nat.leb_le; unfold RcIdentModel.REAC_VER_LEN; lia).
cbn [fst] in Hr. discriminate Hr.
Qed.
(* So the harness's `hw` record is unchanged: only an accepted version record of eight bytes sets it. *)
Lemma d3r_hw_same : forall inp i, SlotModel.rec_r inp i = 0 -> SlotModel.rec_hw inp (S i) = SlotModel.rec_hw inp i.
Proof.
intros inp i Hr. cbn [SlotModel.rec_hw].
destruct (Z.eqb_spec (SlotModel.rec_addr inp i) RcIdentModel.ADDR_REAC_VERSION) as [Ha|Ha]; cbn [andb]; [|reflexivity].
pose proof (d3r_ver inp i Hr Ha) as Hk.
replace (8 <=? SlotModel.rec_k inp i) with false by (symmetry; apply Z.leb_gt; exact Hk). reflexivity.
Qed.
(* An ignored firmware record of four bytes or more has a byte above 9 among its first four (ing_firmware). *)
Lemma d3r_fw : forall inp i, SlotModel.rec_r inp i = 0 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_FIRMWARE ->
  4 <= SlotModel.rec_k inp i ->
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 0) <= 9 ->
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1) <= 9 ->
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2) <= 9 ->
  9 < RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3).
Proof.
intros inp i Hr Ha Hk H0 H1 H2.
destruct (Z_lt_le_dec 9 (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3))) as [H|H3]; [exact H|].
exfalso.
pose proof (SlotModel.rec_pl_length inp i) as Hl. unfold SlotModel.rec_r in Hr. rewrite Ha in Hr.
revert Hl H0 H1 H2 H3 Hr. generalize (SlotModel.rec_pl inp i) as p. intros p Hl H0 H1 H2 H3 Hr.
assert (E : ((4 <=? length p)%nat && RcIdentModel.all_digits (firstn 4 p))%bool = true).
{ destruct p as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hl; try lia.
  unfold RcIdentModel.nthb in *. cbn [nth] in *. unfold RcIdentModel.all_digits.
  cbn [firstn forallb length Nat.leb].
  rewrite (proj2 (Z.leb_le _ _) H0), (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2),
    (proj2 (Z.leb_le _ _) H3). reflexivity. }
unfold RcIdentModel.ING in Hr. change (RcIdentModel.ADDR_FIRMWARE =? RcIdentModel.ADDR_FIRMWARE) with true in Hr.
cbv beta iota in Hr. unfold RcIdentModel.ing_firmware in Hr. rewrite E in Hr. cbn [fst] in Hr. discriminate Hr.
Qed.
(* An ignored model-name record of two bytes or more has its first name byte 0 (ing_name). *)
Lemma d3r_name : forall inp i, SlotModel.rec_r inp i = 0 ->
  SlotModel.rec_addr inp i = RcIdentModel.ADDR_MODEL_NAME -> 2 <= SlotModel.rec_k inp i ->
  RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1) = 0.
Proof.
intros inp i Hr Ha Hk. pose proof (SlotModel.rec_pl_length inp i) as Hl. unfold SlotModel.rec_r in Hr. rewrite Ha in Hr.
revert Hl Hr. generalize (SlotModel.rec_pl inp i) as p. intros p Hl Hr.
destruct p as [|b0 [|b1 r]]; cbn [length] in Hl; try lia.
unfold RcIdentModel.nthb. cbn [nth].
destruct (Z.eqb_spec (RcIdentModel.bz b1) 0) as [E|E]; [exact E|]. exfalso.
assert (W : (1 <= RcIdentModel.name_len (b0 :: b1 :: r))%nat).
{ unfold RcIdentModel.name_len, RcIdentModel.NAME_CAP. cbn [length skipn].
  replace (S (S (length r)) - 1)%nat with (S (length r)) by lia.
  replace (Nat.min (S (length r)) (17 - 1)) with (S (Nat.min (length r) 15)) by lia.
  cbn [firstn RcIdentModel.first_zero]. rewrite (proj2 (Z.eqb_neq _ _) E). lia. }
unfold RcIdentModel.ING in Hr. change (RcIdentModel.ADDR_MODEL_NAME =? RcIdentModel.ADDR_FIRMWARE) with false in Hr.
change (RcIdentModel.ADDR_MODEL_NAME =? RcIdentModel.ADDR_MODEL_NAME) with true in Hr. cbv beta iota in Hr.
unfold RcIdentModel.ing_name in Hr. cbv zeta in Hr.
rewrite (proj2 (Nat.leb_le 1 _) W) in Hr. cbn [length Nat.leb andb fst] in Hr. discriminate Hr.
Qed.
(* The record's address is one of the three modelled ones or a raw value of 49152 or more (SlotModel.pick). *)
Lemma d3r_addr_cases : forall inp i,
  SlotModel.rec_addr inp i = 0 \/ SlotModel.rec_addr inp i = 1536 \/ SlotModel.rec_addr inp i = 4096 \/
  49152 <= SlotModel.rec_addr inp i <= 65535.
Proof.
intros inp i. unfold SlotModel.rec_addr, SlotModel.pick.
assert (Hr : 0 <= SlotModel.rec_raw inp i <= 65535).
{ unfold SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
  pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i)).
  pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i + 1)). lia. }
revert Hr. generalize (SlotModel.rec_raw inp i) as raw. intros raw Hr.
destruct (Z.eqb_spec (raw / 16384) 0) as [E0|E0]; [left; reflexivity|].
destruct (Z.eqb_spec (raw / 16384) 1) as [E1|E1]; [right; left; reflexivity|].
destruct (Z.eqb_spec (raw / 16384) 2) as [E2|E2]; [right; right; left; reflexivity|].
right; right; right. lia.
Qed.

(* ---- small memory facts ---------------------------------------------------------------------------------- *)
Section m.
Variable segs : list Segment.
Lemma d3r_aview_some : forall H (m : word -> option byte) a v,
  val_mem segs (mrestrict H m) a 1 v -> aview segs H m a <> None.
Proof.
intros H m a v Hv. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. discriminate.
Qed.
Lemma d3r_aview_eq : forall H (m : word -> option byte) a b v,
  val_mem segs (mrestrict H m) a 1 v -> val_mem segs (mrestrict H m) b 1 v -> aview segs H m a = aview segs H m b.
Proof.
intros H m a b v Ha Hb. specialize (Ha 0%nat ltac:(lia)). specialize (Hb 0%nat ltac:(lia)).
rewrite Z.add_0_r in Ha, Hb. unfold aview. rewrite Ha, Hb. reflexivity.
Qed.
Lemma d3r_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
End m.
Lemma d3r_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma d3r_mrestrict_aview : forall segs H (m m' : word -> option byte),
  mrestrict H m' = mrestrict H m -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview. rewrite He. reflexivity. Qed.
Lemma d3r_vm_tr : forall segs (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs H m' (a + k) = aview segs H m (a + k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof. intros segs H m m' a n v Hk Hv. exact (val_mem_moved segs H H m m' a a n v Hk Hv). Qed.
Lemma d3r_shb_tr : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hb. exact (block_shadow_agree rd rd' Bs a n Hk Hb). Qed.

(* ---- the symbolic states ---------------------------------------------------------------------------------- *)
(* The shadow base (object 1's cell, read into a3 from mf+168) and the shadow map's span. *)
Definition SB_D : Z := 0x7fff8000.
Definition Bspan_D : Z * Z := (SB_D, SB_D + 2 ^ 44 - 1).
(* Run 1, +0x7b4 .. the bcmp call at +0x7c0. Region 0, base s1 (atom 9): mf+152 = &before and mf+184 = &id,
   both offsets of the frame's address (atom 32); read-only. *)
Definition d3r_mf1 : YP09.region := YP09.mkRegion (Some 9%nat) 152 192 152 152
  [YP09.mkChunk 152 (CVal 8 (SOff 32 32)); YP09.mkChunk 184 (CVal 8 (SOff 32 352))].
Definition ss_d3r1 : sstate := mkSS 0x7b4 sr_atoms [d3r_mf1] None (mkFacts [] [] []).

(* ---- the checks after the call: +0x7c4 .. the join +0xe24 --------------------------------------------- *)
(* Run 2 starts at the return (0x80f38) from a fresh symbolic state. Region 0, base s1: mf+168 = the shadow base
   (atom 32). Region 1, base s11 (the payload copy, atom 27): its first n bytes (n = 0, 2 or 4, as the case
   reads them), atoms 33..36. The facts fix a0 = 0 (the bcmp result), the record's address (s2, atom 18), its
   length (s6, atom 22) and the bytes to the case at hand, so that every branch of the run is decided and it goes
   straight to the join. *)
Definition PL_HI : Z := 0x7fffff800000.
Definition d3r_mf2 : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition d3r_plc : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0));
   YP09.mkChunk 2 (CVal 1 (SOff 35 0)); YP09.mkChunk 3 (CVal 1 (SOff 36 0))].
Definition d3r_pl (n : nat) : YP09.region := YP09.mkRegion (Some 27%nat) 0 (Z.of_nat n) 0 0 (firstn n d3r_plc).
Definition d3r_facts (alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3 : Z) : facts :=
  mkFacts [(10%nat, mkAF 0 0 0); (18%nat, mkAF alo ahi 0); (22%nat, mkAF klo khi 0); (27%nat, mkAF 4096 PL_HI 4);
    (32%nat, mkAF SB_D SB_D 0); (33%nat, mkAF l0 h0 0); (34%nat, mkAF l1 h1 0); (35%nat, mkAF l2 h2 0);
    (36%nat, mkAF l3 h3 0)] [] [].
Definition ss_d3r2 (n : nat) (alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3 : Z) : sstate :=
  mkSS 0x7c4 sr_atoms [d3r_mf2; d3r_pl n] None (d3r_facts alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3).
Definition d3r_xtra (pb : list byte) : list word :=
  map (Z_to_bv 64) [SB_D; RcIdentModel.bz (RcIdentModel.nthb pb 0); RcIdentModel.bz (RcIdentModel.nthb pb 1);
    RcIdentModel.bz (RcIdentModel.nthb pb 2); RcIdentModel.bz (RcIdentModel.nthb pb 3)].
Lemma d3r_nth_map : forall (pb : list byte) j, (j < length pb)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) pb) 0 = RcIdentModel.bz (RcIdentModel.nthb pb j).
Proof.
intros pb j Hj. unfold RcIdentModel.bz, RcIdentModel.nthb.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; exact Hj).
apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.
Ltac d3r_env_old := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The boundary file's Section c, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract file states it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- run 1 and the bcmp call: +0x7b4 .. the return at +0x7c4 ------------------------------------------- *)
(*   0x80f28 li a2,38; 0x80f2c ld a0,152(s1) (&before); 0x80f30 ld a1,184(s1) (&id); 0x80f34 jal to the bcmp
   wrapper. The run writes nothing. The wrapper compares the 38 bytes of `before` and `id`; both hold
   m_id i (the record is ignored, so ingest left the identity as it was), so a0 = 0 at the return. *)
Lemma d3r_call : forall g pos mf i W2 ly2 S2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) ->
  frames S2 = [(4, pos)] ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  mf_before g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 ->
  bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) ->
  bytes_at8 W2 mem2 (SFa g pos + V_id) (m_id g (S i)) ->
  sh_blk W2 mem2 (SFa g pos + V_id) N_id -> sh_blk W2 mem2 (SFa g pos + V_before) N_before ->
  m_id g (S i) = m_id g i ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x7b4) regs2 mem2 md2)
  (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
    c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x7c4)) mem3 (seg_rom SEGS)) md3 /\
    ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly2 S2 W2 mem3 md3 (4 * Z.of_nat i + 3) /\
    getr regs3 10 = w64 0 /\ aregs_preserved regs2 regs3 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
      aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a)).
Proof.
intros g pos mf i W2 ly2 S2 regs2 mem2 md2 HJ Hfrs Rsp Rs1 Hmfb Hmf32 Rgp Rtp Hmbef Hmid Hbef Hid Hshid Hshbef Hsame.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
rewrite EFa, HFB in HSF1, HSFapp. rewrite EFa in HSF0.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hmf1 : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hshi H47; lia).
unfold mf_before, V_before in Hmbef. unfold mf_id, V_id in Hmid.
unfold V_before, N_before in Hbef, Hshbef. unfold V_id, N_id in Hid, Hshid.
(* the environment: atom 32 = SF *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 SF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 SF]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 Hmf1 C1. lia. }
assert (HS : st_ok_pi SEGS VAL E ss_d3r1
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x7b4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_d3r1. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold d3r_mf1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf1; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 32 32) (SF + 32));
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia); reflexivity
      | clear - HSF0 HSF1 C1; lia | lia | exact Hmbef].
    + apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 352) (SF + 352));
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small by (clear - HSF0 HSF1 C1; lia); reflexivity
      | clear - HSF0 HSF1 C1; lia | lia | exact Hmid].
  - cbn. split; exact I.
  - unfold facts_ok. cbn. split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x7b4)) with (Z_to_bv 64 (BASE + 0x7b4)).
paj_run_tok RUN HS HJ SHOK Bspan_D; [awr_ok_tac|].
(* at the call: run 1 wrote nothing *)
assert (Hm : rd W2 (ms_mem ms) = rd W2 mem2) by exact (frame_of_read_only E (ss_mem ss_d3r1) _ _ eq_refl HFr).
pose proof (d3r_mrestrict_aview SEGS (w_H W2) mem2 (ms_mem ms) Hm) as HmA.
assert (Hrd : aview SEGS (w_H W2) (ms_mem ms) = aview SEGS (w_H W2) mem2) by (unfold aview; rewrite Hm; reflexivity).
pose proof (proj1 HJ) as HART.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
rewrite E32, unsigned_lit_small in Qa0, Qa1 by (clear - HSF0 HSF1 C1; lia).
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Qsp. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Qgp.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Qtp.
assert (Usp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Qsp; apply unsigned_lit_small; clear - Hmf0 Hmf1 C1; lia).
assert (HPR : aregs_preserved regs2 (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs2 [Z_to_bv 64 SF] HS); [exact AGE | vm_compute; reflexivity]. }
(* the bytes of `before` and `id`: equal, and present *)
assert (Hlen : length (map (fun b : byte => bv_unsigned b) (m_id g i)) = 38%nat)
  by (rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
unfold bytes_at8 in Hbef, Hid. rewrite Hsame in Hid.
assert (VB : forall j, 0 <= j < 38 -> exists v,
  val_mem SEGS (rd W2 mem2) (SF + 32 + j) 1 v /\ val_mem SEGS (rd W2 mem2) (SF + 352 + j) 1 v).
{ intros j Hj. destruct (Hbef (Z.to_nat j) ltac:(lia)) as [Va _]. destruct (Hid (Z.to_nat j) ltac:(lia)) as [Vb _].
  rewrite Z2Nat.id in Va, Vb by lia. eexists. split; [exact Va | exact Vb]. }
pmkst HS.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W2 (ms_regs ms) (ms_mem ms)
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 3)
    (SF + 32) (SF + 352) 38 (mf - sp0) (Z_to_bv 64 (BASE + 0x7c4)) HJ).
  - exact Qa0.
  - exact Qa1.
  - exact Qa2.
  - lia.
  - clear - HSF0. lia.
  - clear - HSF1 C1. lia.
  - clear - HSF0. lia.
  - clear - HSF1 C1. lia.
  - rewrite Usp. ring.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - rewrite HES. clear - Hmfb HSTK' Has. lia.
  - exact Qgp.
  - exact Qtp.
  - exact Qra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. rewrite Usp, HES. split; [|clear - Ha HSF1 Hmf0; lia].
    rewrite HmA. destruct (VB (a - (SF + 32)) ltac:(lia)) as (v & Va & _).
    replace (SF + 32 + (a - (SF + 32))) with a in Va by ring. exact (d3r_aview_some SEGS _ _ _ _ Va).
  - intros a Ha. rewrite Usp, HES. split; [|clear - Ha HSF1 Hmf0; lia].
    rewrite HmA. destruct (VB (a - (SF + 352)) ltac:(lia)) as (v & _ & Vb).
    replace (SF + 352 + (a - (SF + 352))) with a in Vb by ring. exact (d3r_aview_some SEGS _ _ _ _ Vb).
  - intros a Ha. rewrite HES. clear - Ha HSF1 Hmf0. lia.
  - intros a Ha. rewrite HES. clear - Ha HSF1 Hmf0. lia.
  - apply (amem_range_sub_app SF 1024 (SF + 32) 38 HSFapp HSF1); lia.
  - apply (amem_range_sub_app SF 1024 (SF + 352) 38 HSFapp HSF1); lia.
  - rewrite Hrd. apply (block_shadow_range _ SHADOW_OFF (SF + 32) 38); [exact Hshbef | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ 4 pos (SF + 32) 38 HART Hin4);
    rewrite ?EFa, ?HFB; lia.
  - rewrite Hrd. apply (block_shadow_range _ SHADOW_OFF (SF + 352) 38); [exact Hshid | lia | lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ 4 pos (SF + 352) 38 HART Hin4);
    rewrite ?EFa, ?HFB; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & _).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split.
{ rewrite Hv. apply Hcmp. intros j Hj. rewrite !HmA. destruct (VB j Hj) as (vj & Va & Vb).
  exact (d3r_aview_eq SEGS _ _ _ _ _ Va Vb). }
split; [exact (aregs_preserved_trans regs2 (ms_regs ms) regs3 HPR HP3)|].
intros a Ha Hna. rewrite (Hfr3 a Ha ltac:(clear - Hna; lia)). apply HmA.
Qed.

(* The fresh symbolic state at the return +0x7c4, for the case (n, the bounds) at hand. *)
Lemma d3r_entry2 : forall (W : world SEGS) ly S (regs : bvmap 5 word) (mem : word -> option byte) md mf pl k addr
  (pb : list byte) (n : nat) (alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3 : Z),
  AR SEGS B ly S W mem md -> In (pl, k) (ablocks B ly S) ->
  getr regs 9 = w64 mf -> getr regs 10 = w64 0 -> getr regs 18 = w64 addr -> getr regs 22 = w64 k ->
  getr regs 27 = w64 pl ->
  alloc_ceiling + 16384 <= mf -> mf + 320 <= 2 ^ 47 ->
  val_mem SEGS (rd W mem) (mf + 168) 8 SHADOW_OFF ->
  bytes_at8 W mem pl pb -> Z.of_nat (length pb) = k ->
  (n = 0 \/ n = 2 \/ n = 4)%nat -> Z.of_nat n <= k ->
  0 <= alo -> alo <= addr <= ahi -> ahi < 2 ^ 64 -> 0 <= klo -> klo <= k <= khi ->
  0 <= l0 -> l0 <= RcIdentModel.bz (RcIdentModel.nthb pb 0) <= h0 ->
  0 <= l1 -> l1 <= RcIdentModel.bz (RcIdentModel.nthb pb 1) <= h1 ->
  0 <= l2 -> l2 <= RcIdentModel.bz (RcIdentModel.nthb pb 2) <= h2 ->
  0 <= l3 -> l3 <= RcIdentModel.bz (RcIdentModel.nthb pb 3) <= h3 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (d3r_xtra pb))) (ss_d3r2 n alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x7c4)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) [mkSHE 27 0 (Z.of_nat n)] (Eimg (Ereg regs (d3r_xtra pb))) (rd W mem).
Proof.
intros W ly S regs mem md mf pl k addr pb n alo ahi klo khi l0 h0 l1 h1 l2 h2 l3 h3 HAR Hin R9 R10 R18 R22 R27
  Hmf0 Hmf1 V168 Hpb Hlen Hn Hnk Ha0 Ha Ha1 Hk0 Hk L0 B0 L1 B1 L2 B2 L3 B3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md pl k HAR Hin) as (H16 & H4096 & Hplce & _).
pose proof (req_size_pos k ltac:(lia)) as [Hrq1 Hrq2].
pose proof (SlotModel.bz_range (RcIdentModel.nthb pb 0)) as Z0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb pb 1)) as Z1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb pb 2)) as Z2.
pose proof (SlotModel.bz_range (RcIdentModel.nthb pb 3)) as Z3.
set (b0 := RcIdentModel.bz (RcIdentModel.nthb pb 0)) in *.
set (b1 := RcIdentModel.bz (RcIdentModel.nthb pb 1)) in *.
set (b2 := RcIdentModel.bz (RcIdentModel.nthb pb 2)) in *.
set (b3 := RcIdentModel.bz (RcIdentModel.nthb pb 3)) in *.
set (E := Eimg (Ereg regs (d3r_xtra pb))).
assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs (d3r_xtra pb)) nn)
  by (intros nn Hnn; apply Eimg_low; exact Hnn).
assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E nn) = v)
  by (intros nn v Hnn Hv; rewrite Hnn; apply unsigned_lit_small; exact Hv).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ apply VB; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9 | lia]. }
assert (U10 : bv_unsigned (ew E 10) = 0).
{ apply VB; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10 | lia]. }
assert (U18 : bv_unsigned (ew E 18) = addr).
{ apply VB; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18 | lia]. }
assert (U22 : bv_unsigned (ew E 22) = k).
{ apply VB; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22 | lia]. }
assert (E27 : ew E 27 = Z_to_bv 64 pl).
{ rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27. }
assert (U27 : bv_unsigned (ew E 27) = pl) by (apply VB; [exact E27 | lia]).
assert (E32 : ew E 32 = Z_to_bv 64 SB_D) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 b1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 b2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 b3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = SB_D) by (apply VB; [exact E32 | unfold SB_D; lia]).
assert (U33 : bv_unsigned (ew E 33) = b0) by (apply VB; [exact E33 | lia]).
assert (U34 : bv_unsigned (ew E 34) = b1) by (apply VB; [exact E34 | lia]).
assert (U35 : bv_unsigned (ew E 35) = b2) by (apply VB; [exact E35 | lia]).
assert (U36 : bv_unsigned (ew E 36) = b3) by (apply VB; [exact E36 | lia]).
(* the payload's first bytes, as the chunks state them *)
assert (VP : forall j, (j < n)%nat -> (n <= length pb)%nat ->
  val_mem SEGS (rd W mem) (pl + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb pb j))).
{ intros j Hj Hnl. unfold bytes_at8 in Hpb. destruct (Hpb j ltac:(rewrite length_map; lia)) as [Hv _].
  rewrite d3r_nth_map in Hv by lia. exact Hv. }
assert (Hnl : (n <= length pb)%nat) by lia.
assert (CK : forall j (e : sv) v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 -> (j < n)%nat ->
  RcIdentModel.bz (RcIdentModel.nthb pb j) = v ->
  YP09.chunk_ok SEGS E (rd W mem) pl (YP09.mkChunk (Z.of_nat j) (CVal 1 e))).
{ intros j e v He Hv Hj Hbv. apply (chunk_ok_val SEGS E _ pl (Z.of_nat j) 1 e v); [exact He | cbn; lia | lia |].
  rewrite <- Hbv. exact (VP j Hj Hnl). }
assert (DV : forall nn v, ew E nn = Z_to_bv 64 v -> sv_denot E (SOff nn 0) = Z_to_bv 64 v).
{ intros nn v Hnn. cbn [sv_denot]. rewrite Hnn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
- rewrite restrict_mkst_fx. unfold ss_d3r2. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + destruct Hn as [-> | [-> | ->]]; vm_compute; reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold d3r_mf2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SB_D); [exact (DV 32%nat SB_D E32) | unfold SB_D; cbn; lia | lia |].
      exact V168.
    * unfold d3r_pl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct Hn as [-> | [-> | ->]]; cbn [firstn d3r_plc];
      repeat apply Forall_cons; try apply Forall_nil.
      -- exact (CK 0%nat _ b0 (DV 33%nat b0 E33) ltac:(lia) ltac:(lia) eq_refl).
      -- exact (CK 1%nat _ b1 (DV 34%nat b1 E34) ltac:(lia) ltac:(lia) eq_refl).
      -- exact (CK 0%nat _ b0 (DV 33%nat b0 E33) ltac:(lia) ltac:(lia) eq_refl).
      -- exact (CK 1%nat _ b1 (DV 34%nat b1 E34) ltac:(lia) ltac:(lia) eq_refl).
      -- exact (CK 2%nat _ b2 (DV 35%nat b2 E35) ltac:(lia) ltac:(lia) eq_refl).
      -- exact (CK 3%nat _ b3 (DV 36%nat b3 E36) ltac:(lia) ltac:(lia) eq_refl).
  + apply pairwise_disjoint_of_extents. unfold d3r_mf2, d3r_pl, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    unfold d3r_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U18, U22, U27, U32, U33, U34, U35, U36.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold PL_HI, SB_D. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor; [|constructor].
  apply (shent_ok_of_block SEGS B LAWS ly S W mem md E (SOff 32 0) 27 pl k 0 (Z.of_nat n) HAR Hin).
  + rewrite (U_atom E 32 SB_D E32) by (unfold SB_D; lia). reflexivity.
  + exact (U_atom E 27 pl E27 ltac:(lia)).
  + lia.
  + lia.
Qed.

(* The registers the join's boundary reads (ecommon: sp, gp, tp, s0, s1; P_body: s6, s11). x18 is pinned to the
   record's address in run 2, so it is not in the list. *)
Definition d3r_kept : list (bv 5) := [2; 3; 4; 8; 9; 22; 27]%bv.
(* The join, at the end of a case's run: the post of d3r_rest from the final symbolic state. *)
Ltac d3r_fin AGE :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msc), HFr : frame_of _ ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
  apply SRr_ret; split; [reflexivity|];
  pmkst HS;
  exists (ms_regs msc), (ms_mem msc); eexists;
  split; [reflexivity|];
  split; [eassumption|];
  split; [eapply (regs_kept_of_st_ok_pi _ _ _ _ _ d3r_kept HS);
          [ split; [intros nn Hnn; d3r_env_old; exact (proj1 AGE nn Hnn) | cbn [ed ewset]; exact (proj2 AGE)]
          | vm_compute; reflexivity ] |];
  etransitivity; [exact (frame_of_read_only _ rs _ _ eq_refl HFr) | first [reflexivity | eassumption]]
  end.
(* A case's run: from the fresh state at +0x7c4 straight to the join. *)
Ltac d3r_go RUNTO HS SHOK HJ AGE :=
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_D 0xe24; [awr_ok_tac | d3r_fin AGE].

(* Run 2, +0x7c4 .. +0xe24: the checks of an ignored record. 0x80f38 loads the shadow base, 0x80f3c takes the
   bcmp result 0; then by the record's address: the firmware case (s2 = 0, 0x80f44) reads up to four payload
   bytes, each after its instrumented check and its UBSan pointer checks, and leaves at the first byte above 9
   (0x80f70, 0x80f9c, 0x80fc8, 0x80ff4), or at 0x8154c when the length is below 4; 0x8154c checks the version
   case (s2 = 1536, length above 7 aborts); 0x81560 the model-name case (s2 = 4096, length 2 or more: the byte
   pl[1] must be 0, 0x8158c). An ignored record never takes the aborting side (d3r_fw, d3r_ver, d3r_name). The
   case fixes a0 = 0 and the record's address as literals (st_ok_pi_pin_reg') and bounds the length and the
   bytes in the facts, so the run decides every branch and goes straight to 0x81598; only the model-name byte
   test (0x81590) is taken by hand. *)
Lemma d3r_rest : forall STK sp0 ly0 S0 W0 mem0 md0 own kk (inp : list byte) i mf pl (W : world SEGS) ly S
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3,
  ajournal SEGS B STK sp0 [] ly0 S0 W0 mem0 md0 own ly S W mem3 md3 kk ->
  getr regs3 9 = w64 mf -> getr regs3 10 = w64 0 ->
  getr regs3 18 = w64 (SlotModel.rec_addr inp i) ->
  getr regs3 22 = w64 (SlotModel.rec_k inp i) -> getr regs3 27 = w64 pl ->
  alloc_ceiling + 16384 <= mf -> mf + 320 <= 2 ^ 47 ->
  val_mem SEGS (rd W mem3) (mf + 168) 8 SHADOW_OFF ->
  In (pl, SlotModel.rec_k inp i) (ablocks B ly S) ->
  bytes_at8 W mem3 pl (SlotModel.rec_pl inp i) ->
  SlotModel.rec_r inp i = 0 ->
  SRr SEGS W (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0x7c4)) mem3 (seg_rom SEGS)) md3)
  (fun W4 c4 => W4 = W /\ exists regs4 mem4 md4, c4 = cfg_at SEGS (BASE + 0xe24) regs4 mem4 md4 /\
    ajournal SEGS B STK sp0 [] ly0 S0 W0 mem0 md0 own ly S W mem4 md4 kk /\
    (forall r, In r d3r_kept -> getr regs4 r = getr regs3 r) /\ rd W mem4 = rd W mem3).
Proof.
intros STK sp0 ly0 S0 W0 mem0 md0 own kk inp i mf pl W ly S regs3 mem3 md3 HJ R9 R10 R18 R22 R27 Hmf0 Hmf1 V168
  Hinpl Hpl Hr0.
pose proof (proj1 HJ) as HAR.
pose proof (SlotModel.rec_pl_length inp i) as Hlen.
pose proof (SlotModel.rec_k_range inp i) as Hkr.
pose proof (d3r_addr_cases inp i) as Hac.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 0)) as Z0.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1)) as Z1.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2)) as Z2.
pose proof (SlotModel.bz_range (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3)) as Z3.
assert (Hlen' : Z.of_nat (length (SlotModel.rec_pl inp i)) = SlotModel.rec_k inp i) by (rewrite Hlen; lia).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 (d3r_xtra (SlotModel.rec_pl inp i))))) by apply Eimg_env.
assert (AGE : env_agree 32 (Ereg regs3 (d3r_xtra (SlotModel.rec_pl inp i)))
  (Eimg (Ereg regs3 (d3r_xtra (SlotModel.rec_pl inp i)))))
  by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
destruct Hac as [Ha | [Ha | [Ha | Ha]]].
- (* the firmware address *)
  assert (R18z : getr regs3 18 = Z_to_bv 64 0) by (rewrite R18, Ha; reflexivity).
  destruct (Z_lt_le_dec (SlotModel.rec_k inp i) 4) as [Hk | Hk].
  + (* fewer than four bytes: on to 0x8154c *)
    destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
      (SlotModel.rec_pl inp i) 0 0 0 0 3 0 255 0 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
      V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
    pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
    pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS1 R18z eq_refl) as HS. clear HS1.
    d3r_go RUNTO HS SHOK HJ AGE.
  + destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 0)) 9) as [Hb0 | Hb0].
    * destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 1)) 9) as [Hb1 | Hb1].
      -- destruct (Z_le_gt_dec (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2)) 9) as [Hb2 | Hb2].
         ++ (* the first three bytes are digits: the fourth is not (d3r_fw), 0x80ff4 *)
            pose proof (d3r_fw inp i Hr0 Ha Hk Hb0 Hb1 Hb2) as Hb3.
            destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
              (SlotModel.rec_pl inp i) 4 0 0 4 255 0 9 0 9 0 9 10 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
              V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
            pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
            pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS1 R18z eq_refl) as HS. clear HS1.
            d3r_go RUNTO HS SHOK HJ AGE.
         ++ (* the third byte is above 9: 0x80fc8 *)
            destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
              (SlotModel.rec_pl inp i) 4 0 0 4 255 0 9 0 9 10 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
              V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
            pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
            pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS1 R18z eq_refl) as HS. clear HS1.
            d3r_go RUNTO HS SHOK HJ AGE.
      -- (* the second byte is above 9: 0x80f9c *)
         destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
           (SlotModel.rec_pl inp i) 4 0 0 4 255 0 9 10 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
           V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
         pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
         pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS1 R18z eq_refl) as HS. clear HS1.
         d3r_go RUNTO HS SHOK HJ AGE.
    * (* the first byte is above 9: 0x80f70 *)
      destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
        (SlotModel.rec_pl inp i) 4 0 0 4 255 10 255 0 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
        V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
      pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
      pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS1 R18z eq_refl) as HS. clear HS1.
      d3r_go RUNTO HS SHOK HJ AGE.
- (* the REAC-version address: fewer than eight bytes (d3r_ver) *)
  assert (R18z : getr regs3 18 = Z_to_bv 64 1536) by (rewrite R18, Ha; reflexivity).
  pose proof (d3r_ver inp i Hr0 Ha) as Hk.
  destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
    (SlotModel.rec_pl inp i) 0 1536 1536 0 7 0 255 0 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
    V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
  pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 1536 HS1 R18z eq_refl) as HS. clear HS1.
  d3r_go RUNTO HS SHOK HJ AGE.
- (* the model-name address *)
  assert (R18z : getr regs3 18 = Z_to_bv 64 4096) by (rewrite R18, Ha; reflexivity).
  destruct (Z_lt_le_dec (SlotModel.rec_k inp i) 2) as [Hk | Hk].
  + destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
      (SlotModel.rec_pl inp i) 0 4096 4096 0 1 0 255 0 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
      V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
    pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
    pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 4096 HS1 R18z eq_refl) as HS. clear HS1.
    d3r_go RUNTO HS SHOK HJ AGE.
  + (* two bytes or more: the first name byte is 0 (d3r_name) *)
    pose proof (d3r_name inp i Hr0 Ha Hk) as Hb1.
    destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
      (SlotModel.rec_pl inp i) 2 4096 4096 2 255 0 255 0 0 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
      V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
    pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS1. clear HS0.
    pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 4096 HS1 R18z eq_refl) as HS. clear HS1.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_D 0xe24; [awr_ok_tac|].
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
      pose proof (frame_of_read_only _ rs _ _ eq_refl HFr) as Hm1; clear HFr end.
    psrr_branch_tok RUNTO BR HS SHOK Bspan_D.
    * d3r_go RUNTO HS SHOK HJ AGE.
    * exfalso. rewrite branch_eq_U in Hc.
      lazymatch type of Hc with (U ?Ev (SOff 34 0) =? _) = false =>
        rewrite (U_atom Ev 34 0) in Hc; [discriminate Hc | | lia] end.
      d3r_env_old. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_extra regs3 _ 2). cbn [d3r_xtra map nth]. rewrite Hb1. reflexivity.
- (* any other address: no check applies *)
  destruct (d3r_entry2 W ly S regs3 mem3 md3 mf pl (SlotModel.rec_k inp i) (SlotModel.rec_addr inp i)
    (SlotModel.rec_pl inp i) 0 49152 65535 0 255 0 255 0 255 0 255 0 255 HAR Hinpl R9 R10 R18 R22 R27 Hmf0 Hmf1
    V168 Hpl Hlen') as [HS0 SHOK]; [lia .. |].
  pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS0 R10 eq_refl) as HS. clear HS0.
  d3r_go RUNTO HS SHOK HJ AGE.
Qed.

(* ---- seg_D3r: inv_ignored -> inv_tail ------------------------------------------------------------------ *)
(* The two runs chain (d3r_call then d3r_rest). Neither allocates, frees or stores outside the bcmp wrapper's
   own window [mf - 2*ESTACK, mf), so the journal's state S2, the meter and every byte of the side-stack frame,
   the machine frame and the heap are unchanged; inv_tail's facts are inv_ignored's, re-stated at the final
   state (the registers from the kept-register list, the memory facts transported across the window). The
   harness's hw record and the id are unchanged because the record is ignored (d3r_hw_same, d3r_id_same). *)
Ltac vunf := unfold V_before, N_before, V_again, N_again, V_s, V_v, V_ev, V_id, N_id, V_hw, N_hw,
  V_f, N_f, V_ef, N_ef, SHADOW_OFF in *.
Ltac acs := unfold acallee_saved; repeat first [ left; reflexivity | right ];
  try (match goal with |- _ <= ?x <= _ => let v := eval vm_compute in x in change x with v end; lia).
Ltac inkept := cbv [In d3r_kept]; repeat first [ left; reflexivity | right ].
Ltac tv AWh Hbdh H := eapply d3r_vm_tr;
  [ let kk := fresh "kk" in let Hkk := fresh "Hkk" in intros kk Hkk; apply AWh;
      [ clear - Hbdh Hkk; vunf; lia | clear - Hbdh Hkk; vunf; lia ] | exact H ].
Ltac tg AWh Hbdh H Lh := unfold bytes_at8; eapply d3r_garr8_moved;
  [ let kk := fresh "kk" in let Hkk := fresh "Hkk" in intros kk Hkk; rewrite length_map in Hkk; apply AWh;
      [ clear - Hbdh Hkk Lh; vunf; lia | clear - Hbdh Hkk Lh; vunf; lia ] | exact H ].
Ltac tz AWh Hbdh H := unfold sh_zero; eapply d3r_zero_shadow_moved;
  [ let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii; unfold shadow_of_addr; apply AWh;
      [ clear - Hbdh Hii; vunf; lia | clear - Hbdh Hii; vunf; lia ] | exact H ].
Ltac tb AWh Hbdh H := unfold sh_blk; eapply d3r_shb_tr;
  [ let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii; unfold shadow_of_addr; apply AWh;
      [ clear - Hbdh Hii; vunf; lia | clear - Hbdh Hii; vunf; lia ] | exact H ].
Lemma seg_D3r : seg_D3r_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i pl W2 c2 Hst.
destruct Hst as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (HPB & Hhw & Hr0 & Hbef & Hshbef & R18).
unfold P_body in HPB.
destruct HPB as (Hi & Hbl & Hpl & Hid & V96n & Hfix & Hmbef & Hmag & Hmid & V112 & V120 & V128 & R22 & R27 & Hcur).
unfold id_at in Hid. destruct Hid as (Hidb & Hidz & Hidsh).
unfold hw_live, hw_mem in Hhw. destruct Hhw as (Hhwm & Hhw0 & Hhw24). destruct Hhwm as (Hhwb2 & Hhwz & Hhwsh).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. change (fs_frame_bytes 4) with 1024 in HSF1.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hmf1 : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hshi H47; lia).
assert (Hinpl : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Hpllen.
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkrge.
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as (Hrq1 & Hrq2).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl (SlotModel.rec_k (e_pl g) i) HAR2 Hinpl)
  as (_ & Hpl4096 & Hplce & _).
assert (Hplb : pl + Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) <= alloc_ceiling)
  by (rewrite Hpllen, Z2Nat.id by lia; clear - Hplce Hrq2; lia).
assert (HidlenS : Z.of_nat (length (m_id g (S i))) = 38)
  by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Hidleni : Z.of_nat (length (m_id g i)) = 38)
  by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Hhwblen : Z.of_nat (length (m_hwb g i)) = 8) by (unfold m_hwb; rewrite d3r_hwb_len; reflexivity).
assert (Hbd : 140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling + 16384 <= mf /\
  mf + 320 <= sp0 /\ sp0 <= mf + 336 /\ sp0 <= 2 ^ 47 /\ 4096 <= SF /\ SF + 1024 <= alloc_ceiling /\
  4096 <= pl /\ pl + Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) <= alloc_ceiling /\ ESTACK = 4096)
  by (clear - C1 Hmf0 Hmfb Hshi H47 HSF0 HSF1 Hpl4096 Hplb HES; unfold sp0 in *; repeat split; lia).
assert (Hsame : m_id g (S i) = m_id g i) by (unfold m_id; apply d3r_id_same; exact Hr0).
assert (Hhwb : m_hwb g (S i) = m_hwb g i)
  by (unfold m_hwb, SlotModel.rec_hwb; rewrite (d3r_hw_same (e_pl g) i Hr0); reflexivity).
assert (Hhave : m_have g (S i) = m_have g i)
  by (unfold m_have, SlotModel.rec_have; rewrite (d3r_hw_same (e_pl g) i Hr0); reflexivity).
(* ---- run 1 and the bcmp call ------------------------------------------------------------------------- *)
eapply SRr_bind.
{ apply (d3r_call g pos mf i W2 ly2 S2 regs2 mem2 md2 HJ Hfrs R2 R9 Hmfb Hmf32 R3 R4 Hmbef Hmid
    Hbef Hidb Hidsh Hshbef Hsame). }
cbv beta. intros Wa ca Hwle (-> & regs3 & mem3 & md3 & -> & HJ3 & R10c & HPR & KEEP3).
assert (KR3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r).
{ intros r Hr. pose proof (HPR (bv_unsigned r) Hr) as Hp. rewrite Z_to_bv_bv_unsigned in Hp. exact Hp. }
assert (R9b : getr regs3 9 = w64 mf) by (rewrite (KR3 9%bv ltac:(acs)); exact R9).
assert (R18b : getr regs3 18 = w64 (SlotModel.rec_addr (e_pl g) i)) by (rewrite (KR3 18%bv ltac:(acs)); exact R18).
assert (R22b : getr regs3 22 = w64 (SlotModel.rec_k (e_pl g) i)) by (rewrite (KR3 22%bv ltac:(acs)); exact R22).
assert (R27b : getr regs3 27 = w64 pl) by (rewrite (KR3 27%bv ltac:(acs)); exact R27).
assert (V168b : val_mem SEGS (rd W2 mem3) (mf + 168) 8 SHADOW_OFF).
{ eapply (d3r_vm_tr SEGS (w_H W2) mem2 mem3); [intros kk Hkk; apply KEEP3;
    [clear - Hbd Hkk; lia | clear - Hbd Hkk; lia] | exact V168]. }
assert (Hpl3 : bytes_at8 W2 mem3 pl (SlotModel.rec_pl (e_pl g) i)).
{ unfold bytes_at8 in Hpl |- *. eapply (d3r_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3); [| exact Hpl].
  intros kk Hkk. rewrite length_map in Hkk. apply KEEP3; [clear - Hbd Hplb Hkk; lia | clear - Hbd Hplb Hkk; lia]. }
eapply SRr_bind.
{ apply (d3r_rest LLVMF_STK sp0 (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] (4 * Z.of_nat i + 3)
    (e_pl g) i mf pl W2 ly2 S2 regs3 mem3 md3 HJ3 R9b R10c R18b R22b R27b
    ltac:(clear - Hmf0; lia) ltac:(clear - Hmf1; lia) V168b Hinpl Hpl3 Hr0). }
cbv beta. intros Wb cb Hwle2 (-> & regs4 & mem4 & md4 & -> & HJ4 & Hkept & Hmem43).
assert (AW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite <- (KEEP3 a Ha Hw).
  exact (d3r_mrestrict_aview SEGS (w_H W2) mem3 mem4 Hmem43 a). }
assert (KR4 : forall r : bv 5, In r d3r_kept -> acallee_saved (bv_unsigned r) -> getr regs4 r = getr regs2 r).
{ intros r Hin Hr. rewrite (Hkept r Hin). exact (KR3 r Hr). }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [Hfdeq Hfseq].
assert (K2 : getr regs4 2 = w64 mf) by (rewrite (KR4 2%bv ltac:(inkept) ltac:(acs)); exact R2).
assert (K9 : getr regs4 9 = w64 mf) by (rewrite (KR4 9%bv ltac:(inkept) ltac:(acs)); exact R9).
assert (K8 : getr regs4 8 = w64 sp0) by (rewrite (KR4 8%bv ltac:(inkept) ltac:(acs)); exact R8).
assert (K3 : getr regs4 3 = w64 (as_gp B)) by (rewrite (KR4 3%bv ltac:(inkept) ltac:(acs)); exact R3).
assert (K4 : getr regs4 4 = w64 (as_tp B)) by (rewrite (KR4 4%bv ltac:(inkept) ltac:(acs)); exact R4).
assert (K22 : getr regs4 22 = w64 (SlotModel.rec_k (e_pl g) i)) by (rewrite (KR4 22%bv ltac:(inkept) ltac:(acs)); exact R22).
assert (K27 : getr regs4 27 = w64 pl) by (rewrite (KR4 27%bv ltac:(inkept) ltac:(acs)); exact R27).
(* the input block's byte addresses are off the window *)
assert (Hpb : forall kk, 0 <= kk < Z.of_nat (length (e_pl g)) ->
  0 <= e_p g + kk < 2 ^ 64 /\ ~ (mf - 2 * ESTACK <= e_p g + kk < mf)).
{ intros kk Hkk. pose proof HPRE as HP'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HP'.
  destruct HP' as (_ & _ & _ & _ & Hnp & Hnlen & _). rewrite <- Hnlen in Hkk.
  destruct Hnp as [[Hn0 _] | [Hnn Hine]]; [clear - Hkk Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hce & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hr). clear - Hkk Hp4096 Hce Hr Hmf0 Hbd. lia. }
assert (Hinb4 : bytes_at8 W2 mem4 (e_p g) (e_pl g)).
{ unfold bytes_at8 in Hinb |- *. eapply (d3r_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem4); [| exact Hinb].
  intros kk Hkk. rewrite length_map in Hkk. destruct (Hpb kk Hkk) as [Ha Hw]. apply AW; [exact Ha | exact Hw]. }
(* ---- build inv_tail (every fact transported off the bcmp window) -------------------------------------- *)
(* ---- build inv_tail ---------------------------------------------------------------------------------- *)
apply SRr_ret. unfold inv_tail, acut.
exists ly2, S2, regs4, mem4, md4.
split; [reflexivity|].
split; [exact HJ4|].
split; [exact Hfrs|].
split; [exact Hk|].
split; [exact MLE|].
split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact K2|]. split; [exact K9|]. split; [exact K8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact K3|]. split; [exact K4|].
  split; [tv AW Hbd V16|]. split; [tv AW Hbd V64|]. split; [tv AW Hbd V192|]. split; [tv AW Hbd V168|].
  split; [tv AW Hbd Vra|]. split; [tv AW Hbd Vs0|].
  split; [tv AW Hbd W24|]. split; [tv AW Hbd W32|]. split; [tv AW Hbd W40|]. split; [tv AW Hbd W48|]. split; [tv AW Hbd W56|].
  split; [tv AW Hbd W64|]. split; [tv AW Hbd W72|]. split; [tv AW Hbd W80|]. split; [tv AW Hbd W88|]. split; [tv AW Hbd W96|].
  split; [tv AW Hbd W104|]. split; [tv AW Hbd Vflag|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Hfdeq; reflexivity|].
  split; [exact Hfseq|]. exact Hinb4. }
unfold P_body, hw_live, hw_mem, id_at. change (SFa g pos) with SF.
rewrite Hhwb, Hhave.
split.
{ split; [exact Hi|]. split; [exact Hbl|]. split; [tg AW Hbd Hpl Hplb|].
  split; [split; [tg AW Hbd Hidb HidlenS | split; [tz AW Hbd Hidz | tb AW Hbd Hidsh]]|].
  split; [tv AW Hbd V96n|].
  split; [unfold mf_fixed; change (SFa g pos) with SF;
          destruct Hfix as (A32 & A48 & A56 & A72 & A80 & A88 & A104 & A136 & A144 & A160);
          split; [tv AW Hbd A32|]; split; [tv AW Hbd A48|]; split; [tv AW Hbd A56|]; split; [tv AW Hbd A72|];
          split; [tv AW Hbd A80|]; split; [tv AW Hbd A88|]; split; [tv AW Hbd A104|]; split; [tv AW Hbd A136|];
          split; [tv AW Hbd A144|]; tv AW Hbd A160 |].
  split; [unfold mf_before; change (SFa g pos) with SF; tv AW Hbd Hmbef|].
  split; [unfold mf_again; change (SFa g pos) with SF; tv AW Hbd Hmag|].
  split; [unfold mf_id; change (SFa g pos) with SF; tv AW Hbd Hmid|].
  split; [tv AW Hbd V112|]. split; [tv AW Hbd V120|]. split; [tv AW Hbd V128|].
  split; [exact K22|]. split; [exact K27|]. exact Hcur. }
split; [split; [tg AW Hbd Hhwb2 Hhwblen | split; [tz AW Hbd Hhwz | tb AW Hbd Hhwsh]]|].
split; [tv AW Hbd Hhw0|]. tv AW Hbd Hhw24.
Qed.
Check (seg_D3r : seg_D3r_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
