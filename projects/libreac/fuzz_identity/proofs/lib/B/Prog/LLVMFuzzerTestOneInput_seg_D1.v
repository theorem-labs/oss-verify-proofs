(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* probe: the header run of seg_D1, +0x440 .. the malloc call +0x51c *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0a YO0b YO0c YK0w YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec
reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the record's address is a 16-bit field, or one of the three named addresses *)
Lemma d1_addr_range : forall inp i, 0 <= SlotModel.rec_addr inp i < 65536.
Proof.
intros inp i.
unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi,
SlotModel.pick, RcIdentModel.ADDR_FIRMWARE, RcIdentModel.ADDR_REAC_VERSION, RcIdentModel.ADDR_MODEL_NAME.
pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i)).
pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i + 1)).
repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.
(* what the second ingest call computes: the same record step the model takes *)
Lemma d1_ing_model : forall inp i (id p : Z), id <> 0 -> p <> 0 ->
  reac_identity_ingest_c.ingest_refused id p (SlotModel.rec_k inp i) = false /\
  reac_identity_ingest_c.ingest_ret id (SlotModel.rec_addr inp i) p (SlotModel.rec_k inp i)
    (SlotModel.rec_id inp i) (SlotModel.rec_pl inp i) = SlotModel.rec_r inp i /\
  snd (RcIdentModel.ING (SlotModel.rec_id inp i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i))
    = SlotModel.rec_id inp (S i).
Proof.
intros inp i id p Hid Hp.
assert (Hrf : reac_identity_ingest_c.ingest_refused id p (SlotModel.rec_k inp i) = false).
{ unfold reac_identity_ingest_c.ingest_refused.
  rewrite (proj2 (Z.eqb_neq id 0) Hid), (proj2 (Z.eqb_neq p 0) Hp).
  rewrite Bool.andb_false_r. reflexivity. }
split; [exact Hrf|].
split; [unfold reac_identity_ingest_c.ingest_ret; rewrite Hrf; reflexivity|].
reflexivity.
Qed.
(* the `hw` byte window is always eight bytes long *)
Lemma d1_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION)
            && (8 <=? SlotModel.rec_k inp i))%bool eqn:Hc; [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.

Section hfree.
Variable segs : list Segment.
Lemma d1_le1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma d1_mb : forall (m : word -> option byte) a (l : list byte),
  garr8 segs m a (map (fun b : byte => bv_unsigned b) l) -> mbytes_at segs m a l.
Proof.
intros m a l Hg j Hj.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) l))%nat) by (rewrite length_map; exact Hj).
destruct (Hg j Hj') as [Hv _].
pose proof (Hv 0%nat ltac:(lia)) as Hm. rewrite Z.add_0_r in Hm. rewrite Hm.
rewrite (nth_error_nth' l (RcIdentModel.zb 0) Hj). f_equal.
replace (nth j (map (fun b : byte => bv_unsigned b) l) 0) with (bv_unsigned (nth j l (RcIdentModel.zb 0)))
  by (symmetry; apply (map_nth (fun b : byte => bv_unsigned b) l (RcIdentModel.zb 0) j)).
rewrite d1_le1
  by (pose proof (bv_unsigned_in_range 8 (nth j l (RcIdentModel.zb 0))) as Hrg;
      change (bv_modulus 8) with 256 in Hrg; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma d1_gb : forall (m : word -> option byte) a (l : list byte),
  mbytes_at segs m a l -> garr8 segs m a (map (fun b : byte => bv_unsigned b) l).
Proof.
intros m a l Hm j Hj. rewrite length_map in Hj.
assert (Eb : nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (RcIdentModel.zb 0)))
  by (apply (map_nth (fun b : byte => bv_unsigned b) l (RcIdentModel.zb 0) j)).
pose proof (bv_unsigned_in_range 8 (nth j l (RcIdentModel.zb 0))) as Hrg.
change (bv_modulus 8) with 256 in Hrg.
split; [|rewrite Eb; lia].
intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk.
rewrite Z.add_0_r. rewrite (Hm j Hj). rewrite (nth_error_nth' l (RcIdentModel.zb 0) Hj).
f_equal. rewrite Eb. rewrite d1_le1 by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma d1_shoff : forall x v, x mod 8 = 0 -> v mod 8 = 0 ->
  shadow_of_addr SHADOW_OFF (x + v) = shadow_of_addr SHADOW_OFF x + v / 8.
Proof.
intros x v Hx Hv. unfold shadow_of_addr.
assert (E : x + v = (x / 8 + v / 8) * 8).
{ pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod v 8 ltac:(lia)). lia. }
rewrite E, Z.div_mul by lia. lia.
Qed.
Lemma d1_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma d1_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
End hfree.

Definition d1_B255 : afact := mkAF 0 255 0.
Definition d1_in (n : nat) : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0 (Z.of_nat n) 0 0
    (firstn n [YP09.mkChunk 0 (CVal 1 (SOff 33 0));
               YP09.mkChunk 1 (CVal 1 (SOff 34 0));
               YP09.mkChunk 2 (CVal 1 (SOff 35 0))]).
Definition d1_mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 112 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition d1_hdr_ss (n : nat) (f24 f34 : afact) (al : list (sv * sv)) : sstate :=
  mkSS 0x440 sr_atoms [d1_mf; d1_in n] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
              (15%nat, mkAF 1 1 0); (24%nat, f24); (25%nat, PTR 0); (32%nat, mkAF SB SB 0);
              (33%nat, d1_B255); (34%nat, f34); (35%nat, d1_B255)] [] al).
Definition d1_hdr_SH (n : nat) : list shent :=
  match n with O => [] | _ => [mkSHE 25 0 (Z.of_nat n)] end.

Lemma d1_byte : forall (segs : list Segment) mem a (l : list byte) (j : Z),
  garr8 segs mem a (map (fun b : byte => bv_unsigned b) l) -> 0 <= j < Z.of_nat (length l) ->
  val_mem segs mem (a + j) 1 (SlotModel.inb l j).
Proof.
intros segs mem a l j Hg Hj.
destruct (Hg (Z.to_nat j) ltac:(rewrite length_map; lia)) as [Hv _].
rewrite Z2Nat.id in Hv by lia.
replace (SlotModel.inb l j) with (nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) l) 0); [exact Hv|].
unfold SlotModel.inb, RcIdentModel.bz, RcIdentModel.nthb.
apply (map_nth (fun b : byte => bv_unsigned b) l (RcIdentModel.zb 0) (Z.to_nat j)).
Qed.
Lemma d1_srl6 : forall x : Z, 0 <= x < 2 ^ 64 ->
  alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 6) = Z_to_bv 64 (x / 64).
Proof.
intros x Hx. apply bv_eq. rewrite YO0c.alu64_srl.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small 6) by lia.
change (6 mod 64) with 6. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
rewrite unsigned_lit_small; [reflexivity|].
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma d1_or8 : forall hi lo : Z, 0 <= hi < 256 -> 0 <= lo < 256 ->
  alu64 ALU_OR (alu64 ALU_SLL (Z_to_bv 64 hi) (Z_to_bv 64 8)) (Z_to_bv 64 lo) = Z_to_bv 64 (lo + 256 * hi).
Proof.
intros hi lo Hhi Hlo. apply bv_eq. rewrite YO0c.alu64_or, YO0c.alu64_sll.
rewrite !(unsigned_lit_small hi) by lia. rewrite !(unsigned_lit_small lo) by lia.
rewrite (unsigned_lit_small 8) by lia. change (8 mod 64) with 8.
unfold YO0a.sll64. rewrite (Z.mod_small (Z.shiftl hi 8))
  by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
rewrite Z.lor_comm, YK0w.lor_shiftl8 by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma d1_inb_past : forall (l : list byte) (j : Z), Z.of_nat (length l) <= j -> SlotModel.inb l j = 0.
Proof.
intros l j Hj. unfold SlotModel.inb, RcIdentModel.bz, RcIdentModel.nthb.
rewrite nth_overflow by lia. reflexivity.
Qed.


Definition d1_mfw : YP09.region :=
  YP09.mkRegion (Some 9%nat) 112 176 112 136 [].
Definition d1_st_ss : sstate :=
  mkSS 0x4f0 sr_atoms [d1_mfw] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
              (14%nat, mkAF 0 64 0); (20%nat, PTR 0); (22%nat, mkAF 0 255 0);
              (24%nat, mkAF 0 (2 ^ 26) 0); (25%nat, PTR 0)] [] []).


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
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis MTL : ameter_laws MT.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IB___asan_memcpy).
Hypothesis HING : reac_identity_ingest.treac_identity_ingest_spec B.
Hypothesis HBUF : buf_of.tbuf_of_spec B MT (CTX_BUF_OF RA_LLVMF).
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INVREC := (inv_rec B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

#[local] Notation INVD1END := (inv_D1_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* ---- the cuts of seg_D1 (one per call / per merge), all with the same journal shape ------------------ *)
(* What every cut of the body keeps: the four machine-frame pointers and the record count. *)
Definition d1_stab (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 96) 8 (SlotModel.nrec (e_pl g)) /\
mf_fixed g pos mf W2 mem2 /\ mf_before g pos mf W2 mem2 /\ mf_again g pos mf W2 mem2 /\
mf_id g pos mf W2 mem2.


(* +0x4f0 (0x80c64): the header is read; the four paths of the record header merge here. No byte is
   written yet. x18 = the record's address, x19 is about to be computed, x20 = p + body, x22 = k,
   x24 = Lp, x25 = p + c, x13 = the shadow base, x14 = i, x15 = 1. *)
Definition d1_M (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i) (BASE + 0x4f0)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (e_p g + SlotModel.rec_body (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 24 = w64 (SlotModel.rec_Lp (e_pl g) i) /\
getr regs2 25 = w64 (e_p g + m_cur g i) /\
getr regs2 14 = w64 (Z.of_nat i) /\ getr regs2 15 = w64 1 /\
sh_reg g pos regs2 /\ d1_stab g pos mf W2 mem2 /\
id_at g pos i W2 mem2 /\ hw_live g pos mf i W2 mem2 /\ hblocks B g ly2 S2 []).

(* +0x51c (0x80c90): the malloc call of the payload copy. mf+120 = Lp and mf+128 = i are stored. *)
Definition d1_C1 (g : ectx) (pos mf : Z) (i : nat) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i) (BASE + 0x51c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\
getr regs2 10 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 19 = w64 (e_p g + m_cur g (S i)) /\
getr regs2 20 = w64 (e_p g + SlotModel.rec_body (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 25 = w64 (e_p g + m_cur g i) /\
sh_reg g pos regs2 /\ d1_stab g pos mf W2 mem2 /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
id_at g pos i W2 mem2 /\ hw_live g pos mf i W2 mem2 /\ hblocks B g ly2 S2 []).

(* what the body carries from the payload copy on: the block, its bytes and the three stores *)
Definition d1_pl (g : ectx) (pos mf : Z) (i : nat) (pl : Z)
(ly2 : alayout) (S2 : astate) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
hblocks B g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (e_p g + m_cur g (S i)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
d1_stab g pos mf W2 mem2.

(* +0x548 (0x80cbc): the payload copy is made and filled, mf+112 holds the next cursor. x27 = pl. *)
Definition d1_C2 (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 1) (BASE + 0x548)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ d1_pl g pos mf i pl ly2 S2 W2 mem2 /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 27 = w64 pl /\
sh_reg g pos regs2 /\ id_at g pos i W2 mem2 /\ hw_live g pos mf i W2 mem2).

(* +0x584 (0x80cf8): the first reac_identity_ingest call. `before` holds the record as it was and its
   shadow is clear; the call's arguments are a0 = &id, a1 = the address, a2 = pl, a3 = k. *)
Definition d1_C3 (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 1) (BASE + 0x584)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ d1_pl g pos mf i pl ly2 S2 W2 mem2 /\
getr regs2 10 = w64 (SFa g pos + V_id) /\ getr regs2 11 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 12 = w64 pl /\ getr regs2 13 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 27 = w64 pl /\ getr regs2 19 = w64 (SFa g pos + V_id) /\
sh_reg g pos regs2 /\ id_at g pos i W2 mem2 /\ hw_live g pos mf i W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before).

(* +0x598 (0x80d0c): the buf_of call of the guard copy. The first ingest has run: `id` holds the new
   record, x20 is its result, a0 = k + 1. *)
Definition d1_C4 (g : ectx) (pos mf : Z) (i : nat) (pl : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 1) (BASE + 0x598)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\ d1_pl g pos mf i pl ly2 S2 W2 mem2 /\
getr regs2 10 = w64 (SlotModel.rec_k (e_pl g) i + 1) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 27 = w64 pl /\
sh_reg g pos regs2 /\ id_at g pos (S i) W2 mem2 /\ hw_live g pos mf i W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id).

(* +0x5b4 (0x80d28): the guard copy is made and holds the payload; x24 = its address. *)
Definition d1_C5 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 2) (BASE + 0x5b4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\
hblocks B g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i); (gb, SlotModel.rec_k (e_pl g) i + 1)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
bytes_at8 W2 mem2 gb (SlotModel.rec_pl (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (e_p g + m_cur g (S i)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
d1_stab g pos mf W2 mem2 /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 24 = w64 gb /\ getr regs2 27 = w64 pl /\
sh_reg g pos regs2 /\ id_at g pos (S i) W2 mem2 /\ hw_live g pos mf i W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id).

(* +0x620 (0x80d94): the second reac_identity_ingest call, on `again` and the guard copy.
   a0 = &again, a1 = the address, a2 = the guard copy, a3 = k. *)
Definition d1_C6 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 2) (BASE + 0x620)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\
hblocks B g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i); (gb, SlotModel.rec_k (e_pl g) i + 1)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (e_p g + m_cur g (S i)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
d1_stab g pos mf W2 mem2 /\
getr regs2 10 = w64 (SFa g pos + V_again) /\
getr regs2 11 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 12 = w64 gb /\ getr regs2 13 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 24 = w64 gb /\ getr regs2 27 = w64 pl /\
sh_reg g pos regs2 /\ id_at g pos (S i) W2 mem2 /\ hw_live g pos mf i W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g i) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_again) N_again /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id /\
bytes_at8 W2 mem2 gb (SlotModel.rec_pl (e_pl g) i)).

(* +0x62c (0x80da0): the free of the guard copy. a0 = the guard copy, x26 = the second result. *)
Definition d1_C7 (g : ectx) (pos mf : Z) (i : nat) (pl gb : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat i + 2) (BASE + 0x62c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
(i < m_nrec g)%nat /\
hblocks B g ly2 S2 [(pl, SlotModel.rec_k (e_pl g) i); (gb, SlotModel.rec_k (e_pl g) i + 1)] /\
bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (e_p g + m_cur g (S i)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) /\
d1_stab g pos mf W2 mem2 /\
getr regs2 10 = w64 gb /\
getr regs2 18 = w64 (SlotModel.rec_addr (e_pl g) i) /\
getr regs2 20 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) /\
getr regs2 26 = w64 (SlotModel.rec_r (e_pl g) i) /\
getr regs2 27 = w64 pl /\
sh_reg g pos regs2 /\ id_at g pos (S i) W2 mem2 /\ hw_live g pos mf i W2 mem2 /\
bytes_at8 W2 mem2 (SFa g pos + V_before) (m_id g i) /\
bytes_at8 W2 mem2 (SFa g pos + V_again) (m_id g (S i)) /\
sh_blk W2 mem2 (SFa g pos + V_before) N_before /\
sh_blk W2 mem2 (SFa g pos + V_again) N_again /\
sh_blk W2 mem2 (SFa g pos + V_id) N_id).

Lemma d1_vm_mv : forall (W : world SEGS) (m m' : word -> option byte) a n v,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HK Hv.
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a n v); [intros k _; apply HK | exact Hv].
Qed.
Lemma d1_g8_mv : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0));
[intros k _; apply HK | exact Hv].
Qed.
Lemma d1_shz_mv : forall (W : world SEGS) (m m' : word -> option byte) a n,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) -> sh_zero W m a n -> sh_zero W m' a n.
Proof. intros W m m' a n HK Hz j Hj. unfold sh_zero, zero_shadow in *. rewrite HK. apply Hz. exact Hj. Qed.
Lemma d1_shb_mv : forall (W : world SEGS) (m m' : word -> option byte) a n,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) -> sh_blk W m a n -> sh_blk W m' a n.
Proof.
intros W m m' a n HK Hb. unfold sh_blk, block_shadow in *.
destruct Hb as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. rewrite HK. apply H3. exact Hj.
Qed.
Lemma d1_stab_mv : forall g pos mf (W : world SEGS) (m m' : word -> option byte),
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  d1_stab g pos mf W m -> d1_stab g pos mf W m'.
Proof.
intros g pos mf W m m' HK (A1 & A2 & A3 & A4 & A5).
unfold mf_fixed in A2. unfold mf_before in A3. unfold mf_again in A4. unfold mf_id in A5.
destruct A2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
unfold d1_stab, mf_fixed, mf_before, mf_again, mf_id.
repeat split; apply (d1_vm_mv W m m'); first [exact HK | assumption].
Qed.
Lemma d1_id_mv : forall g pos i (W : world SEGS) (m m' : word -> option byte),
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  id_at g pos i W m -> id_at g pos i W m'.
Proof.
intros g pos i W m m' HK (A1 & A2 & A3). unfold id_at. split; [|split].
- apply (d1_g8_mv W m m'); [exact HK | exact A1].
- apply (d1_shz_mv W m m'); [exact HK | exact A2].
- apply (d1_shb_mv W m m'); [exact HK | exact A3].
Qed.
Lemma d1_hw_mv : forall g pos mf i (W : world SEGS) (m m' : word -> option byte),
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  hw_live g pos mf i W m -> hw_live g pos mf i W m'.
Proof.
intros g pos mf i W m m' HK ((A1 & A2 & A3) & A4 & A5). unfold hw_live, hw_mem.
split; [split; [|split]|split].
- apply (d1_g8_mv W m m'); [exact HK | exact A1].
- apply (d1_shz_mv W m m'); [exact HK | exact A2].
- apply (d1_shb_mv W m m'); [exact HK | exact A3].
- apply (d1_vm_mv W m m'); [exact HK | exact A4].
- apply (d1_vm_mv W m m'); [exact HK | exact A5].
Qed.
Lemma d1_hwb_len : forall g i, length (m_hwb g i) = 8%nat.
Proof.
intros g i. unfold m_hwb, SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw (e_pl g) i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr (e_pl g) i =? RcIdentModel.ADDR_REAC_VERSION)
            && (8 <=? SlotModel.rec_k (e_pl g) i)) eqn:Hc; [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw (e_pl g) i); [exact H | reflexivity].
Qed.
Lemma d1_vm_out : forall (W : world SEGS) (m m' : word -> option byte) lo hi a (n : nat) v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' lo hi a n v HK Ha0 Ha1 Hd Hv.
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a n v); [|exact Hv].
intros k Hk. apply HK; clear - Ha0 Ha1 Hd Hk; lia.
Qed.
Lemma d1_g8_out : forall (W : world SEGS) (m m' : word -> option byte) lo hi a l,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat (length l) < 2 ^ 64 -> (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' lo hi a l HK Ha0 Ha1 Hd Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. apply HK; clear - Ha0 Ha1 Hd Hk Hj; lia.
Qed.
Lemma d1_shz_out : forall (W : world SEGS) (m m' : word -> option byte) lo hi a n,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + n < 2 ^ 47 -> 0 <= n -> shadow_addr (a + n) < lo ->
  sh_zero W m a n -> sh_zero W m' a n.
Proof.
intros W m m' lo hi a n HK Ha0 Ha1 Hn Hsh Hz j Hj.
unfold sh_zero, zero_shadow, shadow_of_addr in *.
rewrite HK; [apply Hz; exact Hj | | ].
- pose proof (YCbq.shadow_addr_bounds a ltac:(unfold kHighMemEnd; clear - Ha0 Ha1 Hn; lia)) as Hb.
  unfold shadow_addr in Hb. unfold SHADOW_OFF in *. clear - Hb Hj Ha0 Ha1 Hn. lia.
- pose proof (YCbq.shadow_mono (a) (a + n) ltac:(clear - Hn; lia)) as Hm.
  unfold shadow_addr in *. unfold SHADOW_OFF in *. clear - Hm Hsh Hj Hn. lia.
Qed.
Lemma d1_shb_out : forall (W : world SEGS) (m m' : word -> option byte) lo hi a n,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + n < 2 ^ 47 -> 0 <= n -> shadow_addr (a + n) < lo ->
  sh_blk W m a n -> sh_blk W m' a n.
Proof.
intros W m m' lo hi a n HK Ha0 Ha1 Hn Hsh Hb.
unfold sh_blk, block_shadow, shadow_of_addr in *.
destruct Hb as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. rewrite HK; [apply H3; exact Hj | |].
- pose proof (YCbq.shadow_addr_bounds a ltac:(unfold kHighMemEnd; clear - Ha0 Ha1 Hn; lia)) as Hbb.
  unfold shadow_addr in Hbb. unfold SHADOW_OFF in *. clear - Hbb Hj Ha0 Ha1 Hn. lia.
- pose proof (YCbq.shadow_mono a (a + n) ltac:(clear - Hn; lia)) as Hm.
  unfold shadow_addr in *. unfold SHADOW_OFF in *. clear - Hm Hsh Hj Hn. lia.
Qed.
Lemma d1_hdr3 : forall g pos mf i W2 c2, INVREC g pos mf i W2 c2 -> SRr SEGS W2 c2 (d1_M g pos mf i).
Proof.
intros g pos mf i W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & R14 & R15 & R24 & R23 & HRL).
destruct HRL as (V96 & Hfix & Hbef & Hagn & Hmid & Hcur & Hid & Hhw & Hbl).
destruct Hcur as (R25 & Hcr).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
set (c := SlotModel.rec_c inp i) in *.
assert (Hnlen : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
pose proof (SlotModel.rec_c_range inp i) as Hcr0. fold c in Hcr0. rewrite Hnlen in Hcr0.
assert (Hne : inp <> []).
{ intros E0. unfold m_nrec in Hi. fold inp in Hi. rewrite E0 in Hi.
  change (SlotModel.nrecn []) with 0%nat in Hi. lia. }
assert (Hn0 : 0 < e_n g).
{ rewrite Hlen. destruct inp as [|b l]; [exfalso; exact (Hne eq_refl)|]. cbn [length]. lia. }
assert (Hinblk : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  cbn [app]. destruct Hinp as [[Hz _] | [_ Hin]]; [lia | exact Hin]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hinblk) as (_ & Hp4096 & Hpce & Hpapp & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
set (bylo := SlotModel.inb inp c) in *.
set (byhi := SlotModel.inb inp (c + 1)) in *.
set (bywd := SlotModel.inb inp (c + 2)) in *.
pose proof (SlotModel.inb_range inp c) as Rlo. fold bylo in Rlo.
pose proof (SlotModel.inb_range inp (c + 1)) as Rhi. fold byhi in Rhi.
pose proof (SlotModel.inb_range inp (c + 2)) as Rwd. fold bywd in Rwd.
remember (Eimg (Ereg regs2 [w64 SB; w64 bylo; w64 byhi; w64 bywd])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 [w64 SB; w64 bylo; w64 byhi; w64 bywd]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 SB) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 bylo) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 byhi) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 bywd) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U25 : bv_unsigned (ew E 25) = e_p g + c).
{ rewrite (EE 25%nat 25%bv eq_refl), R25. apply unsigned_lit_small. clear - Hp4096 Hpce Hcr0 Hrq C1. lia. }
assert (A2 : bv_unsigned (ew E 2) = mf)
  by (rewrite (EE 2%nat 2%bv eq_refl), Rsp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (A9 : bv_unsigned (ew E 9) = mf) by exact U9.
assert (A15 : bv_unsigned (ew E 15) = 1)
  by (rewrite (EE 15%nat 15%bv eq_refl), R15; apply unsigned_lit_small; clear; lia).
assert (A25 : bv_unsigned (ew E 25) = e_p g + c) by exact U25.
assert (A32 : bv_unsigned (ew E 32) = SB)
  by (rewrite E32; apply unsigned_lit_small; unfold SB; clear; lia).
assert (A33 : bv_unsigned (ew E 33) = bylo)
  by (rewrite E33; apply unsigned_lit_small; clear - Rlo; lia).
assert (A34 : bv_unsigned (ew E 34) = byhi)
  by (rewrite E34; apply unsigned_lit_small; clear - Rhi; lia).
assert (A35 : bv_unsigned (ew E 35) = bywd)
  by (rewrite E35; apply unsigned_lit_small; clear - Rwd; lia).
clear HE.
assert (Hn26 : e_n g < 2 ^ 26) by (destruct Hinp as [[Hz _] | [[_ Hh] _]]; lia).
unfold m_cur in R24. fold inp in R24. fold c in R24.
assert (A24 : bv_unsigned (ew E 24) = e_n g - c)
  by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; clear - Hcr0 Hn0 Hn26; lia).
assert (HRAn : forall q, 0 <= q -> q <= e_n g - c ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (e_p g + c) q).
{ intros q H0 Hq. apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g));
  [exact HAR2 | exact Hinblk | clear - Hcr0; lia | clear - Hq Hcr0 Hrq H0; lia]. }
assert (HAPART : forall q x, q <= e_n g - c -> e_p g + c <= x < e_p g + c + q ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros q x Hq Hx. clear - Hx Hq Hpapp Hcr0 Hrq Hn0 C2 C3 C5.
  try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *;
  try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia. }
destruct (Z_le_gt_dec 3 (e_n g - c)) as [Hl3 | Hl3].
{ (* ---- the header reads all three bytes ---- *)
assert (Hhi4 : byhi / 64 = 0 \/ byhi / 64 = 1 \/ byhi / 64 = 2 \/ byhi / 64 = 3)
  by (clear - Rhi; lia).
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vwd : val_mem SEGS (rd W2 mem2) (e_p g + (c + 2)) 1 bywd).
{ unfold bywd. apply (d1_byte SEGS _ _ inp (c + 2)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 3 (mkAF 3 (2 ^ 26) 0) (mkAF (64 * 0) (64 * 0 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 0)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 2 1 (SOff 35 0) bywd);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vwd].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 3) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 3 (e_p g + c) 0 3);
  [ apply (HRAn 3 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 3 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 3] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply HAWR. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwge : e_n g - c - 3 <= bywd).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb]. rewrite YO0c.branch_geu.
    rewrite A35, A24, Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_true_iff, Z.ltb_ge in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_FIRMWARE.
    replace ((bylo + 256 * byhi) / 16384) with 0 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwge. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwlt : bywd < e_n g - c - 3).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb neg_bc]. rewrite YO0c.branch_geu.
    rewrite A35, A24, !Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_false_iff, Z.ltb_lt in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_FIRMWARE.
    replace ((bylo + 256 * byhi) / 16384) with 0 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, E35. unfold w64.
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwlt. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vwd : val_mem SEGS (rd W2 mem2) (e_p g + (c + 2)) 1 bywd).
{ unfold bywd. apply (d1_byte SEGS _ _ inp (c + 2)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 3 (mkAF 3 (2 ^ 26) 0) (mkAF (64 * 1) (64 * 1 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 1)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 2 1 (SOff 35 0) bywd);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vwd].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 3) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 3 (e_p g + c) 0 3);
  [ apply (HRAn 3 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 3 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 3] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply HAWR. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwge : e_n g - c - 3 <= bywd).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb]. rewrite YO0c.branch_geu.
    rewrite A35, A24, Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_true_iff, Z.ltb_ge in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_REAC_VERSION.
    replace ((bylo + 256 * byhi) / 16384) with 1 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwge. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwlt : bywd < e_n g - c - 3).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb neg_bc]. rewrite YO0c.branch_geu.
    rewrite A35, A24, !Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_false_iff, Z.ltb_lt in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_REAC_VERSION.
    replace ((bylo + 256 * byhi) / 16384) with 1 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, E35. unfold w64.
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwlt. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vwd : val_mem SEGS (rd W2 mem2) (e_p g + (c + 2)) 1 bywd).
{ unfold bywd. apply (d1_byte SEGS _ _ inp (c + 2)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 3 (mkAF 3 (2 ^ 26) 0) (mkAF (64 * 2) (64 * 2 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 2)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 2 1 (SOff 35 0) bywd);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vwd].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 3) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 3 (e_p g + c) 0 3);
  [ apply (HRAn 3 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 3 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 3] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply HAWR. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwge : e_n g - c - 3 <= bywd).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb]. rewrite YO0c.branch_geu.
    rewrite A35, A24, Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_true_iff, Z.ltb_ge in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_MODEL_NAME.
    replace ((bylo + 256 * byhi) / 16384) with 2 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwge. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwlt : bywd < e_n g - c - 3).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb neg_bc]. rewrite YO0c.branch_geu.
    rewrite A35, A24, !Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_false_iff, Z.ltb_lt in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_MODEL_NAME.
    replace ((bylo + 256 * byhi) / 16384) with 2 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, E35. unfold w64.
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwlt. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
rename Hhi4 into Hhiv.
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vwd : val_mem SEGS (rd W2 mem2) (e_p g + (c + 2)) 1 bywd).
{ unfold bywd. apply (d1_byte SEGS _ _ inp (c + 2)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 3 (mkAF 3 (2 ^ 26) 0) (mkAF (64 * 3) (64 * 3 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 3)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 2 1 (SOff 35 0) bywd);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vwd].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 3) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 3 (e_p g + c) 0 3);
  [ apply (HRAn 3 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 3 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 3] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply HAWR. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwge : e_n g - c - 3 <= bywd).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb]. rewrite YO0c.branch_geu.
    rewrite A35, A24, Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_true_iff, Z.ltb_ge in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18, E33, E34. unfold w64.
    rewrite (d1_or8 byhi bylo ltac:(clear - Rhi; lia) ltac:(clear - Rlo; lia)). f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick.
    replace ((bylo + 256 * byhi) / 16384) with 3 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwge. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
- paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  assert (Hwlt : bywd < e_n g - c - 3).
  { revert Hc. cbn [sv_denot ew ewset Nat.eqb Nat.ltb neg_bc]. rewrite YO0c.branch_geu.
    rewrite A35, A24, !Z.add_0_r. unfold w64.
    rewrite !unsigned_lit_small by (clear - Rwd Hcr0 Hn0 Hn26 Hl3; lia).
    intros HH. apply negb_false_iff, Z.ltb_lt in HH. clear - HH. lia. }
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. etransitivity; [apply HFr0 | apply HFr];
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 15%nat 15%bv eq_refl), R15 in Q15. rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18, E33, E34. unfold w64.
    rewrite (d1_or8 byhi bylo ltac:(clear - Rhi; lia) ltac:(clear - Rlo; lia)). f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick.
    replace ((bylo + 256 * byhi) / 16384) with 3 by (clear - Rlo Rhi Hhiv; lia).
    reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22, E35. unfold w64.
    f_equal. unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Hwlt. lia. }
  split.
  { rewrite Q24, (EE 24%nat 24%bv eq_refl), R24. unfold w64.
    rewrite unsigned_lit_small by (clear - Hcr0 Hn0 Hn26; lia).
    f_equal. unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [exact Q15|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms0)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms0)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
}
{ (* ---- the three short-header paths ---- *)
assert (Hl2 : e_n g - c = 0 \/ e_n g - c = 1 \/ e_n g - c = 2) by (clear - Hl3 Hcr0; lia).
clear Hl3. destruct Hl2 as [Hl3 | [Hl3 | Hl3]].
{ (* the header is cut short: 0 byte(s) left *)
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 0 (mkAF 0 0 0) d1_B255 [])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 0) E (mrestrict (w_H W2) mem2))
  by (unfold d1_hdr_SH; constructor).
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 0] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 0 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c.
    rewrite (d1_inb_past inp c ltac:(rewrite <- Hlen; clear - Hl3 Hcr0; lia)).
    rewrite (d1_inb_past inp (c + 1) ltac:(rewrite <- Hlen; clear - Hl3 Hcr0; lia)).
    unfold SlotModel.pick, RcIdentModel.ADDR_FIRMWARE. reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
{ (* the header is cut short: 1 byte(s) left *)
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 1 (mkAF 1 1 0) d1_B255 [])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 1) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 1 (e_p g + c) 0 1);
  [ apply (HRAn 1 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 1 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 1] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c.
    rewrite (d1_inb_past inp (c + 1) ltac:(rewrite <- Hlen; clear - Hl3 Hcr0; lia)).
    fold bylo. unfold SlotModel.pick, RcIdentModel.ADDR_FIRMWARE.
    replace ((bylo + 256 * 0) / 16384) with 0 by (clear - Rlo; lia). reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
{ (* two bytes left: the address is read in full *)
assert (Hhi4 : byhi / 64 = 0 \/ byhi / 64 = 1 \/ byhi / 64 = 2 \/ byhi / 64 = 3)
  by (clear - Rhi; lia).
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 2 (mkAF 2 2 0) (mkAF (64 * 0) (64 * 0 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 0)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 2) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 2 (e_p g + c) 0 2);
  [ apply (HRAn 2 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 2 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 2] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 2 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_FIRMWARE.
    replace ((bylo + 256 * byhi) / 16384) with 0 by (clear - Rlo Rhi Hhiv; lia). reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 2 (mkAF 2 2 0) (mkAF (64 * 1) (64 * 1 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 1)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 2) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 2 (e_p g + c) 0 2);
  [ apply (HRAn 2 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 2 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 2] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 2 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_REAC_VERSION.
    replace ((bylo + 256 * byhi) / 16384) with 1 by (clear - Rlo Rhi Hhiv; lia). reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
destruct Hhi4 as [Hhiv | Hhi4].
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 2 (mkAF 2 2 0) (mkAF (64 * 2) (64 * 2 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 2)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 2) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 2 (e_p g + c) 0 2);
  [ apply (HRAn 2 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 2 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 2] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 2 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18. unfold w64. f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick, RcIdentModel.ADDR_MODEL_NAME.
    replace ((bylo + 256 * byhi) / 16384) with 2 by (clear - Rlo Rhi Hhiv; lia). reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
rename Hhi4 into Hhiv.
{
assert (Vlo : val_mem SEGS (rd W2 mem2) (e_p g + c) 1 bylo).
{ unfold bylo. apply (d1_byte SEGS _ _ inp c); [exact Hinb | rewrite <- Hlen; lia]. }
assert (Vhi : val_mem SEGS (rd W2 mem2) (e_p g + (c + 1)) 1 byhi).
{ unfold byhi. apply (d1_byte SEGS _ _ inp (c + 1)); [exact Hinb | rewrite <- Hlen; lia]. }
assert (HS : st_ok_pi SEGS VAL E (d1_hdr_ss 2 (mkAF 2 2 0) (mkAF (64 * 3) (64 * 3 + 63) 0) [(SAlu ALU_SRL (SOff 34 0) (SLit 6), SLit 3)])
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x440)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_hdr_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; exfalso; clear - Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | exact V168].
    + unfold d1_in, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn].
      rewrite U25. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|]. split; [clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      split; [intros o Ho; clear - Ho C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 0 1 (SOff 33 0) bylo);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite Z.add_0_r; exact Vlo].
      * apply (chunk_ok_val SEGS E _ (e_p g + c) 1 1 (SOff 34 0) byhi);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | rewrite <- Z.add_assoc; exact Vhi].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1_mf, d1_in.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    clear - Hmf0 Hpce Hcr0 Hrq Hn0 C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    2:{ split; [|exact I]. cbn [sv_denot]. rewrite A34, Z.add_0_r.
        rewrite (d1_srl6 byhi ltac:(clear - Rhi; lia)). f_equal. clear - Rhi Hhiv. lia. }
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A15, ?A24, ?A25, ?A32, ?A33, ?A34, ?A35.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hrq Hn0 Hn26 Hl3 Rlo Rhi Rwd Hhiv;
    try unfold SB in *; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (d1_hdr_SH 2) E (mrestrict (w_H W2) mem2)).
{ unfold d1_hdr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 25 (e_p g + c) 2 (e_p g + c) 0 2);
  [ apply (HRAn 2 ltac:(clear; lia) ltac:(clear - Hl3; lia))
  | rewrite (U_atom E 32 SB E32) by (unfold SB; clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia); reflexivity
  | exact (U_atom E 25 (e_p g + c) (ltac:(rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity)) ltac:(clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia))
  | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia | clear - C1 C2 C3 C4 C5 Has HSTK' Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hceil Hslo Hp4096 Hpce Hpapp Hrq Hcr0 Hn0 Hn26 Rlo Rhi Rwd Hl3; try unfold SB in *; try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia
  | intros x Hx; apply (HAPART 2 x ltac:(clear - Hl3; lia));
    revert Hx; cbn [Z.min Z.max]; clear - Hl3; lia ]. }
assert (HAWR : forall E', awr_ok E' [d1_mf; d1_in 2] LLVMF_STK sp0 (@nil (Z * Z))
  (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E'. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi d1_in]; clear; lia | apply awr_ok_nil]. }
pose proof (st_ok_pi_pin_reg' E _ _ (24%bv : bv 5) 2 HS
  ltac:(cbn [restrict ms_regs mkst]; rewrite R24; unfold w64; f_equal; clear - Hl3; lia)
  ltac:(reflexivity)) as HSP. clear HS. rename HSP into HS.
pose proof (st_ok_pi_pin_reg' E _ _ (15%bv : bv 5) 1 HS
  ltac:(cbn [restrict ms_regs mkst]; exact R15) ltac:(reflexivity)) as HSP.
clear HS. rename HSP into HS.
unfold cfg_at. change (w64 (BASE + 0x440)) with (Z_to_bv 64 (BASE + 0x440)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x4f0; [apply HAWR|].
  apply SRr_ret.
  assert (MEQ : forall x : word, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x. apply HFr;
    intros (r & Hin & Ha); cbn [ss_mem add_cond d1_hdr_ss] in Hin; unfold d1_mf, d1_in in Hin;
    cbn [In firstn] in Hin;
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Ha; clear - Ha; lia. }
  assert (AVEQ : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
    by (intros a; apply aview_eq_of; apply MEQ).
  rewrite ?wvb_collapse in HJ.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
  prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9. prreg HS (8%bv : bv 5) P8.
  prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EE 14%nat 14%bv eq_refl), R14 in Q14.
  rewrite (EE 23%nat 23%bv eq_refl) in Q23.
  unfold d1_M, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0.
    split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V16]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V192]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact V168]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vra]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vs0]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W24]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W32]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W40]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W48]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W56]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W64]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W72]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W80]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W88]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W96]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact W104]|].
    split; [apply (d1_vm_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Vflag]|].
    split; [exact HPRE|].
    split; [intros fd; rewrite Efd; reflexivity|].
    split; [exact Efs|].
    apply (d1_g8_mv W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hinb]. }
  split; [exact Hi|].
  split.
  { rewrite Q18, E33, E34. unfold w64.
    rewrite (d1_or8 byhi bylo ltac:(clear - Rhi; lia) ltac:(clear - Rlo; lia)). f_equal.
    unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi.
    fold inp. fold c. fold bylo. fold byhi. unfold SlotModel.pick.
    replace ((bylo + 256 * byhi) / 16384) with 3 by (clear - Rlo Rhi Hhiv; lia). reflexivity. }
  split.
  { rewrite Q20, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by (unfold m_cur; fold inp; fold c; clear - Hp4096 Hpce Hcr0 Hrq C1; lia).
    f_equal. unfold m_cur, SlotModel.rec_body, SlotModel.h_body, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split.
  { rewrite Q22. unfold w64. f_equal.
    unfold SlotModel.rec_k, SlotModel.h_k, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left, SlotModel.h_w.
    fold inp. fold c. fold bywd. rewrite Hnlen. clear - Hl3 Hcr0 Rwd. lia. }
  split.
  { rewrite Q24. unfold w64. f_equal.
    unfold SlotModel.rec_Lp, SlotModel.h_Lp, SlotModel.h_h, SlotModel.h_left.
    fold inp. fold c. rewrite Hnlen. clear - Hl3 Hcr0. lia. }
  split; [exact Q25|].
  split; [exact Q14|].
  split; [rewrite Q15; reflexivity|].
  split; [unfold sh_reg; rewrite Q23; exact R23|].
  split; [apply (d1_stab_mv g pos mf W2 mem2 (ms_mem ms)); [exact AVEQ|];
          split; [exact V96|]; split; [exact Hfix|]; split; [exact Hbef|]; split; [exact Hagn | exact Hmid]|].
  split; [apply (d1_id_mv g pos i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hid]|].
  split; [apply (d1_hw_mv g pos mf i W2 mem2 (ms_mem ms)); [exact AVEQ | exact Hhw]|].
  exact Hbl.
}
}
}
Qed.
Lemma d1_m_c1 : forall g pos mf i W2 c2, d1_M g pos mf i W2 c2 -> SRr SEGS W2 c2 (d1_C1 g pos mf i).
Proof.
intros g pos mf i W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & R18 & R20 & R22 & R24 & R25 & R14 & R15 & R23 & Hstab & Hid & Hhw & Hbl).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
assert (Hnlen : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hne : inp <> []).
{ intros E0. unfold m_nrec in Hi. fold inp in Hi. rewrite E0 in Hi.
  change (SlotModel.nrecn []) with 0%nat in Hi. lia. }
assert (Hn0 : 0 < e_n g).
{ rewrite Hlen. destruct inp as [|b l]; [exfalso; exact (Hne eq_refl)|]. cbn [length]. lia. }
assert (Hn26 : e_n g < 2 ^ 26) by (destruct Hinp as [[Hz _] | [[_ Hh] _]]; lia).
assert (Hinblk : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  cbn [app]. destruct Hinp as [[Hz _] | [_ Hin]]; [lia | exact Hin]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hinblk) as (_ & Hp4096 & Hpce & Hpapp & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
pose proof (SlotModel.rec_bounds inp i) as (Hh3 & Hbod0 & Hbodk & HLpe & Hkle & Hcs).
pose proof (SlotModel.rec_k_range inp i) as Hkr.
pose proof (SlotModel.rec_c_range inp i) as Hcr0. rewrite Hnlen in Hcr0.
pose proof (SlotModel.rec_c_range inp (S i)) as Hcr1. rewrite Hnlen in Hcr1.
rewrite Hnlen in Hbodk, HLpe.
assert (Hi64 : Z.of_nat i < 64).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp in Hi.
  pose proof (SlotModel.nrec_range inp) as Hnr. clear - Hi Hnr. lia. }
assert (Hcs' : m_cur g (S i) = SlotModel.rec_body inp i + SlotModel.rec_k inp i)
  by (unfold m_cur; fold inp; exact Hcs).
remember (Eimg (Ereg regs2 [w64 SB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 [w64 SB]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 SB) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (A2 : bv_unsigned (ew E 2) = mf)
  by (rewrite (EE 2%nat 2%bv eq_refl), Rsp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (A9 : bv_unsigned (ew E 9) = mf)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (A20 : bv_unsigned (ew E 20) = e_p g + SlotModel.rec_body inp i).
{ rewrite (EE 20%nat 20%bv eq_refl), R20. fold inp. apply unsigned_lit_small.
  clear - Hp4096 Hpce Hcr0 Hcr1 Hbodk Hbod0 Hrq C1 Hkr. lia. }
assert (A22 : bv_unsigned (ew E 22) = SlotModel.rec_k inp i).
{ rewrite (EE 22%nat 22%bv eq_refl), R22. fold inp. apply unsigned_lit_small. clear - Hkr. lia. }
assert (A24 : bv_unsigned (ew E 24) = SlotModel.rec_Lp inp i).
{ rewrite (EE 24%nat 24%bv eq_refl), R24. fold inp. apply unsigned_lit_small.
  clear - HLpe Hbod0 Hcr0 Hn0 Hn26 Hbodk Hkr Hkle Hcr1; lia. }
assert (A14 : bv_unsigned (ew E 14) = Z.of_nat i)
  by (rewrite (EE 14%nat 14%bv eq_refl), R14; apply unsigned_lit_small; clear - Hi64; lia).
assert (Hmc0 : m_cur g i = SlotModel.rec_c inp i) by reflexivity.
assert (A25 : bv_unsigned (ew E 25) = e_p g + SlotModel.rec_c inp i).
{ rewrite (EE 25%nat 25%bv eq_refl), R25, Hmc0. apply unsigned_lit_small.
  clear - Hp4096 Hpce Hcr0 Hrq C1. lia. }
assert (HS : st_ok_pi SEGS VAL E d1_st_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x4f0)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1_st_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold d1_mfw, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite A9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; clear - Ho Hmfb HSTK' Has; lia|].
    constructor.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, PTR, d1_B255. cbn [af_lo af_hi af_al2].
    rewrite ?A2, ?A9, ?A14, ?A20, ?A22, ?A24, ?A25.
    repeat match goal with |- _ /\ _ => split end;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hp4096 Hpce Hcr0 Hcr1 Hrq Hn0 Hn26 Hkr Hbod0 Hbodk HLpe Hi64;
    lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
assert (HAWR : forall E', bv_unsigned (ew E' 9) = mf ->
  awr_ok E' [d1_mfw] LLVMF_STK sp0 (@nil (Z * Z)) (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)]).
{ intros E' HE9. eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [reflexivity | rewrite HE9; clear; lia | cbn [YP09.r_wlo d1_mfw]; clear - Hmfb HSTK' Has; lia
  | cbn [YP09.r_whi d1_mfw]; clear - Hmfb; lia | apply awr_ok_nil]. }
assert (E20' : ew E 20 = Z_to_bv 64 (e_p g + SlotModel.rec_body inp i))
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (E22' : ew E 22 = Z_to_bv 64 (SlotModel.rec_k inp i))
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; reflexivity).
assert (Ubod : U E (SOff 20 0) = e_p g + SlotModel.rec_body inp i)
  by (apply (U_atom E 20 _ E20'); clear - Hp4096 Hpce Hcr0 Hcr1 Hbodk Hbod0 Hrq C1 Hkr; lia).
assert (Uk : U E (SOff 22 0) = SlotModel.rec_k inp i)
  by (apply (U_atom E 22 _ E22'); clear - Hkr; lia).
assert (UADD : U E (SAlu ALU_ADD (SOff 20 0) (SOff 22 0))
  = e_p g + SlotModel.rec_body inp i + SlotModel.rec_k inp i).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite Ubod, Uk. unfold zcanon, M64.
  rewrite Z.mod_small; [reflexivity|].
  clear - Hp4096 Hpce Hcr0 Hcr1 Hbodk Hbod0 Hrq C1 Hkr. lia. }
unfold cfg_at. change (w64 (BASE + 0x4f0)) with (Z_to_bv 64 (BASE + 0x4f0)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x51c.
{ apply HAWR. exact A9. }
psrr_branch_tok RUN BR HS SHOK Bspan.
2:{ exfalso. revert Hc. rewrite YO0c.branch_geu.
    change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 20 0) (SOff 22 0))))
      with (U E (SAlu ALU_ADD (SOff 20 0) (SOff 22 0))).
    change (bv_unsigned (sv_denot E (SOff 20 0))) with (U E (SOff 20 0)).
    rewrite UADD, Ubod. intros HH. apply negb_false_iff, Z.ltb_lt in HH.
    clear - HH Hkr. lia. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x51c.
{ apply HAWR. exact A9. }
apply SRr_ret.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 136) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E (ss_mem d1_st_ss) (w_H W2) mem2 (ms_mem ms)
    (fun x => mf + 112 <= x < mf + 136) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold d1_st_ss, windows in Hin. cbn [ss_mem map In d1_mfw] in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. rewrite A9 in Hr. lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 136) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) (ms_mem ms) (ms_mem ms0)
    (fun x => mf + 112 <= x < mf + 136) HFr0); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. cbn [ss_mem add_cond windows map In] in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. rewrite A9 in Hr. lia. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 136) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite (KEEP2 a Ha Hw). exact (KEEP1 a Ha Hw). }
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2
  ltac:(rewrite Hfrs; left; reflexivity)) as (HSF0 & HSF1 & HSFapp).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in HSF1, HSFapp.
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
rewrite EFa in HSF0, HSF1, HSFapp.
assert (VMS : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (a + Z.of_nat n <= mf + 112 \/ mf + 136 <= a) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v Ha0 Ha1 Hd Hv. apply (d1_vm_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) a n v);
  [exact KEEP | exact Ha0 | exact Ha1 | exact Hd | exact Hv]. }
pose proof (st_ok_pi_region_nth E _ _ 0%nat _ HS eq_refl) as HR0.
cbn [ms_mem restrict] in HR0.
prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (23%bv : bv 5) Q23. prreg HS (2%bv : bv 5) P2. prreg HS (9%bv : bv 5) P9.
prreg HS (8%bv : bv 5) P8. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Q10, Q22.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Q18.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Q20.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25.
rewrite (EE 23%nat 23%bv eq_refl) in Q23.
rewrite ?wvb_collapse in HJ.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
assert (V120 : val_mem SEGS (rd W2 (ms_mem ms0)) (mf + 120) 8 (SlotModel.rec_Lp inp i)).
{ apply (field_of_region E _ 9%nat mf _ 112 176 112 136 120 8%N (SOff 24 0) (SlotModel.rec_Lp inp i) HR0 A9);
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite A24, Z.add_0_r; reflexivity
  | clear - HLpe Hbod0 Hcr0 Hn0 Hn26 Hbodk Hkr Hkle Hcr1; cbn; lia
  | clear; lia .. ]. }
assert (V128 : val_mem SEGS (rd W2 (ms_mem ms0)) (mf + 128) 8 (Z.of_nat i)).
{ apply (field_of_region E _ 9%nat mf _ 112 176 112 136 128 8%N (SOff 14 0) (Z.of_nat i) HR0 A9);
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite A14, Z.add_0_r; reflexivity
  | clear - Hi64; cbn; lia | clear; lia .. ]. }
unfold d1_C1, acut. pmkst HS.
exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md2) mat0 md2).
split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0.
  split; [exact P2|]. split; [exact P9|]. split; [exact P8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact P3|]. split; [exact P4|].
  split; [apply (VMS (mf + 16) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact V16]|].
  split; [apply (VMS (mf + 64) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact V64]|].
  split; [apply (VMS (mf + 192) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact V192]|].
  split; [apply (VMS (mf + 168) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact V168]|].
  split; [apply (VMS (sp0 - 8) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply (VMS (sp0 - 16) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply (VMS (sp0 - 24) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W24]|].
  split; [apply (VMS (sp0 - 32) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W32]|].
  split; [apply (VMS (sp0 - 40) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W40]|].
  split; [apply (VMS (sp0 - 48) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W48]|].
  split; [apply (VMS (sp0 - 56) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W56]|].
  split; [apply (VMS (sp0 - 64) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W64]|].
  split; [apply (VMS (sp0 - 72) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W72]|].
  split; [apply (VMS (sp0 - 80) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W80]|].
  split; [apply (VMS (sp0 - 88) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W88]|].
  split; [apply (VMS (sp0 - 96) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W96]|].
  split; [apply (VMS (sp0 - 104) 8%nat); [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear - Hmfb; lia | exact W104]|].
  split; [apply (VMS (SFa g pos + 1016) 8%nat); [clear - HSF0; lia | clear - HSF1 Hmf0 C1; lia | clear - HSF1 Hmf0 C1; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  apply (d1_g8_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (e_p g));
  [ exact KEEP | clear - Hp4096; lia
  | rewrite length_map; replace (Z.of_nat (length (e_pl g))) with (e_n g) by (exact Hlen);
    clear - Hp4096 Hpce Hrq C1; lia
  | rewrite length_map; replace (Z.of_nat (length (e_pl g))) with (e_n g) by (exact Hlen);
    clear - Hp4096 Hpce Hrq C1 Hmf0; lia
  | exact Hinb ]. }
split; [exact Hi|].
split; [exact Q10|].
split; [exact Q18|].
split.
{ rewrite (EE 20%nat 20%bv eq_refl), R20, (EE 22%nat 22%bv eq_refl), R22 in Q19.
  unfold w64 in Q19. rewrite YI08.alu64_add_lit in Q19. rewrite Q19.
  unfold w64. f_equal. rewrite Hcs'. clear. lia. }
split; [exact Q20|].
split; [exact Q22|].
split; [exact Q25|].
split; [unfold sh_reg; rewrite Q23; exact R23|].
split.
{ destruct Hstab as (S96 & Sfix & Sbef & Sagn & Sid).
  unfold mf_fixed in Sfix. destruct Sfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
  unfold mf_before in Sbef. unfold mf_again in Sagn. unfold mf_id in Sid.
  unfold d1_stab, mf_fixed, mf_before, mf_again, mf_id.
  split; [apply (VMS (mf + 96) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact S96]|].
  split.
  { split; [apply (VMS (mf + 32) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F32]|].
    split; [apply (VMS (mf + 48) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F48]|].
    split; [apply (VMS (mf + 56) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F56]|].
    split; [apply (VMS (mf + 72) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F72]|].
    split; [apply (VMS (mf + 80) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F80]|].
    split; [apply (VMS (mf + 88) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F88]|].
    split; [apply (VMS (mf + 104) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F104]|].
    split; [apply (VMS (mf + 136) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F136]|].
    split; [apply (VMS (mf + 144) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F144]|].
    apply (VMS (mf + 160) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact F160]. }
  split; [apply (VMS (mf + 152) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact Sbef]|].
  split; [apply (VMS (mf + 176) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact Sagn]|].
  apply (VMS (mf + 184) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact Sid]. }
split; [exact V120|].
split; [exact V128|].
split.
{ destruct Hid as (I1 & I2 & I3). unfold id_at. split; [|split].
  - apply (d1_g8_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_id));
    [ exact KEEP | unfold V_id; clear - HSF0; lia
    | rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length;
      unfold V_id, RcIdentModel.ID_SIZE; clear - HSF1 C1; lia
    | rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length;
      unfold V_id, RcIdentModel.ID_SIZE; clear - HSF1 Hmf0 C1; lia
    | exact I1 ].
  - apply (d1_shz_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_id) N_id);
    [ exact KEEP | unfold V_id; clear - HSF0; lia | unfold V_id, N_id; clear - HSF1 C1; lia
    | unfold N_id; clear; lia
    | pose proof (YCbq.shadow_addr_bounds (SFa g pos + V_id + N_id)
        ltac:(unfold V_id, N_id, kHighMemEnd; clear - HSF0 HSF1 C1; lia)) as Hsb;
      unfold kHighShadowEnd in Hsb; clear - Hsb Hmf0 C1; lia
    | exact I2 ].
  - apply (d1_shb_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_id) N_id);
    [ exact KEEP | unfold V_id; clear - HSF0; lia | unfold V_id, N_id; clear - HSF1 C1; lia
    | unfold N_id; clear; lia
    | pose proof (YCbq.shadow_addr_bounds (SFa g pos + V_id + N_id)
        ltac:(unfold V_id, N_id, kHighMemEnd; clear - HSF0 HSF1 C1; lia)) as Hsb;
      unfold kHighShadowEnd in Hsb; clear - Hsb Hmf0 C1; lia
    | exact I3 ]. }
split.
{ destruct Hhw as ((Y1 & Y2 & Y3) & Y4 & Y5). unfold hw_live, hw_mem.
  split; [split; [|split]|split].
  - apply (d1_g8_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_hw + 4));
    [ exact KEEP | unfold V_hw; clear - HSF0; lia
    | rewrite length_map, (d1_hwb_len g i); unfold V_hw; clear - HSF1 C1; lia
    | rewrite length_map, (d1_hwb_len g i); unfold V_hw; clear - HSF1 Hmf0 C1; lia
    | exact Y1 ].
  - apply (d1_shz_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_hw) N_hw);
    [ exact KEEP | unfold V_hw; clear - HSF0; lia | unfold V_hw, N_hw; clear - HSF1 C1; lia
    | unfold N_hw; clear; lia
    | pose proof (YCbq.shadow_addr_bounds (SFa g pos + V_hw + N_hw)
        ltac:(unfold V_hw, N_hw, kHighMemEnd; clear - HSF0 HSF1 C1; lia)) as Hsb;
      unfold kHighShadowEnd in Hsb; clear - Hsb Hmf0 C1; lia
    | exact Y2 ].
  - apply (d1_shb_out W2 mem2 (ms_mem ms0) (mf + 112) (mf + 136) (SFa g pos + V_hw) N_hw);
    [ exact KEEP | unfold V_hw; clear - HSF0; lia | unfold V_hw, N_hw; clear - HSF1 C1; lia
    | unfold N_hw; clear; lia
    | pose proof (YCbq.shadow_addr_bounds (SFa g pos + V_hw + N_hw)
        ltac:(unfold V_hw, N_hw, kHighMemEnd; clear - HSF0 HSF1 C1; lia)) as Hsb;
      unfold kHighShadowEnd in Hsb; clear - Hsb Hmf0 C1; lia
    | exact Y3 ].
  - apply (VMS (SFa g pos + V_hw) 4%nat); [unfold V_hw; clear - HSF0; lia
    | unfold V_hw; clear - HSF1 C1; lia | unfold V_hw; clear - HSF1 Hmf0 C1; lia | exact Y4 ].
  - apply (VMS (mf + 24) 8%nat); [clear - Hmf0 C1; lia | clear - Hmf0 Hmfb Hshi H47 C1; lia | clear; lia | exact Y5 ]. }
exact Hbl.
Qed.

(* ---- d1_c1_c2: the payload copy, +0x51c .. +0x548 (0x80c90 .. 0x80cbc) ------------------------------------ *)
(* The one machine-frame word the stretch writes: mf+112 (0x80ca4), base s1 (atom 9). *)
Definition mal_mf : YP09.region := YP09.mkRegion (Some 9%nat) 112 120 112 120 [].
Definition mal_ss : sstate :=
  mkSS 0x51c sr_atoms [mal_mf] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Let mal_RUNP := SRr_run_pi_AJ B LAWS.
Let mal_RUNC := SRr_run_pi_AJ_call B LAWS.
Let mal_RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma mal_eq0 : forall E n v b, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H Hr Hc. rewrite branch_eq_U in Hc.
rewrite (U_atom E n v H Hr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia). exact Hc.
Qed.
Lemma mal_ne0 : forall E n v b, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> negb (v =? 0) = b.
Proof.
intros E n v b H Hr Hc. rewrite branch_ne_U in Hc.
rewrite (U_atom E n v H Hr), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia). exact Hc.
Qed.
Lemma mal_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk8]. apply Z.leb_le in Hk8.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.
Lemma mal_nth_fs : forall {A} (l : list A) (bd kk j : nat) (d : A), (j < kk)%nat ->
  nth j (firstn kk (skipn bd l)) d = nth (bd + j) l d.
Proof.
intros A l bd. revert l. induction bd as [|bd IH]; intros l kk j d Hj.
- cbn [skipn Nat.add]. revert l j Hj. induction kk as [|kk IH2]; intros l j Hj; [lia|].
  destruct l as [|a l]; [rewrite firstn_nil; reflexivity|].
  cbn [firstn]. destruct j as [|j]; cbn [nth]; [reflexivity | apply IH2; lia].
- destruct l as [|a l].
  + rewrite skipn_nil, firstn_nil, !nth_overflow by (cbn [length]; lia). reflexivity.
  + cbn [skipn Nat.add]. apply IH. exact Hj.
Qed.
(* the j-th byte of the record's payload is the (body + j)-th byte of the input *)
Lemma mal_pl_nth : forall inp i j, (j < Z.to_nat (SlotModel.rec_k inp i))%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (SlotModel.rec_pl inp i)) 0 =
  nth (Z.to_nat (SlotModel.rec_body inp i) + j) (map (fun b : byte => bv_unsigned b) inp) 0.
Proof.
intros inp i j Hj.
transitivity (bv_unsigned (nth j (SlotModel.rec_pl inp i) (RcIdentModel.zb 0))).
- apply (map_nth (fun b : byte => bv_unsigned b) (SlotModel.rec_pl inp i) (RcIdentModel.zb 0) j).
- transitivity (bv_unsigned (nth (Z.to_nat (SlotModel.rec_body inp i) + j) inp (RcIdentModel.zb 0))).
  + f_equal. unfold SlotModel.rec_pl, SlotModel.h_pl. apply mal_nth_fs. exact Hj.
  + symmetry. apply (map_nth (fun b : byte => bv_unsigned b) inp (RcIdentModel.zb 0) _).
Qed.
Lemma mal_garr8_moved : forall (segs : list Segment) H H' (m m' : word -> option byte) a l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (a + j) = aview segs H m (a + j)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros segs H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hk1. replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.
Lemma mal_zshadow_moved : forall (rdr rdr' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rdr' (shadow_of_addr Bs a + i) = rdr (shadow_of_addr Bs a + i)) ->
  zero_shadow rdr Bs a n -> zero_shadow rdr' Bs a n.
Proof. intros rdr rdr' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma mal_bshadow_moved : forall (rdr rdr' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rdr' (shadow_of_addr Bs a + i) = rdr (shadow_of_addr Bs a + i)) ->
  block_shadow rdr Bs a n -> block_shadow rdr' Bs a n.
Proof.
intros rdr rdr' Bs a n Hk (Hm & Hn & Hb). split; [exact Hm|]. split; [exact Hn|].
intros i Hi. rewrite (Hk i Hi). exact (Hb i Hi).
Qed.
(* The cut at +0x548, from the start cut and what the stretch did: both paths of the copy end here. *)
Lemma mal_fin : forall g pos mf i (res : Z) ly2 S2 W2 regs2 mem2 md2 ly3 S3 (W3 : world SEGS) memF regsF mdF,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  frames S2 = [(4, pos)] ->
  (i < m_nrec g)%nat ->
  getr regs2 19 = w64 (e_p g + m_cur g (S i)) ->
  d1_stab g pos mf W2 mem2 ->
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.rec_Lp (e_pl g) i) ->
  val_mem SEGS (rd W2 mem2) (mf + 128) 8 (Z.of_nat i) ->
  id_at g pos i W2 mem2 -> hw_live g pos mf i W2 mem2 -> hblocks B g ly2 S2 [] ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 memF mdF (4 * Z.of_nat i + 1) ->
  frames S3 = frames S2 ->
  mo_le MT (e_S g) S2 (4 * Z.of_nat i * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat i) * MEV MT) ->
  mo_le MT S2 S3 (mo_malloc MT (SlotModel.rec_k (e_pl g) i)) ->
  ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(res, SlotModel.rec_k (e_pl g) i)] ->
  4096 <= res ->
  (forall a, mf <= a < e_sp0 g -> ~ (mf + 112 <= a < mf + 120) ->
     aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, (SFa g pos <= a < SFa g pos + 1024 \/
              shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
     aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, e_p g <= a < e_p g + req_size (e_n g) ->
     aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a) ->
  getr regsF 2 = w64 mf -> getr regsF 9 = w64 mf -> getr regsF 8 = w64 (e_sp0 g) ->
  getr regsF 3 = w64 (as_gp B) -> getr regsF 4 = w64 (as_tp B) ->
  getr regsF 18 = w64 (SlotModel.rec_addr (e_pl g) i) ->
  getr regsF 22 = w64 (SlotModel.rec_k (e_pl g) i) ->
  sh_reg g pos regsF -> getr regsF 27 = w64 res ->
  val_mem SEGS (rd W3 memF) (mf + 112) 8 (e_p g + m_cur g (S i)) ->
  bytes_at8 W3 memF res (SlotModel.rec_pl (e_pl g) i) ->
  d1_C2 g pos mf i res W3 (cfg_at SEGS (BASE + 0x548) regsF memF mdF).
Proof.
intros g pos mf i res ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 memF regsF mdF
  HC Hfrs Hi R19 Hstab V120 V128 Hid Hhw Hbl HJF Hfrs3 MLE MOK MLE3 Eab3 Hres4096
  FS FF FP Z2 Z9 Z8 Z3 Z4 Z18 Z22 Z23 Z27 V112 HPL.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct Hstab as (V96 & Hfix & Hbef & Hagn & Hmid).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & Hbb0 & _).
pose proof HJF as (HARF & HlyF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresF & HstaticF & _).
pose proof HstaticF as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof HlyF as (_ & _ & _ & _ & _ & EFF & _).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
pose proof (SlotModel.nrec_range inp) as Hnr.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp in Hi. clear - Hi Hnr. lia. }
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3, Hfrs; left; reflexivity).
assert (EFa : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EFF; reflexivity).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memF mdF 4 pos HARF Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly3 S3 W3 memF mdF 4 pos HARF Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the transports *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= mf + 112 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 memF) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 memF a a n v); [|exact Hv].
  intros kk Hkk. apply FS; clear - H1 H2 Hkk Hmfb; lia. }
assert (VMS2 : forall a (n : nat) v, mf + 120 <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 memF) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 memF a a n v); [|exact Hv].
  intros kk Hkk. apply FS; clear - H1 H2 Hkk Hmfb; lia. }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W3 memF) (SF + off) n v).
{ intros off n v H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 memF (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply FF. left. clear - H1 H2 Hkk. lia. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W3 memF) (SF + off) l).
{ intros off l H1 H2 Hg. apply (mal_garr8_moved SEGS (w_H W2) (w_H W3) mem2 memF _ l); [|exact Hg].
  intros kk Hkk. apply FF. left. clear - H1 H2 Hkk. lia. }
assert (SHZ : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W3 memF (SF + off) n).
{ intros off n H1 H2 Hn Hz. unfold sh_zero in *.
  apply (mal_zshadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) memF) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FF. right. unfold shadow_of_addr. rewrite Esh.
  clear - H1 H2 Hn Hii HSF64. lia. }
assert (SHB : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W3 memF (SF + off) n).
{ intros off n H1 H2 Hn Hz. unfold sh_blk in *.
  apply (mal_bshadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) memF) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FF. right. unfold shadow_of_addr. rewrite Esh.
  clear - H1 H2 Hn Hii HSF64. lia. }
assert (HINB : bytes_at8 W3 memF (e_p g) inp).
{ unfold bytes_at8 in *. apply (mal_garr8_moved SEGS (w_H W2) (w_H W3) mem2 memF _ _); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  pose proof (req_size_pos (e_n g) ltac:(clear - Hj; lia)) as Hrq.
  apply FP. clear - Hj Hrq. lia. }
(* the meter *)
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL k 256 ltac:(clear - Hkr; lia)) as HMk.
pose proof (mo_malloc_nonneg MT MTL k ltac:(clear - Hkr; lia)) as HMk0.
unfold d1_C2, acut.
exists ly3, S3, regsF, memF, mdF.
split; [reflexivity|].
split; [exact HJF|].
split; [rewrite Hfrs3; exact Hfrs|].
split; [unfold EV_LLVMF; clear - Hi64; lia|].
split.
{ eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3)|].
  unfold MEV. clear - HM0 HF0 HMk. nia. }
split.
{ apply (mo_ok_step MT MTL S2 S3 (mo_malloc MT k)); [|exact MLE3].
  apply (mo_ok_le MT MTL _ _ _ MOK). unfold MEV. clear - HM0 HF0 HMk HMk0 Hi64. nia. }
split.
{ unfold ecommon. fold sp0 SF.
  split; [exact Z2|]. split; [exact Z9|]. split; [exact Z8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Z3|]. split; [exact Z4|].
  split; [apply VMS; [clear; lia | clear; lia | exact V16]|].
  split; [apply VMS; [clear; lia | clear; lia | exact V64]|].
  split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W24]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W32]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W40]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W48]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W56]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W64]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W72]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W80]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W88]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W96]|].
  split; [apply VMS2; [clear - Hmfb; lia | clear - Hmfb; lia | exact W104]|].
  split; [apply (VMF 1016 8%nat); [clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [Efd Efs].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [rewrite Efs; reflexivity|].
  exact HINB. }
(* the stretch's own post *)
split; [exact Hi|].
split.
{ unfold d1_pl. fold inp k SF.
  split.
  { split.
    - rewrite Eab3. cbn [app]. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
      apply perm_skip. destruct Hbl as [Hperm _]. cbn [app] in Hperm. exact Hperm.
    - constructor; [|constructor]. cbn [fst snd]. split; [exact Hres4096 | clear - Hkr; lia]. }
  split; [exact HPL|].
  split; [exact V112|].
  split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact V128]|].
  unfold d1_stab. fold SF.
  split; [apply VMS; [clear; lia | clear; lia | exact V96]|].
  split.
  { destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
    unfold mf_fixed. fold SF.
    split; [apply VMS; [clear; lia | clear; lia | exact F32]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F48]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F56]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F72]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F80]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F88]|].
    split; [apply VMS; [clear; lia | clear; lia | exact F104]|].
    split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact F136]|].
    split; [apply VMS2; [clear; lia | clear - Hmfb; lia | exact F144]|].
    apply VMS2; [clear; lia | clear - Hmfb; lia | exact F160]. }
  split; [unfold mf_before in *; fold SF; apply VMS2; [clear; lia | clear - Hmfb; lia | exact Hbef]|].
  split; [unfold mf_again in *; fold SF; apply VMS2; [clear; lia | clear - Hmfb; lia | exact Hagn]|].
  unfold mf_id in *. fold SF. apply VMS2; [clear; lia | clear - Hmfb; lia | exact Hmid]. }
split; [exact Z18|].
split; [exact Z22|].
split; [exact Z27|].
split; [exact Z23|].
split.
{ destruct Hid as (Hidb & Hidz & Hidbk). unfold id_at. fold SF.
  split.
  { apply (GF V_id); [unfold V_id; clear; lia | | exact Hidb].
    rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
    unfold V_id, RcIdentModel.ID_SIZE. clear; lia. }
  split.
  - apply (SHZ V_id N_id); [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia
    | unfold N_id; clear; lia | exact Hidz].
  - apply (SHB V_id N_id); [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia
    | unfold N_id; clear; lia | exact Hidbk]. }
{ destruct Hhw as ((Hhw1 & Hhw2 & Hhw3) & Hhw4 & Hhw5). unfold hw_live, hw_mem. fold SF.
  split.
  { split.
    - replace (SF + V_hw + 4) with (SF + (V_hw + 4)) by ring.
      apply (GF (V_hw + 4)); [unfold V_hw; clear; lia | | ].
      + rewrite length_map. unfold m_hwb. rewrite mal_hwb_length. unfold V_hw. clear; lia.
      + replace (SF + (V_hw + 4)) with (SF + V_hw + 4) by ring. exact Hhw1.
    - split.
      + apply (SHZ V_hw N_hw); [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia
        | unfold N_hw; clear; lia | exact Hhw2].
      + apply (SHB V_hw N_hw); [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia
        | unfold N_hw; clear; lia | exact Hhw3]. }
  split; [apply (VMF V_hw 4%nat); [unfold V_hw; clear; lia | unfold V_hw; clear; lia | exact Hhw4]|].
  apply VMS; [clear; lia | clear; lia | exact Hhw5]. }
Qed.

Lemma d1_c1_c2 : forall g pos mf i W2 c2, d1_C1 g pos mf i W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists pl, d1_C2 g pos mf i pl W3 c3).
Proof.
intros g pos mf i W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HC as HCC.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & R10 & R18 & R19 & R20 & R22 & R25 & R23 & Hstab & V120 & V128 & Hid & Hhw & Hbl).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & Hbb0 & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
set (bod := SlotModel.rec_body inp i) in *.
pose proof (SlotModel.rec_bounds inp i) as (_ & Hbod0 & Hbodk & _ & _ & Hcs).
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
fold k bod in Hbodk, Hcs.
assert (Hnlen : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
rewrite Hnlen in Hbodk.
pose proof (SlotModel.nrec_range inp) as Hnr.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp in Hi. clear - Hi Hnr. lia. }
assert (Hne : inp <> []).
{ intros E0. unfold m_nrec in Hi. fold inp in Hi. rewrite E0 in Hi.
  change (SlotModel.nrecn []) with 0%nat in Hi. lia. }
assert (Hn0 : 0 < e_n g).
{ rewrite Hlen. destruct inp as [|b l]; [exfalso; exact (Hne eq_refl)|]. cbn [length]. lia. }
assert (Hn26 : e_n g < 2 ^ 26) by (destruct Hinp as [[Hz _] | [[_ Hh] _]]; lia).
assert (Hinblk : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  cbn [app]. destruct Hinp as [[Hz _] | [_ Hin]]; [lia | exact Hin]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hinblk) as (_ & Hp4096 & Hpce & Hpapp & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
(* the environment: the registers only *)
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (HS : st_ok_pi SEGS VAL E mal_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x51c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold mal_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold mal_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho Hmfb HSTK' Has. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32; lia. }
unfold cfg_at. change (w64 (BASE + 0x51c)) with (Z_to_bv 64 (BASE + 0x51c)).
(* ---- run 1: the malloc call at 0x80c90 ---- *)
paj_run_shc mal_RUNP mal_RUNC HS HJ.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo mal_mf]; clear - Hmfb HSTK' Has; lia
  | cbn [YP09.r_whi mal_mf]; clear - Hmfb; lia | apply awr_ok_nil]. }
(* what run 1 kept: every byte outside mf+112 .. mf+120 *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 120) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => mf + 112 <= x < mf + 120) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold mal_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr; rewrite U9 in Hr; clear - Hr; lia. }
clear HF HFr HG.
(* the registers at the call *)
prreg HS (10%bv : bv 5) Q10. prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
pmkst HS. rewrite (pal_malloc B TL).
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite Q2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Ura : raZ (ms_regs ms) = BASE + 0x520).
{ unfold raZ. rewrite Q1. apply unsigned_lit_small. clear - HBASE. lia. }
(* the malloc's premises *)
assert (Hnev : st_nev S2 < EV_MAX).
{ unfold EV_LLVMF in HEV. clear - Hnev2 Hnev0 HEV Hi64. lia. }
assert (Hlive : blocks_bytes S2 + k <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ (proj1 Hbl)). cbn [app].
  rewrite <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
  unfold LIVE_LLVMF in HLIVE. clear - Hbb0 HLIVE Hkr. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL k 256 ltac:(lia)) as HMk.
pose proof (mo_malloc_nonneg MT MTL k ltac:(lia)) as HMk0.
assert (MOKm : mo_ok MT S2 (mo_malloc MT k)).
{ apply (mo_ok_le MT MTL S2 (mo_malloc MT k) ((EV_LLVMF - 4 * Z.of_nat i) * MEV MT) MOK).
  unfold MEV, EV_LLVMF. clear - HM0 HF0 HMk Hi64. nia. }
(* the call chain: the entry's frame record at sp0, or none *)
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & ETop & _).
assert (HCH : exists ch, chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms)) (ms_regs ms) ch /\
  (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)])).
{ assert (Ura4 : 4096 <= raZ (ms_regs ms)) by (rewrite Ura; clear - HBLO; lia).
  change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; exists sp0, (s0Z (e_regs g)); reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0); [| rewrite Usp; clear - Hmf0; lia | exact Us0 | exact Ura4].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
      intros kk Hkk. apply KEEP1; clear - Hkk Hmf0 Hmfb H47 Hshi C1; lia.
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 16) (sp0 - 16) 8 (s0Z (e_regs g)));
      [|exact Vs0].
      intros kk Hkk. apply KEEP1; clear - Hkk Hmf0 Hmfb H47 Hshi C1; lia.
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. split; [|left; reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0 []); [| rewrite Usp; clear - Hmf0; lia | exact Us0 | exact Ura4].
    left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch & Hchain & Hchs).
(* ---- the malloc of the payload copy, 0x80c90 ---- *)
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W2 (ms_regs ms) (ms_mem ms) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i) k (mf - sp0)
    (Z_to_bv 64 (BASE + 0x520)) ch HJ).
  - exact Q10.
  - unfold MALLOC_MAX. clear - Hkr. lia.
  - exact Hlive.
  - rewrite Usp. ring.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK' Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hnev.
  - exact Hchain.
  - destruct Hchs as [-> | (fp & v & ->)].
    + eapply llvmf_univ_call0; [exact HUMM|].
      rewrite Ura. unfold LLVMF_MALLOC_CTX, LLVMF_MALLOC_RAS. cbn [map app]. right. left. reflexivity.
    + eapply llvmf_univ_call; [exact HUMM|].
      rewrite Ura. unfold LLVMF_MALLOC_CTX, LLVMF_MALLOC_RAS. cbn [map app]. left. reflexivity.
  - exact MOKm. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres4096 & Eab3 & HK3 & MLE3 & HJf).
clear HJf.
(* back at 0x80c94: only the machine-frame region survives the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 | clear - Hmfb; lia
  | clear - Hmfb HSTK' Has; lia | clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
(* ---- run 2: 0x80c94 .. the branch at 0x80c98 ---- *)
paj_run_sh mal_RUNP HS HJ3.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
  [reflexivity | rewrite ew_havoc_old by (cbv; lia); rewrite U9; ring
  | cbn [YP09.r_wlo]; clear - Hmfb HSTK' Has; lia | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
cbn [ms_mem mkst] in HF, HFr, HG.
(* what run 2 kept: every byte outside mf+112 .. mf+120 *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 120) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw.
  apply (kept_of_frame _ _ (w_H W3) mem3 (ms_mem ms0) (fun x => mf + 112 <= x < mf + 120) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. cbn in Hin.
  destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  rewrite ew_havoc_old in Hr by (cbv; lia); rewrite U9 in Hr; clear - Hr; lia. }
clear HF HFr HG.
(* the result and the length, as the environment after the call holds them *)
assert (E22 : ew (havoc E 512 (map (getr regs3) CLOB)) 22 = w64 k).
{ rewrite ew_havoc_old by (cbv; lia). rewrite (EE 22%nat 22%bv eq_refl). exact R22. }
assert (E516 : ew (havoc E 512 (map (getr regs3) CLOB)) 516 = w64 res).
{ rewrite <- Ha03. exact (ew_havoc_new E 512 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)). }
assert (Hres_in : In (res, k) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
pose proof HJ3 as (HAR3 & Hly3 & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 _ _ res k HAR3 Hres_in) as (_ & _ & Hrceil & Hrapp & Hrpres & _).
pose proof (req_size_pos k ltac:(clear - Hkr; lia)) as Hrqk.
(* ---- the frame, its shadow and the input block, and what the call kept of them ---- *)
pose proof HK3 as (K1 & K2 & K3 & K4 & _ & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _ & _ & ETop3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3, Hfrs; left; reflexivity).
assert (Hin4' : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (EFa2 : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF2; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ 4 pos HAR3 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms0) _ 4 pos HAR3 Hin4) as (HSF64 & _ & _).
rewrite EFa3 in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
assert (Hpin3 : In (e_p g, e_n g) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hinblk).
assert (HnotE : ~ In (res, k) (ablocks B (e_ly g) (e_S g))).
{ intros Hin.
  assert (Hin2 : In (res, k) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). cbn [app]. exact Hin. }
  apply in_split in Hin2 as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly3 S3) ((res, k) :: (res, k) :: l1 ++ l2)).
  { rewrite Eab3, El. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
    apply perm_skip. apply Permutation_sym, Permutation_middle. }
  pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ (res, k) (res, k) (l1 ++ l2) HAR3 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd Hrqk. lia. }
assert (Hpne : (e_p g, e_n g) <> (res, k)).
{ intros Heq. apply HnotE. rewrite <- Heq.
  destruct Hinp as [[Hz _] | [_ Hin]]; [clear - Hz Hn0; lia | exact Hin]. }
assert (DISJPB : e_p g + req_size (e_n g) <= res \/ res + req_size k <= e_p g).
{ pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ (e_p g) (e_n g) res k HAR3 Hpin3 Hres_in Hpne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd. lia. }
assert (DISJFB : forall a, SF <= a < SF + 1024 -> ~ (res <= a < res + req_size k)).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ res k 4 pos HAR3 Hres_in Hin4) as Hd.
  rewrite EFa3, HFB in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd. lia. }
assert (DISJSB : forall a, sh <= a < sh + 128 -> ~ (res <= a < res + req_size k)).
{ intros a Ha Hb. apply (fshadow_not_app SF 128 res (req_size k) a);
  [exact HSF0 | clear - HSF1 C1; lia | exact Hrapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia
  | exact Hb]. }
(* ---- the three transports from the start state to the state after the call ---- *)
assert (TRS : forall a, mf <= a < sp0 -> ~ (mf + 112 <= a < mf + 120) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite (KEEP2 a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia) Hw).
  rewrite (K1 a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia) ltac:(clear - Ha Has; lia)).
  apply KEEP1; [clear - Ha Hmf0 Hshi H47 C1; lia | exact Hw]. }
assert (TRF : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 128) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  rewrite (KEEP2 a ltac:(clear - Ha Hsh1 HSF0 HSF1 C1; lia) ltac:(clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0; lia)).
  rewrite (K4 4 pos a Hin4').
  - apply KEEP1; [clear - Ha Hsh1 HSF0 HSF1 C1; lia | clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0; lia].
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa2, HFB. fold sh.
    destruct Ha as [Ha | Ha]; [left | right]; clear - Ha; lia.
  - cbn beta. destruct Ha as [Ha | Ha]; [exact (DISJFB a Ha) | exact (DISJSB a Ha)]. }
assert (TRP : forall a, e_p g <= a < e_p g + req_size (e_n g) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  rewrite (KEEP2 a ltac:(clear - Ha Hp4096 Hpce C1; lia) ltac:(clear - Ha Hp4096 Hpce C1 Hmf0; lia)).
  replace a with (e_p g + (a - e_p g)) by ring.
  rewrite (K2 (e_p g) (e_n g) (a - e_p g) Hinblk ltac:(clear - Ha; lia) ltac:(cbn beta; clear - Ha DISJPB Hrq; lia)).
  apply KEEP1; [clear - Ha Hp4096 Hpce C1; lia | clear - Ha Hp4096 Hpce C1 Hmf0; lia]. }
psrr_branch_pi mal_RUNP BR HS.
- (* k = 0: the copy is skipped *)
  pose proof (mal_eq0 _ 22 k true E22 ltac:(clear - Hkr; lia) Hc) as Hk0. apply Z.eqb_eq in Hk0. clear Hc.
  paj_run_to_sh mal_RUNTOP HS HJ3 1352.
  { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite ew_havoc_old by (cbv; lia); rewrite U9; ring
    | cbn [YP09.r_wlo]; clear - Hmfb HSTK' Has; lia | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
  cbn [ms_mem mkst] in HF, HFr, HG.
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms0) a).
  { intros a Ha Hw.
    apply (kept_of_frame _ _ (w_H W3) (ms_mem ms0) (ms_mem ms1) (fun x => mf + 112 <= x < mf + 120) HFr);
    [|exact Ha|exact Hw].
    intros bb wlo whi aa Hin Hr. cbn in Hin.
    destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    rewrite ew_havoc_old in Hr by (cbv; lia); rewrite U9 in Hr; clear - Hr; lia. }
  clear HF HFr HG.
  assert (FS : forall a, mf <= a < sp0 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw. rewrite (KEEP4 a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia) Hw). apply TRS; assumption. }
  assert (FF : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 128) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite (KEEP4 a ltac:(clear - Ha Hsh1 HSF0 HSF1 C1; lia)
      ltac:(clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0; lia)). apply TRF; exact Ha. }
  assert (FP : forall a, e_p g <= a < e_p g + req_size (e_n g) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite (KEEP4 a ltac:(clear - Ha Hp4096 Hpce C1; lia)
      ltac:(clear - Ha Hp4096 Hpce C1 Hmf0; lia)). apply TRP; exact Ha. }
  (* the registers at 0x80cbc *)
  prreg HS (2%bv : bv 5) Y2. rewrite (EE 2%nat 2%bv eq_refl), Rsp in Y2.
  prreg HS (9%bv : bv 5) Y9. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Y9.
  prreg HS (8%bv : bv 5) Y8. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Y8.
  prreg HS (3%bv : bv 5) Y3. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Y3.
  prreg HS (4%bv : bv 5) Y4. rewrite (EE 4%nat 4%bv eq_refl), Rtp in Y4.
  prreg HS (18%bv : bv 5) Y18. rewrite (EE 18%nat 18%bv eq_refl), R18 in Y18.
  prreg HS (22%bv : bv 5) Y22. rewrite (EE 22%nat 22%bv eq_refl), R22 in Y22.
  prreg HS (23%bv : bv 5) Y23. unfold sh_reg in R23.
  rewrite (EE 23%nat 23%bv eq_refl), R23 in Y23.
  prreg HS (27%bv : bv 5) Y27. pose proof E516 as E516'.
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in E516'.
  rewrite E516' in Y27.
  (* the store at mf+112 *)
  pose proof (st_ok_region_nth _ _ _ 0%nat
    (YP09.mkRegion (Some 9%nat) 112 120 112 120 [YP09.mkChunk 112 (CVal 8 (SOff 19 0))]) HS eq_refl) as HRG.
  cbn [ms_mem restrict] in HRG.
  pose proof (SlotModel.rec_c_range inp (S i)) as Hcr1. rewrite Hnlen in Hcr1.
  assert (V112 : val_mem SEGS (rd W3 (ms_mem ms1)) (mf + 112) 8 (e_p g + m_cur g (S i))).
  { apply (field_of_region _ _ 9%nat mf [YP09.mkChunk 112 (CVal 8 (SOff 19 0))] 112 120 112 120 112 8%N
      (SOff 19 0) (e_p g + m_cur g (S i)) HRG).
    - rewrite ew_havoc_old by (cbv; lia). exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite (EE 19%nat 19%bv eq_refl), R19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold m_cur. fold inp. change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616.
      clear - Hcr1 Hp4096 Hpce Hrq C1. lia.
    - cbn. lia. }
  (* the payload: k = 0, so the block has no byte *)
  assert (HPL : bytes_at8 W3 (ms_mem ms1) res (SlotModel.rec_pl inp i)).
  { unfold bytes_at8. intros j Hj. exfalso. rewrite length_map in Hj.
    rewrite SlotModel.rec_pl_length in Hj. change (SlotModel.rec_k inp i) with k in Hj.
    rewrite Hk0 in Hj. cbn in Hj. clear - Hj. lia. }
  apply SRr_ret. pmkst HS. exists res.
  exact (mal_fin g pos mf i res ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 (ms_mem ms1) (ms_regs ms1) _
    HCC Hfrs Hi R19 Hstab V120 V128 Hid Hhw Hbl HJ3 Hfrs3 MLE MOK MLE3 Eab3 Hres4096
    FS FF FP Y2 Y9 Y8 Y3 Y4 Y18 Y22 Y23 Y27 V112 HPL).
- (* k <> 0 *)
  pose proof (mal_eq0 _ 22 k false E22 ltac:(clear - Hkr; lia) Hc) as Hk0. apply Z.eqb_neq in Hk0. clear Hc.
  paj_run_sh mal_RUNP HS HJ3.
  { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite ew_havoc_old by (cbv; lia); rewrite U9; ring
    | cbn [YP09.r_wlo]; clear - Hmfb HSTK' Has; lia | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms0) a).
  { intros a Ha Hw.
    apply (kept_of_frame _ _ (w_H W3) (ms_mem ms0) (ms_mem ms1) (fun x => mf + 112 <= x < mf + 120) HFr);
    [|exact Ha|exact Hw].
    intros bb wlo whi aa Hin Hr. cbn in Hin.
    destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    rewrite ew_havoc_old in Hr by (cbv; lia); rewrite U9 in Hr; clear - Hr; lia. }
  clear HF HFr HG.
  psrr_branch_pi mal_RUNP BR HS.
  2: { exfalso. pose proof (mal_ne0 _ 516 res false E516 ltac:(clear - Hres4096 Hrceil Hrqk C1; lia) Hc) as Hz.
       apply negb_false_iff, Z.eqb_eq in Hz. clear - Hz Hres4096. lia. }
  paj_run_shc mal_RUNP mal_RUNC HS HJ3.
  { eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite ew_havoc_old by (cbv; lia); rewrite U9; ring
    | cbn [YP09.r_wlo]; clear - Hmfb HSTK' Has; lia | cbn [YP09.r_whi]; clear - Hmfb; lia | apply awr_ok_nil]. }
  cbn [ms_mem mkst] in HF, HFr, HG.
  assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms1) a).
  { intros a Ha Hw.
    apply (kept_of_frame _ _ (w_H W3) (ms_mem ms1) (ms_mem ms2) (fun x => mf + 112 <= x < mf + 120) HFr);
    [|exact Ha|exact Hw].
    intros bb wlo whi aa Hin Hr. cbn in Hin.
    destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    rewrite ew_havoc_old in Hr by (cbv; lia); rewrite U9 in Hr; clear - Hr; lia. }
  clear HF HFr HG.
  (* the three transports up to the state at the copy *)
  assert (FS2 : forall a, mf <= a < sp0 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw. rewrite (KEEP5 a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia) Hw).
    rewrite (KEEP3 a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia) Hw). apply TRS; assumption. }
  assert (FF2 : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 128) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha.
    rewrite (KEEP5 a ltac:(clear - Ha Hsh1 HSF0 HSF1 C1; lia) ltac:(clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0; lia)).
    rewrite (KEEP3 a ltac:(clear - Ha Hsh1 HSF0 HSF1 C1; lia) ltac:(clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0; lia)).
    apply TRF; exact Ha. }
  assert (FP2 : forall a, e_p g <= a < e_p g + req_size (e_n g) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha.
    rewrite (KEEP5 a ltac:(clear - Ha Hp4096 Hpce C1; lia) ltac:(clear - Ha Hp4096 Hpce C1 Hmf0; lia)).
    rewrite (KEEP3 a ltac:(clear - Ha Hp4096 Hpce C1; lia) ltac:(clear - Ha Hp4096 Hpce C1 Hmf0; lia)).
    apply TRP; exact Ha. }
  (* the registers at the copy *)
  pose proof E516 as E516'.
  cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add] in E516'.
  prreg HS (10%bv : bv 5) P10. rewrite E516' in P10.
  prreg HS (11%bv : bv 5) P11. rewrite (EE 20%nat 20%bv eq_refl), R20 in P11.
  prreg HS (12%bv : bv 5) P12. rewrite (EE 22%nat 22%bv eq_refl), R22 in P12.
  prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2.
  prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
  prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
  prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in P8.
  prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in P9.
  prreg HS (18%bv : bv 5) P18. rewrite (EE 18%nat 18%bv eq_refl), R18 in P18.
  prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl), R22 in P22.
  prreg HS (23%bv : bv 5) P23. unfold sh_reg in R23.
  rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
  prreg HS (27%bv : bv 5) P27. rewrite E516' in P27.
  (* the store at mf+112, at the state the copy starts from *)
  pose proof (st_ok_region_nth _ _ _ 0%nat
    (YP09.mkRegion (Some 9%nat) 112 120 112 120 [YP09.mkChunk 112 (CVal 8 (SOff 19 0))]) HS eq_refl) as HRG.
  cbn [ms_mem restrict] in HRG.
  pose proof (SlotModel.rec_c_range inp (S i)) as Hcr1. rewrite Hnlen in Hcr1.
  assert (V112 : val_mem SEGS (rd W3 (ms_mem ms2)) (mf + 112) 8 (e_p g + m_cur g (S i))).
  { apply (field_of_region _ _ 9%nat mf [YP09.mkChunk 112 (CVal 8 (SOff 19 0))] 112 120 112 120 112 8%N
      (SOff 19 0) (e_p g + m_cur g (S i)) HRG).
    - rewrite ew_havoc_old by (cbv; lia). exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite (EE 19%nat 19%bv eq_refl), R19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold m_cur. fold inp. change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616.
      clear - Hcr1 Hp4096 Hpce Hrq C1. lia.
    - cbn. lia. }
  (* the premises of the copy *)
  pose proof HJ3 as (HARc & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 _ _ (e_p g) (e_n g) HARc Hpin3) as (_ & _ & _ & _ & Hppres & _).
  assert (Usp2 : spZ (ms_regs ms2) = mf).
  { unfold spZ. rewrite P2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA IB___asan_memcpy) AMEMCPY W3
      (ms_regs ms2) (ms_mem ms2) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
      ly3 S3 _ (4 * Z.of_nat i + 1) res (e_p g + bod) k (mf - sp0) (Z_to_bv 64 (BASE + 0x548)) HJ3).
    - exact P10.
    - exact P11.
    - exact P12.
    - clear - Hkr. lia.
    - clear - Hres4096. lia.
    - clear - Hres4096 Hrceil Hrqk C1. lia.
    - rewrite Usp2. ring.
    - clear - Hmf32 Hsp0al. lia.
    - clear - Hmfb. lia.
    - clear - Hmfb HSTK' Has Hes. lia.
    - exact P3.
    - exact P4.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right. right. left. exists res, k. split; [exact Hres_in|]. split; [exact HnotE|].
        clear - Ha Hrqk. lia.
      + clear - Ha Hres4096 Hrceil Hrqk Hmf0 Hes C1. lia.
    - apply (amem_range_sub_app res (req_size k) res k Hrapp Hrceil);
      [clear; lia | clear - Hrqk; lia | clear - Hkr; lia].
    - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ res k res k HARc Hres_in);
      [clear; lia | clear - Hrqk; lia].
    - intros Hk1.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ res k res k HARc Hres_in);
      [clear; lia | clear - Hrqk; lia | exact Hk1].
    - split; [clear - Hp4096 Hbod0; lia|].
      split; [clear - Hp4096 Hpce Hbodk Hbod0 Hkr Hrq C1; lia|].
      split.
      { intros a Ha. split.
        - apply (aview_some_of_apresent SEGS). apply (proj1 (Hppres a ltac:(clear - Ha Hbod0 Hbodk Hrq; lia))).
        - rewrite Usp2. clear - Ha Hp4096 Hpce Hrq Hbod0 Hbodk Hmf0 Hes C1. lia. }
      split; [clear - DISJPB Hbod0 Hbodk Hkr Hrq Hrqk; lia|].
      split.
      { apply (amem_range_sub_app (e_p g) (req_size (e_n g)) (e_p g + bod) k Hpapp Hpce);
        [clear - Hbod0; lia | clear - Hbodk Hrq; lia | clear - Hkr; lia]. }
      split.
      { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ (e_p g) (e_n g)
          (e_p g + bod) k HARc Hpin3); [clear - Hbod0; lia | clear - Hbodk Hrq; lia]. }
      intros Hk1.
      apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ (e_p g) (e_n g)
        (e_p g + bod) k HARc Hpin3); [clear - Hbod0; lia | clear - Hbodk Hrq; lia | exact Hk1]. }
  cbv beta. intros W4 c4 Hwle4 (-> & regsC & memC & mdC & -> & HJC & HPC & Ha0C & HcpC0 & HfrC & HprC & HsmC).
  assert (HcpC : forall ii, 0 <= ii < k ->
    aview SEGS (w_H W3) memC (res + ii) = aview SEGS (w_H W3) (ms_mem ms2) (e_p g + bod + ii)) by exact HcpC0.
  clear HcpC0.
  (* the three transports, all the way to the end of the stretch *)
  assert (FS : forall a, mf <= a < sp0 -> ~ (mf + 112 <= a < mf + 120) ->
    aview SEGS (w_H W3) memC a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw.
    rewrite (HfrC a ltac:(clear - Ha Hmf0 Hshi H47 C1; lia)
      ltac:(clear - Ha Hres4096 Hrceil Hrqk Hmf0 C1; lia) ltac:(clear - Ha Hes; lia)).
    apply FS2; assumption. }
  assert (FF : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 128) ->
    aview SEGS (w_H W3) memC a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha.
    rewrite (HfrC a ltac:(clear - Ha Hsh1 HSF0 HSF1 C1; lia)
      ltac:(destruct Ha as [Ha | Ha]; [pose proof (DISJFB a Ha) | pose proof (DISJSB a Ha)];
            clear - H Hrqk Hkr; lia)
      ltac:(clear - Ha Hsh1 HSF0 HSF1 C1 Hmf0 Hes; lia)).
    apply FF2; exact Ha. }
  assert (FP : forall a, e_p g <= a < e_p g + req_size (e_n g) ->
    aview SEGS (w_H W3) memC a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha.
    rewrite (HfrC a ltac:(clear - Ha Hp4096 Hpce C1; lia)
      ltac:(clear - Ha DISJPB Hrqk Hkr Hrq; lia)
      ltac:(clear - Ha Hp4096 Hpce C1 Hmf0 Hes; lia)).
    apply FP2; exact Ha. }
  (* the store survives the copy *)
  assert (V112C : val_mem SEGS (rd W3 memC) (mf + 112) 8 (e_p g + m_cur g (S i))).
  { apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms2) memC (mf + 112) (mf + 112) 8
      (e_p g + m_cur g (S i))); [|exact V112].
    intros kk Hkk. apply HfrC;
    [clear - Hkk Hmfb Hmf0 Hshi H47 C1; lia | clear - Hkk Hres4096 Hrceil Hrqk Hmf0 C1; lia
     | clear - Hkk Hes; lia]. }
  (* the copied bytes are the record's payload *)
  assert (HPL : bytes_at8 W3 memC res (SlotModel.rec_pl inp i)).
  { unfold bytes_at8. intros j Hj. rewrite length_map, SlotModel.rec_pl_length in Hj.
    change (SlotModel.rec_k inp i) with k in Hj.
    assert (Hjb : (Z.to_nat bod + j < length inp)%nat)
      by (clear - Hj Hbodk Hbod0 Hkr Hlen; lia).
    destruct (Hinb (Z.to_nat bod + j)%nat ltac:(rewrite length_map; exact Hjb)) as [Hv Hr].
    rewrite (mal_pl_nth inp i j ltac:(change (SlotModel.rec_k inp i) with k; exact Hj)).
    change (SlotModel.rec_body inp i) with bod. split; [|exact Hr].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 memC
      (e_p g + Z.of_nat (Z.to_nat bod + j)) (res + Z.of_nat j) 1
      (nth (Z.to_nat bod + j) (map (fun b : byte => bv_unsigned b) inp) 0)); [|exact Hv].
    intros kk Hkk. assert (Ekk : kk = 0) by (clear - Hkk; lia). subst kk.
    rewrite !Z.add_0_r.
    replace (e_p g + Z.of_nat (Z.to_nat bod + j)) with (e_p g + bod + Z.of_nat j) by (clear - Hbod0; lia).
    rewrite (HcpC (Z.of_nat j) ltac:(clear - Hj; lia)).
    apply FP2. clear - Hj Hbod0 Hbodk Hkr Hrq. lia. }
  (* the registers the copy kept *)
  assert (Y2 : getr regsC 2 = w64 mf)
    by (transitivity (getr (ms_regs ms2) 2); [exact (HPC 2 ltac:(unfold acallee_saved; lia)) | exact P2]).
  assert (Y9 : getr regsC 9 = w64 mf)
    by (transitivity (getr (ms_regs ms2) 9); [exact (HPC 9 ltac:(unfold acallee_saved; lia)) | exact P9]).
  assert (Y8 : getr regsC 8 = w64 sp0)
    by (transitivity (getr (ms_regs ms2) 8); [exact (HPC 8 ltac:(unfold acallee_saved; lia)) | exact P8]).
  assert (Y3 : getr regsC 3 = w64 (as_gp B))
    by (transitivity (getr (ms_regs ms2) 3); [exact (HPC 3 ltac:(unfold acallee_saved; lia)) | exact P3]).
  assert (Y4 : getr regsC 4 = w64 (as_tp B))
    by (transitivity (getr (ms_regs ms2) 4); [exact (HPC 4 ltac:(unfold acallee_saved; lia)) | exact P4]).
  assert (Y18 : getr regsC 18 = w64 (SlotModel.rec_addr inp i))
    by (transitivity (getr (ms_regs ms2) 18); [exact (HPC 18 ltac:(unfold acallee_saved; lia)) | exact P18]).
  assert (Y22 : getr regsC 22 = w64 k)
    by (transitivity (getr (ms_regs ms2) 22); [exact (HPC 22 ltac:(unfold acallee_saved; lia)) | exact P22]).
  assert (Y23 : getr regsC 23 = w64 (shadow_addr SF))
    by (transitivity (getr (ms_regs ms2) 23); [exact (HPC 23 ltac:(unfold acallee_saved; lia)) | exact P23]).
  assert (Y27 : getr regsC 27 = w64 res)
    by (transitivity (getr (ms_regs ms2) 27); [exact (HPC 27 ltac:(unfold acallee_saved; lia)) | exact P27]).
  apply SRr_ret. exists res.
  exact (mal_fin g pos mf i res ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 memC regsC mdC
    HCC Hfrs Hi R19 Hstab V120 V128 Hid Hhw Hbl HJC Hfrs3 MLE MOK MLE3 Eab3 Hres4096
    FS FF FP Y2 Y9 Y8 Y3 Y4 Y18 Y22 Y23 Y27 V112C HPL).
Qed.

(* ---- seg_D1, the stretch +0x548 .. +0x598: the `before` copy, the first reac_identity_ingest call ---- *)

(* A byte a region's chunk pins, as the shadow view reads it. *)
Lemma d1i_chunk_view : forall E (W : world SEGS) m base off (e : sv),
  YP09.chunk_ok SEGS E (mrestrict (w_H W) m) base (YP09.mkChunk off (CVal 1 e)) ->
  aview SEGS (w_H W) m (base + off) = Some (bv_unsigned (byte_of_word (sv_denot E e) 0)).
Proof.
intros E W m base off e Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. injection Hb1 as Hb1. subst b.
rewrite Z.add_0_r in Hb2. unfold aview. rewrite Hb2. reflexivity.
Qed.

(* Bytes known at one state, at another state that agrees on them. *)
Lemma d1i_garr8_move : forall (H H' : word -> bool) (m m' : word -> option byte) p p' L,
  (forall i, 0 <= i < Z.of_nat (length L) -> aview SEGS H' m' (p' + i) = aview SEGS H m (p + i)) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H' m') p' L.
Proof.
intros H H' m m' p p' L HK Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (p + Z.of_nat j) (p' + Z.of_nat j) 1 (nth j L 0)); [|exact Hv].
intros k Hk. replace (p' + Z.of_nat j + k) with (p' + (Z.of_nat j + k)) by lia.
replace (p + Z.of_nat j + k) with (p + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.

(* The record's address is a 16-bit field of the input. *)
Lemma d1i_addr_range : forall inp i, 0 <= SlotModel.rec_addr inp i < 65536.
Proof.
intros inp i. unfold SlotModel.rec_addr, SlotModel.rec_raw, SlotModel.h_raw, SlotModel.h_lo, SlotModel.h_hi,
SlotModel.pick, RcIdentModel.ADDR_FIRMWARE, RcIdentModel.ADDR_REAC_VERSION, RcIdentModel.ADDR_MODEL_NAME.
pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i)) as H1.
pose proof (SlotModel.inb_range inp (SlotModel.rec_c inp i + 1)) as H2.
destruct (_ =? 0); [clear; lia|]. destruct (_ =? 1); [clear; lia|]. destruct (_ =? 2); clear - H1 H2; lia.
Qed.

(* A 38-byte object whose five shadow cells are 0,0,0,0,6. *)
Lemma d1i_block_shadow38 : forall (W : world SEGS) m a s,
  a mod 8 = 0 -> s = SHADOW_OFF + a / 8 ->
  aview SEGS (w_H W) m s = Some 0 -> aview SEGS (w_H W) m (s + 1) = Some 0 ->
  aview SEGS (w_H W) m (s + 2) = Some 0 -> aview SEGS (w_H W) m (s + 3) = Some 0 ->
  aview SEGS (w_H W) m (s + 4) = Some 6 ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a 38.
Proof.
intros W m a s Ha Hs H0 H1 H2 H3 H4. split; [exact Ha|]. split; [clear; lia|].
intros j Hj. change ((38 + 7) / 8) with 5 in Hj. unfold shadow_of_addr. rewrite <- Hs.
change (38 / 8) with 4. change (38 mod 8) with 6.
assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj; lia).
destruct Hc as [E0 | [E0 | [E0 | [E0 | E0]]]]; subst j; cbn [Z.ltb Z.compare];
[rewrite Z.add_0_r; exact H0 | exact H1 | exact H2 | exact H3 | exact H4].
Qed.

(* A block's shadow and a cleared shadow, at a state that agrees on their cells. *)
Lemma d1i_bs_move : forall (W : world SEGS) m m' a n,
  (forall j, 0 <= j < (n + 7) / 8 ->
     aview SEGS (w_H W) m' (SHADOW_OFF + a / 8 + j) = aview SEGS (w_H W) m (SHADOW_OFF + a / 8 + j)) ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n ->
  block_shadow (aview SEGS (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' a n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros j Hj. unfold shadow_of_addr. rewrite (HK j Hj). exact (H3 j Hj).
Qed.
Lemma d1i_zs_move : forall (W : world SEGS) m m' a n,
  (forall j, 0 <= j < n / 8 ->
     aview SEGS (w_H W) m' (SHADOW_OFF + a / 8 + j) = aview SEGS (w_H W) m (SHADOW_OFF + a / 8 + j)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n ->
  zero_shadow (aview SEGS (w_H W) m') SHADOW_OFF a n.
Proof.
intros W m m' a n HK H j Hj. unfold shadow_of_addr. rewrite (HK j Hj). exact (H j Hj).
Qed.

(* The `hw` payload the record loop keeps is eight bytes. *)
Lemma d1i_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) &&
            (8 <=? SlotModel.rec_k inp i)) eqn:Hc; [|exact IH].
  apply andb_prop in Hc as [_ Hk8]. apply Z.leb_le in Hk8.
  rewrite length_firstn, SlotModel.rec_pl_length. clear - Hk8. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.

(* ---- the symbolic state at +0x548 ---------------------------------------------------------------- *)
(* Region 0: the two machine-frame pointer slots the stretch loads, base s1 (atom 9), read-only:
   mf+152 = &before and mf+184 = &id, both as the frame address (atom 32) plus the variable's offset.
   Region 1: the frame's shadow, base s7 (atom 23), writable on the five cells the stores hit. *)
Definition d1i_mf : YP09.region := YP09.mkRegion (Some 9%nat) 112 192 112 112
  [YP09.mkChunk 152 (CVal 8 (SOff 32 32)); YP09.mkChunk 184 (CVal 8 (SOff 32 352))].
Definition d1i_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 128 4 9 [].
Definition d1i_ss : sstate := mkSS 0x548 sr_atoms [d1i_mf; d1i_sh] None
  (mkFacts [(23%nat, mkAF SB (2 ^ 47) 0)] [] []).
(* The stretch makes no checked access: no shadow entry, and a span the frame's shadow window is apart from. *)
Definition d1i_Bx : sv := SLit SB.
Definition d1i_Bspan : Z * Z := (0, 0).

Lemma d1_c2_c3 : forall g pos mf i pl W2 c2, d1_C2 g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (d1_C3 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & (Hbl & Hplb & V112 & V120 & V128 & (V96 & Hfix & Hbef & Hagn & Hmid)) &
  R18 & R22 & R27 & R23 & Hid & Hhw).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : SB <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. unfold SB. lia. }
assert (Hsh2 : 0 <= sh /\ sh + 128 <= alloc_ceiling) by (clear - Hsh1 C1; unfold SB in Hsh1; lia).
assert (Hshapp : forall a, sh <= a < sh + 128 -> ~ (SF <= a < SF + 1024)).
{ intros a Ha Hb. apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia
  | exact HSFapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | exact Hb]. }
(* the environment: atom 32 = the frame address *)
remember (Eimg (Ereg regs2 [w64 SF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 [w64 SF]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = w64 SF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U32 : bv_unsigned (ew E 32) = SF)
  by (rewrite E32; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U23 : bv_unsigned (ew E 23) = sh).
{ rewrite (EE 23%nat 23%bv eq_refl), R23. apply unsigned_lit_small. clear - Hsh2 C1. lia. }
(* the symbolic state *)
assert (HS : st_ok_pi SEGS VAL E d1i_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x548)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1i_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1i_mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 32 32) (SF + 32));
        [cbn [sv_denot]; rewrite U32; reflexivity | clear - HSF0 HSF1 C1; lia | clear; lia | exact Hbef].
      * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 352) (SF + 352));
        [cbn [sv_denot]; rewrite U32; reflexivity | clear - HSF0 HSF1 C1; lia | clear; lia | exact Hmid].
    + unfold d1i_sh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [clear - Hsh2; lia|]. split; [clear - Hsh2 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 1) (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1i_mf, d1i_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U23. right. clear - Hsh2 Hmf0. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    split; [clear - Hsh1 C1; lia|].
    split; [reflexivity | clear; lia]. }
assert (SHOK : sh_ok SEGS d1i_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x548)) with (Z_to_bv 64 (BASE + 0x548)).
paj_run_tok RUN HS HJ SHOK d1i_Bspan.
{ intros a (r & Hin & Hr). cbn [ss_mem d1i_ss In] in Hin.
  destruct Hin as [<- | [<- | []]];
  unfold d1i_mf, d1i_sh in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [clear - Hr; lia|].
  rewrite U23 in Hr. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Hr. lia. }
(* what run 1 kept: every byte outside the five shadow cells *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 9) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E (ss_mem d1i_ss) (w_H W2) mem2 (ms_mem ms)
    (fun x => sh + 4 <= x < sh + 9) HFr); [| exact Ha | exact Hw].
  intros bb wlo whi aa Hin Hr. unfold d1i_ss in Hin.
  cbn [ss_mem windows map d1i_mf d1i_sh YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [clear - Hr; lia | rewrite U23 in Hr; clear - Hr; lia]. }
(* the five shadow cells the stores set: `before` is no longer poisoned *)
destruct (st_ok_mem_ok SEGS E _ _ HS) as (_ & HRO & _).
cbn [restrict ms_mem setpc ss_mem] in HRO.
pose proof (Forall_inv (Forall_inv_tail HRO)) as HshR.
destruct HshR as (_ & _ & _ & HCH).
cbn [YP09.r_chunks YP09.r_base base_val] in HCH. rewrite U23 in HCH.
pose proof (Forall_inv HCH) as HC8. pose proof (Forall_inv_tail HCH) as HCHa.
pose proof (Forall_inv HCHa) as HC7. pose proof (Forall_inv_tail HCHa) as HCHb.
pose proof (Forall_inv HCHb) as HC6. pose proof (Forall_inv_tail HCHb) as HCHc.
pose proof (Forall_inv HCHc) as HC5. pose proof (Forall_inv_tail HCHc) as HCHd.
pose proof (Forall_inv HCHd) as HC4. clear HCH HCHa HCHb HCHc HCHd HRO.
assert (SH8 : aview SEGS (w_H W2) (ms_mem ms) (sh + 8) = Some 6).
{ rewrite (d1i_chunk_view E W2 (ms_mem ms) sh 8 (SLit 6) HC8). f_equal; vm_compute; reflexivity. }
assert (SH7 : aview SEGS (w_H W2) (ms_mem ms) (sh + 7) = Some 0).
{ rewrite (d1i_chunk_view E W2 (ms_mem ms) sh 7 (SLit 0) HC7). f_equal; vm_compute; reflexivity. }
assert (SH6 : aview SEGS (w_H W2) (ms_mem ms) (sh + 6) = Some 0).
{ rewrite (d1i_chunk_view E W2 (ms_mem ms) sh 6 (SLit 0) HC6). f_equal; vm_compute; reflexivity. }
assert (SH5 : aview SEGS (w_H W2) (ms_mem ms) (sh + 5) = Some 0).
{ rewrite (d1i_chunk_view E W2 (ms_mem ms) sh 5 (SLit 0) HC5). f_equal; vm_compute; reflexivity. }
assert (SH4 : aview SEGS (w_H W2) (ms_mem ms) (sh + 4) = Some 0).
{ rewrite (d1i_chunk_view E W2 (ms_mem ms) sh 4 (SLit 0) HC4). f_equal; vm_compute; reflexivity. }
(* `before`'s shadow now says: 38 live bytes *)
assert (BSB : sh_blk W2 (ms_mem ms) (SF + 32) N_before).
{ apply (d1i_block_shadow38 W2 (ms_mem ms) (SF + 32) (sh + 4));
  [clear - HSF64; lia | clear - Esh HSF64; clearbody sh; lia
  | exact SH4
  | replace (sh + 4 + 1) with (sh + 5) by (clear; lia); exact SH5
  | replace (sh + 4 + 2) with (sh + 6) by (clear; lia); exact SH6
  | replace (sh + 4 + 3) with (sh + 7) by (clear; lia); exact SH7
  | replace (sh + 4 + 4) with (sh + 8) by (clear; lia); exact SH8]. }
(* the write right and the presence of every byte of the frame *)
assert (AWF : forall a, SF <= a < SF + 1024 ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. exact Ha. }
assert (APR : forall a, SF <= a < SF + 1024 -> apresent (w_H W2) (ms_mem ms) a).
{ intros a Ha. exact (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat i + 1) a HJ (AWF a Ha))). }
(* `id`'s shadow, carried over run 1 *)
assert (BSI : sh_blk W2 (ms_mem ms) (SF + V_id) N_id).
{ apply (d1i_bs_move W2 mem2 (ms_mem ms)); [|exact (proj2 (proj2 Hid))].
  intros j Hj. unfold shadow_of_addr. apply KEEP1;
  [clear - Esh HSF0 HSF1 C1 Hsh2 Hj; unfold V_id, N_id in *; clearbody sh SF; lia
  | clear - Esh HSF64 Hj; unfold V_id, N_id in *; clearbody sh SF; lia]. }
(* the registers the call reads *)
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4.
assert (Psp : spZ (ms_regs ms) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite P2. rewrite unsigned_lit_small by (clear - Hmf0 H47 Hmfb Hshi C1; lia). clear; lia. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA IB___asan_memcpy) AMEMCPY W2 (ms_regs ms)
    (ms_mem ms) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _
    (4 * Z.of_nat i + 1) (SF + 32) (SF + V_id) 38 (mf - sp0) (Z_to_bv 64 (BASE + 0x574)) HJ).
  - rewrite P10. rewrite U32. reflexivity.
  - rewrite P11. rewrite U32. unfold V_id. reflexivity.
  - rewrite P12. reflexivity.
  - clear; lia.
  - clear - HSF0; lia.
  - clear - HSF1 C1; lia.
  - exact Psp.
  - clear - Hmf32 Hsp0al; lia.
  - clear - Hmfb; lia.
  - clear - Hmfb HSTK' Hes Has; lia.
  - exact P3.
  - exact P4.
  - exact P1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros a Ha. split; [apply AWF; clear - Ha HSF0; lia|].
    clear - Ha HSF1 Hmf0 Hes C1. lia.
  - apply (amem_range_sub_app SF 1024 (SF + 32) 38);
    [exact HSFapp | clear - HSF1; lia | clear; lia | clear; lia | clear; lia].
  - apply (block_shadow_range _ SHADOW_OFF (SF + 32) N_before); [exact BSB | clear; lia | unfold N_before; clear; lia].
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms));
    [exact (proj1 HJ) | exact Hin4 | rewrite EFa; clear; lia | rewrite EFa, HFB; clear; lia | clear; lia].
  - cbn beta. split; [clear - HSF0; unfold V_id; lia|].
    split; [clear - HSF1 C1; unfold V_id; lia|].
    split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent SEGS). apply APR. clear - Ha; unfold V_id in *; lia.
      - rewrite Psp. clear - Ha HSF1 Hmf0 Hes C1; unfold V_id in *; lia. }
    split; [unfold V_id; clear; lia|].
    split; [apply (amem_range_sub_app SF 1024 (SF + V_id) 38);
      [exact HSFapp | clear - HSF1; lia | unfold V_id; clear; lia | unfold V_id; clear; lia | clear; lia]|].
    split.
    { apply (block_shadow_range _ SHADOW_OFF (SF + V_id) N_id); [exact BSI | clear; lia | unfold N_id; clear; lia]. }
    intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms));
    [exact (proj1 HJ) | exact Hin4 | rewrite EFa; unfold V_id; clear; lia
    | rewrite EFa, HFB; unfold V_id; clear; lia | clear; lia]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & Ha03 & HEFF & HFR3 & HPRES3 & HSAME3).
(* back at +0x574: no region survives the call, the four moves that follow read none *)
let K := run_K_hi HS in jafter_call_keep_hi HS K regs3 (mrestrict (w_H W2) mem3) HPR3 (@nil nat) HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [constructor | specialize (HS3 HQ); clear HQ] end.
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI3 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (SHOK3 : sh_ok SEGS d1i_Bx (@nil shent) Ev (mrestrict (w_H W2) mem3)) by constructor end.
clear HEI0 SHOK.
paj_run_to_tok RUNTO HS HJ3 SHOK3 d1i_Bspan 0x584.
{ intros a (r & Hin & _). destruct Hin. }
(* ---- what the three steps kept ---- *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr0);
  [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. cbn [ss_mem windows map] in Hin. destruct Hin. }
assert (KEEPG : forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 32 <= a < SF + 70) -> ~ (mf - 4096 <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) (ms_mem ms) a).
{ intros a Ha H2 H3. rewrite (KEEP2 a Ha).
  apply (HFR3 a Ha ltac:(clear - H2; lia) ltac:(clear - H3 Hes; lia)). }
assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 9) -> ~ (SF + 32 <= a < SF + 70) ->
  ~ (mf - 4096 <= a < mf) -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (KEEPG a Ha H2 H3). apply KEEP1; assumption. }
(* the machine frame and the saved words *)
assert (MFK : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H0 H1 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) a a n v); [|exact Hv].
  intros k Hkk. apply KEEPF;
  [clear - H0 H1 Hkk Hmf0 Hshi H47 C1; lia | clear - H0 H1 Hkk Hmf0 Hsh2 C1; lia
  | clear - H0 H1 Hkk Hmf0 HSF1 C1; lia | clear - H0 H1 Hkk; lia]. }
(* the frame, above `before` *)
assert (FRK : forall off (n : nat) v, 70 <= off -> off + Z.of_nat n <= 1024 ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 (ms_mem ms0)) (SF + off) n v).
{ intros off n v H0 H1 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) (SF + off) (SF + off) n v); [|exact Hv].
  intros k Hkk. apply KEEPF.
  - clear - H0 H1 Hkk HSF0 HSF1 C1. lia.
  - intros Hx. apply (Hshapp (SF + off + k)); [clear - Hx Hsh2; lia | clear - H0 H1 Hkk; lia].
  - clear - H0 H1 Hkk. lia.
  - clear - H0 H1 Hkk HSF1 Hmf0 C1. lia. }
assert (GFK : forall off l, 70 <= off -> off + Z.of_nat (length l) <= 1024 ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W2 (ms_mem ms0)) (SF + off) l).
{ intros off l H0 H1 Hg. apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms0) (SF + off) (SF + off)); [|exact Hg].
  intros k Hkk. apply KEEPF.
  - clear - H0 H1 Hkk HSF0 HSF1 C1. lia.
  - intros Hx. apply (Hshapp (SF + off + k)); [clear - Hx Hsh2; lia | clear - H0 H1 Hkk; lia].
  - clear - H0 H1 Hkk. lia.
  - clear - H0 H1 Hkk HSF1 Hmf0 C1. lia. }
(* the frame's shadow, above `before`'s cells *)
assert (SHK : forall c, 9 <= c < 128 ->
  aview SEGS (w_H W2) (ms_mem ms0) (sh + c) = aview SEGS (w_H W2) mem2 (sh + c)).
{ intros c Hc. apply KEEPF; [clear - Hc Hsh2 C1; lia | clear - Hc; lia
  | intros Hx; apply (Hshapp (sh + c)); [clear - Hc; lia | clear - Hx; lia]
  | clear - Hc Hsh2 Hmf0 C1; lia]. }
assert (SHG : forall c, 0 <= c < 128 ->
  aview SEGS (w_H W2) (ms_mem ms0) (sh + c) = aview SEGS (w_H W2) (ms_mem ms) (sh + c)).
{ intros c Hc. apply KEEPG; [clear - Hc Hsh2 C1; lia
  | intros Hx; apply (Hshapp (sh + c)); [clear - Hc; lia | clear - Hx; lia]
  | clear - Hc Hsh2 Hmf0 C1; lia]. }
(* the heap blocks of the state *)
assert (HBK : forall b m a, In (b, m) (ablocks B ly2 S2) -> b <= a < b + m ->
  0 <= a < 2 ^ 64 /\ ~ (sh + 4 <= a < sh + 9) /\ ~ (SF + 32 <= a < SF + 70) /\ ~ (mf - 4096 <= a < mf)).
{ intros b m a Hin Ha.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & Hb0 & Hbce & Hbapp & _ & _ & Hbn).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR2 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa, HFB in Hd.
  pose proof (req_size_pos m (proj1 Hbn)) as [_ Hrq].
  split; [clear - Ha Hb0 Hbce Hrq C1; lia|].
  split; [intros Hx; apply (fshadow_not_app SF 128 b (req_size m) a);
    [clear - HSF0; lia | clear - HSF1 C1; lia | exact Hbapp
    | rewrite Esh in Hx; unfold SHADOW_OFF in Hx; clear - Hx; lia | clear - Ha Hrq; lia]|].
  split; [clear - Ha Hd Hrq; lia | clear - Ha Hbce Hrq Hmf0 C1; lia]. }
assert (GBK : forall b m l, In (b, m) (ablocks B ly2 S2) -> Z.of_nat (length l) <= m ->
  garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W2 (ms_mem ms0)) b l).
{ intros b m l Hin Hl Hg. apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms0) b b); [|exact Hg].
  intros k Hkk. destruct (HBK b m (b + k) Hin ltac:(clear - Hkk Hl; lia)) as (A1 & A2 & A3 & A4).
  apply KEEPF; assumption. }
(* the two live blocks *)
assert (Hinpl : In (pl, SlotModel.rec_k inp i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
assert (Hne : inp <> []).
{ intros E0. unfold m_nrec in Hi. fold inp in Hi. rewrite E0 in Hi.
  change (SlotModel.nrecn []) with 0%nat in Hi. clear - Hi. lia. }
assert (Hn0 : 0 < e_n g).
{ rewrite Hlen. destruct inp as [|b l]; [exfalso; exact (Hne eq_refl)|]. cbn [length]. clear; lia. }
assert (Hinblk : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  cbn [app]. right. destruct Hinp as [[Hz _] | [_ Hin]]; [clear - Hz Hn0; lia | exact Hin]. }
(* `id` and `before` after the copy *)
assert (BID : bytes_at8 W2 (ms_mem ms) (SF + V_id) (m_id g i)).
{ unfold bytes_at8 in *. apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms) (SF + V_id) (SF + V_id)); [|exact (proj1 Hid)].
  intros k Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  apply KEEP1; [clear - Hkk HSF0 HSF1 C1; unfold V_id, RcIdentModel.ID_SIZE in *; lia|].
  intros Hx. apply (Hshapp (SF + V_id + k)); [clear - Hx Hsh2; lia
  | clear - Hkk; unfold V_id, RcIdentModel.ID_SIZE in *; lia]. }
assert (BBEF : bytes_at8 W2 (ms_mem ms0) (SF + V_before) (m_id g i)).
{ unfold bytes_at8, V_before in *.
  apply (d1i_garr8_move (w_H W2) (w_H W2) (ms_mem ms) (ms_mem ms0) (SF + V_id) (SF + 32)); [|exact BID].
  intros k Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  change (Z.of_nat RcIdentModel.ID_SIZE) with 38 in Hkk.
  rewrite (KEEP2 (SF + 32 + k) ltac:(clear - Hkk HSF0 HSF1 C1; lia)).
  apply HEFF. clear - Hkk. lia. }
assert (BSB2 : sh_blk W2 (ms_mem ms0) (SF + V_before) N_before).
{ unfold sh_blk, V_before in *. apply (d1i_bs_move W2 (ms_mem ms) (ms_mem ms0)); [|exact BSB].
  intros j Hj. change ((N_before + 7) / 8) with 5 in Hj.
  replace (SHADOW_OFF + (SF + 32) / 8 + j) with (sh + (4 + j))
    by (clear - Esh HSF64 Hj; clearbody sh SF; lia).
  apply SHG. clear - Hj. lia. }
(* the registers at +0x584 *)
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 18%nat 18%bv eq_refl), R18 in Q11, Q18.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q12, Q27.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Q13, Q22.
rewrite (EE 23%nat 23%bv eq_refl), R23 in Q23.
rewrite U32 in Q10, Q19.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
(* ---- the boundary d1_C3 at +0x584 ---- *)
apply SRr_ret. unfold d1_C3, acut. pmkst HS.
exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [exact HJ3|].
split; [exact Hfrs|].
split; [exact Hk|].
split; [exact MLE|].
split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W24]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W32]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W40]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W48]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W56]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W64]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W72]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W80]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W88]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W96]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W104]|].
  split; [apply FRK; [clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold bytes_at8 in *. apply (GBK (e_p g) (e_n g)); [exact Hinblk | | exact Hinb].
  rewrite length_map. try fold inp. rewrite <- Hlen. apply Z.le_refl. }
(* d1_C3's own facts *)
split; [exact Hi|].
split.
{ split; [exact Hbl|].
  split.
  { unfold bytes_at8 in *. apply (GBK pl (SlotModel.rec_k inp i)); [exact Hinpl | | exact Hplb].
    rewrite length_map, SlotModel.rec_pl_length. try fold inp.
    pose proof (SlotModel.rec_k_range inp i) as Hkr. rewrite Z2Nat.id by (clear - Hkr; lia).
    apply Z.le_refl. }
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split.
  { destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
    unfold mf_fixed.
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F32]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F48]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F56]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F72]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F80]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F88]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F104]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F136]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F144]|].
    apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F160]. }
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hbef]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hagn]|].
  apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]. }
change (SFa g pos) with SF.
split; [rewrite Q10; unfold V_id; reflexivity|].
split; [exact Q11|].
split; [exact Q12|].
split; [exact Q13|].
split; [exact Q18|].
split; [exact Q22|].
split; [exact Q27|].
split; [rewrite Q19; unfold V_id; reflexivity|].
split; [unfold sh_reg; rewrite Q23; reflexivity|].
split.
{ destruct Hid as (Hidb & Hidz & Hidk). change (SFa g pos) with SF in Hidb, Hidz, Hidk.
  unfold id_at. change (SFa g pos) with SF.
  split.
  { unfold bytes_at8 in *. apply (GFK V_id); [unfold V_id; clear; lia | | exact Hidb].
    rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
    unfold V_id, RcIdentModel.ID_SIZE. clear; lia. }
  split.
  { unfold sh_zero in *. apply (d1i_zs_move W2 mem2 (ms_mem ms0)); [|exact Hidz].
    intros j Hj. change (N_id / 8) with 4 in Hj.
    replace (SHADOW_OFF + (SF + V_id) / 8 + j) with (sh + (44 + j))
      by (clear - Esh HSF64 Hj; unfold V_id; clearbody sh SF; lia).
    apply SHK. clear - Hj. lia. }
  unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hidk].
  intros j Hj. change ((N_id + 7) / 8) with 5 in Hj.
  replace (SHADOW_OFF + (SF + V_id) / 8 + j) with (sh + (44 + j))
    by (clear - Esh HSF64 Hj; unfold V_id; clearbody sh SF; lia).
  apply SHK. clear - Hj. lia. }
split.
{ destruct Hhw as ((Hhwb & Hhwz & Hhwk) & Hhw4 & Hhw24).
  change (SFa g pos) with SF in Hhwb, Hhwz, Hhwk, Hhw4.
  replace (SF + V_hw + 4) with (SF + 436) in Hhwb by (unfold V_hw; clear; lia).
  unfold hw_live, hw_mem. change (SFa g pos) with SF.
  replace (SF + V_hw + 4) with (SF + 436) by (unfold V_hw; clear; lia).
  split.
  { split.
    { unfold bytes_at8 in *. apply (GFK 436); [clear; lia | | exact Hhwb].
      rewrite length_map. unfold m_hwb. rewrite d1i_hwb_length. clear; lia. }
    split.
    { unfold sh_zero in *. apply (d1i_zs_move W2 mem2 (ms_mem ms0)); [|exact Hhwz].
      intros j Hj. change (N_hw / 8) with 1 in Hj.
      replace (SHADOW_OFF + (SF + V_hw) / 8 + j) with (sh + (54 + j))
        by (clear - Esh HSF64 Hj; unfold V_hw; clearbody sh SF; lia).
      apply SHK. clear - Hj. lia. }
    unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hhwk].
    intros j Hj. change ((N_hw + 7) / 8) with 2 in Hj.
    replace (SHADOW_OFF + (SF + V_hw) / 8 + j) with (sh + (54 + j))
      by (clear - Esh HSF64 Hj; unfold V_hw; clearbody sh SF; lia).
    apply SHK. clear - Hj. lia. }
  split; [apply (FRK V_hw); [unfold V_hw; clear; lia | unfold V_hw; clear; lia | exact Hhw4]|].
  apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hhw24]. }
split; [exact BBEF | exact BSB2].
Qed.

(* ---- seg_D1, the stretch +0x584 .. +0x598: the first reac_identity_ingest call ---- *)

(* Bytes a list of bytes holds, from the walk's byte form. *)
Lemma d1j_mbytes_of_bytes8 : forall m a (bs : list byte),
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) bs) -> mbytes_at SEGS m a bs.
Proof.
intros m a bs Hg j Hj.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
rewrite (garr8_mbyte SEGS m a _ j Hg Hj').
rewrite (nth_error_nth' bs (RcIdentModel.zb 0) Hj). f_equal.
replace (nth j (map (fun b : byte => bv_unsigned b) bs) 0)
  with (bv_unsigned (nth j bs (RcIdentModel.zb 0)))
  by (symmetry; apply (map_nth (fun b : byte => bv_unsigned b) bs (RcIdentModel.zb 0) j)).
apply Z_to_bv_bv_unsigned.
Qed.
(* and back *)
Lemma d1j_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
intros b. unfold YO0f.le_byte. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr.
replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. apply Z_to_bv_bv_unsigned.
Qed.
Lemma d1j_bytes8_of_mbytes : forall m a (bs : list byte),
  mbytes_at SEGS m a bs -> garr8 SEGS m a (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros m a bs Hm j Hj. rewrite length_map in Hj.
replace (nth j (map (fun b : byte => bv_unsigned b) bs) 0)
  with (bv_unsigned (nth j bs (RcIdentModel.zb 0)))
  by (symmetry; apply (map_nth (fun b : byte => bv_unsigned b) bs (RcIdentModel.zb 0) j)).
pose proof (bv_unsigned_in_range 8 (nth j bs (RcIdentModel.zb 0))) as Hr.
change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by (clear - Hkk; lia). subst kk.
replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by (clear; lia).
rewrite (Hm j Hj), (nth_error_nth' bs (RcIdentModel.zb 0) Hj). f_equal.
symmetry. apply d1j_le_byte1.
Qed.

(* The symbolic state at +0x584: the call reads no memory the walk must know. *)
Definition d1j_ss : sstate := mkSS 0x584 sr_atoms [] None (mkFacts [] [] []).

Lemma d1_c3_c4 : forall g pos mf i pl W2 c2, d1_C3 g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (d1_C4 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & (Hbl & Hplb & V112 & V120 & V128 & (V96 & Hfix & Hbef & Hagn & Hmid)) &
  R10 & R11 & R12 & R13 & R18 & R22 & R27 & R19 & R23 & Hid & Hhw & Hbefb & Hbefs).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
set (inp := e_pl g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : SB <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. unfold SB. lia. }
assert (Hsh2 : 0 <= sh /\ sh + 128 <= alloc_ceiling) by (clear - Hsh1 C1; unfold SB in Hsh1; lia).
assert (Hshapp : forall a, sh <= a < sh + 128 -> ~ (SF <= a < SF + 1024)).
{ intros a Ha Hb. apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia
  | exact HSFapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | exact Hb]. }
(* the two live blocks and the model's bounds *)
assert (Hinpl : In (pl, SlotModel.rec_k inp i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl (SlotModel.rec_k inp i) HAR2 Hinpl)
  as (_ & Hpl0 & Hplce & Hplapp & _ & _ & Hpln).
pose proof (SlotModel.rec_k_range inp i) as Hkr.
destruct (req_size_pos (SlotModel.rec_k inp i) ltac:(clear - Hkr; lia)) as [Hrq1 Hrq2].
pose proof (d1i_addr_range inp i) as Har.
assert (Hi64 : Z.of_nat i < 64).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp in Hi.
  pose proof (SlotModel.nrec_range inp) as Hnr. clear - Hi Hnr. lia. }
(* the write right and the presence of every byte of the frame *)
assert (AWF : forall a, SF <= a < SF + 1024 ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. exact Ha. }
assert (APR : forall a, SF <= a < SF + 1024 -> apresent (w_H W2) mem2 a).
{ intros a Ha. eapply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 _ (4 * Z.of_nat i + 1) a HJ (AWF a Ha))). }
(* the environment and the state at the call *)
remember (Eimg (Ereg regs2 (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 (@nil word)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E d1j_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x584)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1j_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS d1i_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x584)) with (Z_to_bv 64 (BASE + 0x584)).
paj_run_tok RUN HS HJ SHOK d1i_Bspan.
{ intros a (r & Hin & _). destruct Hin. }
(* the step kept every byte *)
assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E (ss_mem d1j_ss) (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr);
  [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. unfold d1j_ss in Hin. cbn [ss_mem windows map] in Hin. destruct Hin. }
assert (APR2 : forall a, SF <= a < SF + 1024 -> apresent (w_H W2) (ms_mem ms) a).
{ intros a Ha. eapply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g)
    (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat i + 1) a HJ (AWF a Ha))). }
(* `id` at the call state *)
destruct Hid as (Hidb & Hidz & Hidk). change (SFa g pos) with SF in Hidb, Hidz, Hidk.
assert (BID : bytes_at8 W2 (ms_mem ms) (SF + V_id) (m_id g i)).
{ unfold bytes_at8 in *.
  apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms) (SF + V_id) (SF + V_id)); [|exact Hidb].
  intros kk Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  change (Z.of_nat RcIdentModel.ID_SIZE) with 38 in Hkk.
  apply KEEPJ. clear - Hkk HSF0 HSF1 C1. unfold V_id. lia. }
assert (BIDK : sh_blk W2 (ms_mem ms) (SF + V_id) N_id).
{ unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms)); [|exact Hidk].
  intros j Hj. apply KEEPJ. clear - Hj Esh HSF0 HSF1 C1 Hsh2. unfold V_id, N_id in *.
  clearbody sh SF. lia. }
assert (BPL : bytes_at8 W2 (ms_mem ms) pl (SlotModel.rec_pl inp i)).
{ unfold bytes_at8 in *.
  apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms) pl pl); [|exact Hplb].
  intros kk Hkk. rewrite length_map, SlotModel.rec_pl_length in Hkk.
  rewrite Z2Nat.id in Hkk by (clear - Hkr; lia).
  apply KEEPJ. clear - Hkk Hpl0 Hplce Hkr Hrq1 Hrq2 C1. lia. }
(* the registers the call reads *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in P2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in P3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in P4. rewrite (EE 10%nat 10%bv eq_refl), R10 in P10.
rewrite (EE 11%nat 11%bv eq_refl), R11 in P11. rewrite (EE 12%nat 12%bv eq_refl), R12 in P12.
rewrite (EE 13%nat 13%bv eq_refl), R13 in P13.
assert (Psp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite P2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Pra : raZ (ms_regs ms) = BASE + 1416).
{ unfold raZ. rewrite P1. apply unsigned_lit_small. clear - HBASE. lia. }
pmkst HS. rewrite (PSIG IB_reac_identity_ingest AF_reac_identity_ingest eq_refl).
eapply SRr_bind.
{ eapply (HING LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2
    (ms_mem ms) _ (4 * Z.of_nat i + 1) (ms_regs ms)
    (SF + V_id) (SlotModel.rec_addr inp i) pl (SlotModel.rec_k inp i)
    (m_id g i) (SlotModel.rec_pl inp i) HJ).
  - rewrite P1. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite Pra. clear - HBLO. lia.
  - exact P10.
  - exact P11.
  - exact P12.
  - exact P13.
  - clear - HSF0 HSF1 C1. unfold V_id. lia.
  - exact Har.
  - clear - Hpl0 Hplce C1 Hrq1. lia.
  - clear - Hkr. lia.
  - rewrite Psp. clear - Hmf32. lia.
  - rewrite Psp. unfold reac_identity_ingest.INGEST_STK.
    clear - Hmfb HSTK' Hes Has. lia.
  - rewrite Psp. clear - Hmfb. lia.
  - apply SlotModel.rec_pl_length.
  - intros _. split.
    + unfold reac_identity_ingest.ting_rec_ok. split; [clear - HSF64; unfold V_id; lia|].
      split; [left; exists 4, pos; split; [exact Hin4|];
        intros a Ha; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa, HFB;
        clear - Ha HSF0; unfold V_id in *; lia|].
      split; [rewrite Psp; right; clear - HSF1 Hmf0 Hes C1; unfold V_id, reac_identity_ingest.INGEST_STK; lia|].
      split; [intros a Ha; split; [apply AWF | apply APR2]; clear - Ha HSF0; unfold V_id in *; lia|].
      split.
      { apply (block_shadow_range _ SHADOW_OFF (SF + V_id) N_id);
        [exact BIDK | clear; lia | unfold N_id; clear; lia]. }
      split; [unfold m_id; apply SlotModel.rec_id_length|].
      apply d1j_mbytes_of_bytes8. exact BID.
    + unfold reac_identity_ingest.ting_pay_ok. split.
      { intros _. exists pl, (SlotModel.rec_k inp i). split; [exact Hinpl|]. clear; lia. }
      apply d1j_mbytes_of_bytes8. exact BPL.
  - unfold reac_identity_ingest.EV_INGEST.
    pose proof HEV as HEV'. unfold EV_LLVMF in HEV'.
    clear - Hnev2 Hnev0 HEV' Hi64. unfold EV_MAX in *. lia.
  - unfold reac_identity_ingest.LIVE_INGEST.
    pose proof (wf_live _ _ _ _ _ (am_wf B ly2 S2 _ (proj1 HAR2))) as HLB. clear - HLB. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HPR3 & Ha03 & HKEPT3 & HID3).
(* the call is not refused: the record's address is the frame's, the payload is a live block *)
assert (REF : reac_identity_ingest_c.ingest_refused (SF + V_id) pl (SlotModel.rec_k inp i) = false).
{ unfold reac_identity_ingest_c.ingest_refused. apply orb_false_intro.
  - apply Z.eqb_neq. clear - HSF0. unfold V_id. lia.
  - apply andb_false_iff. right. apply Z.eqb_neq. clear - Hpl0. lia. }
unfold reac_identity_ingest_c.ingest_ret in Ha03. rewrite REF in Ha03.
change (RcIdentModel.ING (m_id g i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i)).1
  with (SlotModel.rec_r inp i) in Ha03.
pose proof (HID3 REF) as HIDN. clear HID3.
replace (4 * Z.of_nat i + 1 + reac_identity_ingest.EV_INGEST) with (4 * Z.of_nat i + 1) in HJ3
  by (unfold reac_identity_ingest.EV_INGEST; clear; lia).
rewrite Psp in HKEPT3.
destruct HKEPT3 as (K1 & K2 & _ & K4 & _ & _).
assert (HnotE : forall a, ~ (SF + V_id <= a < SF + V_id + 38) ->
  ~ reac_identity_ingest.ting_E (SF + V_id) pl (SlotModel.rec_k inp i) a).
{ intros a Ha (_ & Hx). exact (Ha Hx). }
rewrite P1.
(* back at +0x588: no region, and a0 is the model's result *)
let K := run_K_hi HS in jafter_call_keep_hi HS K regs3 (mrestrict (w_H W2) mem3) HPR3 (@nil nat) HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [constructor | specialize (HS3 HQ); clear HQ] end.
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI3 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (SHOK3 : sh_ok SEGS d1i_Bx (@nil shent) Ev (mrestrict (w_H W2) mem3)) by constructor;
  assert (E516 : ew Ev 516 = getr regs3 10%bv)
    by (exact (ew_havoc_new E 512 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia))) end.
clear HEI0 SHOK.
(* the result is 0 or 1, so the abort branch is not taken *)
pose proof (SlotModel.rec_r_range inp i) as Hrr.
apply (st_ok_pi_add_fact _ _ _ 516%nat (mkAF 0 1 0)) in HS.
2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E516, Ha03.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    rewrite unsigned_lit_small by (clear - Hrr; lia).
    split; [clear - Hrr; lia|]. split; [reflexivity | clear; lia]. }
paj_run_to_tok RUNTO HS HJ3 SHOK3 d1i_Bspan 0x598.
{ intros a (r & Hin & _). destruct Hin. }
(* ---- what the call and the two steps kept ---- *)
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr0);
  [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. cbn [ss_mem add_atom windows map] in Hin. destruct Hin. }
assert (STK2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - 4128 <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite (KEEP4 a ltac:(clear - Ha C1; lia)).
  rewrite (K1 a Ha ltac:(unfold reac_identity_ingest.INGEST_STK; clear - Hw Hes; lia)
    (HnotE a ltac:(clear - Ha HSF1; unfold V_id; lia))).
  apply KEEPJ. clear - Ha C1. lia. }
assert (FRM2 : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 128) -> ~ (SF + V_id <= a < SF + V_id + 38) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (KEEP4 a ltac:(clear - Ha HSF0 HSF1 Hsh2 C1; lia)).
  rewrite (K4 4 pos a Hin4); [| | exact (HnotE a Hn)].
  - apply KEEPJ. clear - Ha HSF0 HSF1 Hsh2 C1. lia.
  - unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFa, HFB. fold sh. exact Ha. }
assert (BLK2 : forall b m j, In (b, m) (ablocks B ly2 S2) -> 0 <= j < req_size m ->
  aview SEGS (w_H W2) (ms_mem ms0) (b + j) = aview SEGS (w_H W2) mem2 (b + j)).
{ intros b m j Hin Hj.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & Hb0 & Hbce & _ & _ & _ & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR2 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa, HFB in Hd.
  rewrite (KEEP4 (b + j) ltac:(clear - Hj Hb0 Hbce C1; lia)).
  rewrite (K2 b m j Hin Hj (HnotE (b + j) ltac:(clear - Hj Hd; unfold V_id; lia))).
  apply KEEPJ. clear - Hj Hb0 Hbce C1. lia. }
assert (MFK : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H0 H1 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) a a n v); [|exact Hv].
  intros kk Hkk. apply STK2; [clear - H0 H1 Hkk Hmf0 Hshi H47 C1; lia | clear - H0 H1 Hkk; lia]. }
assert (FRK : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= 352 \/ 390 <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 (ms_mem ms0)) (SF + off) n v).
{ intros off n v H0 H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply FRM2; [left; clear - H0 H1 Hkk; lia | clear - H2 Hkk; unfold V_id; lia]. }
assert (GFK : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  (off + Z.of_nat (length l) <= 352 \/ 390 <= off) ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W2 (ms_mem ms0)) (SF + off) l).
{ intros off l H0 H1 H2 Hg.
  apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms0) (SF + off) (SF + off)); [|exact Hg].
  intros kk Hkk. apply FRM2; [left; clear - H0 H1 Hkk; lia | clear - H2 Hkk; unfold V_id; lia]. }
assert (SHK : forall c, 0 <= c < 128 ->
  aview SEGS (w_H W2) (ms_mem ms0) (sh + c) = aview SEGS (w_H W2) mem2 (sh + c)).
{ intros c Hc. apply FRM2; [right; clear - Hc; lia|].
  intros Hx. apply (Hshapp (sh + c)); [clear - Hc; lia | clear - Hx; unfold V_id in Hx; lia]. }
assert (GBK : forall b m l, In (b, m) (ablocks B ly2 S2) -> 0 <= m -> Z.of_nat (length l) <= m ->
  garr8 SEGS (rd W2 mem2) b l -> garr8 SEGS (rd W2 (ms_mem ms0)) b l).
{ intros b m l Hin Hm Hl Hg. apply (d1i_garr8_move (w_H W2) (w_H W2) mem2 (ms_mem ms0) b b); [|exact Hg].
  intros kk Hkk. apply (BLK2 b m kk Hin). pose proof (req_size_pos m Hm) as [_ Hrq].
  clear - Hkk Hl Hrq. lia. }
assert (Hne : inp <> []).
{ intros E0. unfold m_nrec in Hi. fold inp in Hi. rewrite E0 in Hi.
  change (SlotModel.nrecn []) with 0%nat in Hi. clear - Hi. lia. }
assert (Hn0 : 0 < e_n g).
{ rewrite Hlen. destruct inp as [|b l]; [exfalso; exact (Hne eq_refl)|]. cbn [length]. clear; lia. }
assert (Hinblk : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  cbn [app]. right. destruct Hinp as [[Hz _] | [_ Hin]]; [clear - Hz Hn0; lia | exact Hin]. }
(* the new record *)
assert (BIDN : bytes_at8 W2 (ms_mem ms0) (SF + V_id) (m_id g (S i))).
{ change (m_id g (S i)) with
    ((RcIdentModel.ING (m_id g i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i)).2).
  unfold bytes_at8.
  apply (d1i_garr8_move (w_H W2) (w_H W2) mem3 (ms_mem ms0) (SF + V_id) (SF + V_id));
  [|exact (d1j_bytes8_of_mbytes _ _ _ HIDN)].
  intros kk Hkk. apply KEEP4. rewrite length_map in Hkk.
  assert (HL : length (RcIdentModel.ING (m_id g i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i)).2
    = RcIdentModel.ID_SIZE).
  { change ((RcIdentModel.ING (m_id g i) (SlotModel.rec_addr inp i) (SlotModel.rec_pl inp i)).2)
      with (SlotModel.rec_id inp (S i)). apply SlotModel.rec_id_length. }
  rewrite HL in Hkk. change (Z.of_nat RcIdentModel.ID_SIZE) with 38 in Hkk.
  clear - Hkk HSF0 HSF1 C1. unfold V_id. lia. }
(* the registers at +0x598 *)
prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
prreg HS (23%bv : bv 5) Q23. prreg HS (27%bv : bv 5) Q27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 18%nat 18%bv eq_refl), R18 in Q18.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Q10, Q22.
rewrite (EE 23%nat 23%bv eq_refl), R23 in Q23.
cbn [nth map CLOB] in Q20. rewrite Ha03 in Q20.
rewrite unsigned_lit_small in Q10 by (clear - Hkr; lia).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
(* ---- the boundary d1_C4 at +0x598 ---- *)
apply SRr_ret. unfold d1_C4, acut. pmkst HS.
exists ly2, S2, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [exact HJ3|].
split; [exact Hfrs|].
split; [exact Hk|].
split; [exact MLE|].
split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W24]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W32]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W40]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W48]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W56]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W64]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W72]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W80]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W88]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W96]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact W104]|].
  split; [apply FRK; [clear; lia | clear; lia | right; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold bytes_at8 in *. apply (GBK (e_p g) (e_n g)); [exact Hinblk | clear - Hn0; lia | | exact Hinb].
  rewrite length_map. try fold inp. rewrite <- Hlen. apply Z.le_refl. }
(* d1_C4's own facts *)
split; [exact Hi|].
split.
{ split; [exact Hbl|].
  split.
  { unfold bytes_at8 in *. apply (GBK pl (SlotModel.rec_k inp i)); [exact Hinpl | clear - Hkr; lia | | exact Hplb].
    rewrite length_map, SlotModel.rec_pl_length. try fold inp.
    rewrite Z2Nat.id by (clear - Hkr; lia). apply Z.le_refl. }
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split.
  { destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
    unfold mf_fixed.
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F32]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F48]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F56]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F72]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F80]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F88]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F104]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F136]|].
    split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F144]|].
    apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact F160]. }
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hbef]|].
  split; [apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hagn]|].
  apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]. }
change (SFa g pos) with SF.
split; [exact Q10|].
split; [exact Q18|].
split; [exact Q20|].
split; [exact Q22|].
split; [exact Q27|].
split; [unfold sh_reg; rewrite Q23; reflexivity|].
split.
{ unfold id_at. change (SFa g pos) with SF.
  split; [exact BIDN|].
  split.
  { unfold sh_zero in *. apply (d1i_zs_move W2 mem2 (ms_mem ms0)); [|exact Hidz].
    intros j Hj. change (N_id / 8) with 4 in Hj.
    replace (SHADOW_OFF + (SF + V_id) / 8 + j) with (sh + (44 + j))
      by (clear - Esh HSF64 Hj; unfold V_id; clearbody sh SF; lia).
    apply SHK. clear - Hj. lia. }
  unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hidk].
  intros j Hj. change ((N_id + 7) / 8) with 5 in Hj.
  replace (SHADOW_OFF + (SF + V_id) / 8 + j) with (sh + (44 + j))
    by (clear - Esh HSF64 Hj; unfold V_id; clearbody sh SF; lia).
  apply SHK. clear - Hj. lia. }
split.
{ destruct Hhw as ((Hhwb & Hhwz & Hhwk) & Hhw4 & Hhw24).
  change (SFa g pos) with SF in Hhwb, Hhwz, Hhwk, Hhw4.
  replace (SF + V_hw + 4) with (SF + 436) in Hhwb by (unfold V_hw; clear; lia).
  unfold hw_live, hw_mem. change (SFa g pos) with SF.
  replace (SF + V_hw + 4) with (SF + 436) by (unfold V_hw; clear; lia).
  split.
  { split.
    { unfold bytes_at8 in *. apply (GFK 436); [clear; lia | | | exact Hhwb];
      rewrite length_map; unfold m_hwb; rewrite d1i_hwb_length; clear; lia. }
    split.
    { unfold sh_zero in *. apply (d1i_zs_move W2 mem2 (ms_mem ms0)); [|exact Hhwz].
      intros j Hj. change (N_hw / 8) with 1 in Hj.
      replace (SHADOW_OFF + (SF + V_hw) / 8 + j) with (sh + (54 + j))
        by (clear - Esh HSF64 Hj; unfold V_hw; clearbody sh SF; lia).
      apply SHK. clear - Hj. lia. }
    unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hhwk].
    intros j Hj. change ((N_hw + 7) / 8) with 2 in Hj.
    replace (SHADOW_OFF + (SF + V_hw) / 8 + j) with (sh + (54 + j))
      by (clear - Esh HSF64 Hj; unfold V_hw; clearbody sh SF; lia).
    apply SHK. clear - Hj. lia. }
  split; [apply (FRK V_hw); [unfold V_hw; clear; lia | unfold V_hw; clear; lia
    | right; unfold V_hw; clear; lia | exact Hhw4]|].
  apply MFK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hhw24]. }
split.
{ change (SFa g pos) with SF in Hbefb. unfold bytes_at8, V_before in *.
  apply (GFK 32); [clear; lia | | | exact Hbefb];
  rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length;
  change (Z.of_nat RcIdentModel.ID_SIZE) with 38; clear; lia. }
split.
{ change (SFa g pos) with SF in Hbefs. unfold sh_blk, V_before in *.
  apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hbefs].
  intros j Hj. change ((N_before + 7) / 8) with 5 in Hj.
  replace (SHADOW_OFF + (SF + 32) / 8 + j) with (sh + (4 + j))
    by (clear - Esh HSF64 Hj; clearbody sh SF; lia).
  apply SHK. clear - Hj. lia. }
unfold sh_blk in *. apply (d1i_bs_move W2 mem2 (ms_mem ms0)); [|exact Hidk].
intros j Hj. change ((N_id + 7) / 8) with 5 in Hj.
replace (SHADOW_OFF + (SF + V_id) / 8 + j) with (sh + (44 + j))
  by (clear - Esh HSF64 Hj; unfold V_id; clearbody sh SF; lia).
apply SHK. clear - Hj. lia.
Qed.

(* The stretch +0x548 .. +0x598 as one lemma: the two halves chained at d1_C3 (+0x584). *)
Lemma d1_c2_c4 : forall g pos mf i pl W2 c2, d1_C2 g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (d1_C4 g pos mf i pl).
Proof.
intros g pos mf i pl W2 c2 H.
eapply SRr_bind; [exact (d1_c2_c3 g pos mf i pl W2 c2 H)|].
intros W3 c3 _ H3. exact (d1_c3_c4 g pos mf i pl W3 c3 H3).
Qed.

Section h.
Lemma d1g_garr8_moved : forall H H' (m m' : word -> option byte) a b l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (b + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') b l.
Proof.
intros H H' m m' a b l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (b + Z.of_nat j + kk) with (b + (Z.of_nat j + kk)) by lia.
replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.
Lemma d1g_bytes_moved : forall (W W' : world SEGS) mem mem' a b l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W') mem' (b + k) = aview SEGS (w_H W) mem (a + k)) ->
  bytes_at8 W mem a l -> bytes_at8 W' mem' b l.
Proof.
intros W W' mem mem' a b l Hk H. unfold bytes_at8 in *.
apply (d1g_garr8_moved (w_H W) (w_H W') mem mem' a b); [|exact H].
rewrite length_map. exact Hk.
Qed.
Lemma d1g_shblk_moved : forall (W W' : world SEGS) mem mem' a n,
  (forall j, 0 <= j < (n + 7) / 8 -> aview SEGS (w_H W') mem' (shadow_of_addr SHADOW_OFF a + j) =
     aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF a + j)) ->
  sh_blk W mem a n -> sh_blk W' mem' a n.
Proof. intros W W' mem mem' a n Hk H. unfold sh_blk in *. exact (block_shadow_agree _ _ _ _ _ Hk H). Qed.
Lemma d1g_shzero_moved : forall (W W' : world SEGS) mem mem' a n,
  (forall j, 0 <= j < n / 8 -> aview SEGS (w_H W') mem' (shadow_of_addr SHADOW_OFF a + j) =
     aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF a + j)) ->
  sh_zero W mem a n -> sh_zero W' mem' a n.
Proof. intros W W' mem mem' a n Hk Hz j Hj. unfold sh_zero, zero_shadow in *. rewrite (Hk j Hj). exact (Hz j Hj). Qed.
Lemma d1g_aview_some : forall H mem a v, val_mem SEGS (mrestrict H mem) a 1 v -> aview SEGS H mem a <> None.
Proof.
intros H mem a v Hv. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. discriminate.
Qed.
Lemma d1g_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
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
Lemma d1g_sh_off : forall p c, p mod 8 = 0 -> shadow_of_addr SHADOW_OFF (p + c) = shadow_addr p + c / 8.
Proof. intros p c Hp. rewrite shadow_of_addr_aligned_off by exact Hp. reflexivity. Qed.
End h.

Lemma d1g_ecommon_moved : forall g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  (forall a, mf <= a < e_sp0 g -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, SFa g pos + 1016 <= a < SFa g pos + 1024 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall j, 0 <= j < e_n g -> aview SEGS (w_H W3) mem3 (e_p g + j) = aview SEGS (w_H W2) mem2 (e_p g + j)) ->
  m_fds md3 = m_fds (e_md g) -> m_fs md3 = m_fs (e_md g) ->
  ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HC E2 E9 E8 E3 E4 KM KFl KIn Hfd Hfs.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs0 & Hinb).
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _).
assert (VA : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= e_sp0 g ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 mem3) a n v).
{ intros a n v H0 H1 Hv. apply (val_mem_kept SEGS (w_H W2) (w_H W3) mem2 mem3 a n v); [|exact Hv].
  intros kk Hkk. apply KM. lia. }
unfold ecommon. rewrite E2, E9, E8, E3, E4.
split; [exact Rsp|]. split; [exact Rs1|]. split; [exact Rs0|]. split; [exact Hmfb|]. split; [exact Hmf32|].
split; [exact Rgp|]. split; [exact Rtp|].
do 17 (split; [apply VA; [lia | cbn; lia | assumption] |]).
split.
{ apply (val_mem_kept SEGS (w_H W2) (w_H W3) mem2 mem3 _ 8 _); [|exact Vflag].
  intros kk Hkk. apply KFl. cbn in Hkk. lia. }
split; [exact HPRE|].
split; [intros fd; rewrite Hfd; reflexivity|].
split; [exact Hfs|].
apply (d1g_bytes_moved W2 W3 mem2 mem3 (e_p g) (e_p g) (e_pl g)); [|exact Hinb].
intros kk Hkk. apply KIn. lia.
Qed.


Lemma d1g_val : forall (W W' : world SEGS) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  val_mem SEGS (rd W mem) a n v -> val_mem SEGS (rd W' mem') a n v.
Proof.
intros W W' mem mem' a n v K H. apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem' a n v); [|exact H].
intros kk Hkk. apply K. lia.
Qed.
Lemma d1g_fbytes : forall (W W' : world SEGS) mem mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  bytes_at8 W mem a l -> bytes_at8 W' mem' a l.
Proof.
intros W W' mem mem' a l K H. apply (d1g_bytes_moved W W' mem mem' a a l); [|exact H].
intros kk Hkk. apply K. lia.
Qed.
Lemma d1g_fshblk : forall (W W' : world SEGS) mem mem' a n,
  (forall x, shadow_of_addr SHADOW_OFF a <= x < shadow_of_addr SHADOW_OFF a + (n + 7) / 8 ->
     aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  sh_blk W mem a n -> sh_blk W' mem' a n.
Proof.
intros W W' mem mem' a n K H. apply (d1g_shblk_moved W W' mem mem' a n); [|exact H].
intros j Hj. apply K. lia.
Qed.
Lemma d1g_fshzero : forall (W W' : world SEGS) mem mem' a n,
  (forall x, shadow_of_addr SHADOW_OFF a <= x < shadow_of_addr SHADOW_OFF a + n / 8 ->
     aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  sh_zero W mem a n -> sh_zero W' mem' a n.
Proof.
intros W W' mem mem' a n K H. apply (d1g_shzero_moved W W' mem mem' a n); [|exact H].
intros j Hj. apply K. lia.
Qed.
Lemma d1g_id_moved : forall g pos j (W W' : world SEGS) mem mem',
  SFa g pos mod 64 = 0 ->
  (forall x, SFa g pos + 352 <= x < SFa g pos + 390 -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  (forall x, shadow_addr (SFa g pos) + 44 <= x < shadow_addr (SFa g pos) + 49 ->
     aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  id_at g pos j W mem -> id_at g pos j W' mem'.
Proof.
intros g pos j W W' mem mem' H64 KF KSx (Hb & Hz & Hk). unfold id_at, V_id, N_id in *.
assert (Hl : length (m_id g j) = 38%nat) by (unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Es : shadow_of_addr SHADOW_OFF (SFa g pos + 352) = shadow_addr (SFa g pos) + 44)
  by (rewrite d1g_sh_off by lia; reflexivity).
split; [|split].
- apply (d1g_fbytes W W' mem mem' _ _); [|exact Hb]. rewrite Hl. intros x Hx. apply KF. lia.
- apply (d1g_fshzero W W' mem mem' _ 38); [|exact Hz]. rewrite Es. intros x Hx. apply KSx. lia.
- apply (d1g_fshblk W W' mem mem' _ 38); [|exact Hk]. rewrite Es. intros x Hx. apply KSx. lia.
Qed.
Lemma d1g_hw_moved : forall g pos mf j (W W' : world SEGS) mem mem',
  SFa g pos mod 64 = 0 ->
  (forall x, SFa g pos + 432 <= x < SFa g pos + 444 -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  (forall x, shadow_addr (SFa g pos) + 54 <= x < shadow_addr (SFa g pos) + 56 ->
     aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  (forall x, mf + 24 <= x < mf + 32 -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  hw_live g pos mf j W mem -> hw_live g pos mf j W' mem'.
Proof.
intros g pos mf j W W' mem mem' H64 KF KSx KM ((Hb & Hz & Hk) & Hv & Hm). unfold hw_live, hw_mem, V_hw, N_hw in *.
assert (Hl : length (m_hwb g j) = 8%nat) by (unfold m_hwb; apply d1g_hwb_length).
assert (Es : shadow_of_addr SHADOW_OFF (SFa g pos + 432) = shadow_addr (SFa g pos) + 54)
  by (rewrite d1g_sh_off by lia; reflexivity).
split; [split; [|split]|split].
- apply (d1g_fbytes W W' mem mem' _ _); [|exact Hb]. rewrite Hl. intros x Hx. apply KF. lia.
- apply (d1g_fshzero W W' mem mem' _ 12); [|exact Hz]. rewrite Es. intros x Hx. apply KSx. lia.
- apply (d1g_fshblk W W' mem mem' _ 12); [|exact Hk]. rewrite Es. intros x Hx. apply KSx. lia.
- apply (d1g_val W W' mem mem' _ 4 0); [|exact Hv]. intros x Hx. apply KF. cbn in Hx. lia.
- apply (d1g_val W W' mem mem' _ 8 _); [|exact Hm]. intros x Hx. apply KM. cbn in Hx. lia.
Qed.
Lemma d1g_stab_moved : forall g pos mf (W W' : world SEGS) mem mem',
  (forall x, mf + 32 <= x < mf + 192 -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  d1_stab g pos mf W mem -> d1_stab g pos mf W' mem'.
Proof.
intros g pos mf W W' mem mem' KM H. unfold d1_stab, mf_fixed, mf_before, mf_again, mf_id in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; (apply (d1g_val W W' mem mem'); [intros x Hx; apply KM; cbn in Hx; lia | assumption]).
Qed.
Lemma d1g_shoff_frame : forall g pos c, SFa g pos mod 64 = 0 -> 0 <= c ->
  shadow_of_addr SHADOW_OFF (SFa g pos + c) = shadow_addr (SFa g pos) + c / 8.
Proof. intros g pos c H64 Hc. apply d1g_sh_off. lia. Qed.
Lemma d1_c4_c5 : forall g pos mf i pl W2 c2, d1_C4 g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists gb, d1_C5 g pos mf i pl gb W3 c3).
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & _ & Vra & Vs0 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
destruct HP as (Hi & Hpl & R10 & R18 & R20 & R22 & R27 & R23 & Hid & Hhw & Hbef & Hsbef & Hsid).
pose proof Hpl as (Hbl & Hplb & V112 & V120 & V128 & Hstab).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HBS : buf_of.BUF_OF_STK = 16 + ASTACK) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & Hlive0 & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh1 : kLowMemEnd <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= kHighShadowEnd).
{ rewrite Esh, C2, C5. unfold SHADOW_OFF. clear - HSF0 HSF1 C1. lia. }
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
set (nrec := SlotModel.nrec inp) in *.
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
pose proof (SlotModel.nrec_range inp) as Hnr. fold nrec in Hnr.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp nrec in Hi. clear - Hi Hnr. lia. }
remember (Eimg (Ereg regs2 [w64 SB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x598 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x598)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - unfold facts_ok. cbn. repeat split. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x598)) with (Z_to_bv 64 (BASE + 0x598)).
paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_nil|].
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10.
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite Q2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Ura : raZ (ms_regs ms) = BASE + 1436).
{ unfold raZ. rewrite Q1. apply unsigned_lit_small. clear - HBASE. lia. }
assert (HCH : exists ch, achain ly2 (aview SEGS (w_H W2) (ms_mem ms)) mf sp0 ch /\
  (ch = [] \/ exists v, ch = [(sp0, RA_LLVMF, v)])).
{ change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach0 : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; eexists; reflexivity].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach0).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
      intros kk Hkk. apply KEEP0. clear - Hkk Hmf0 Hmfb H47 Hshi C1. lia.
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 16) 8 (s0Z (e_regs g))); [|exact Vs0].
      intros kk Hkk. apply KEEP0. clear - Hkk Hmf0 Hmfb H47 Hshi C1. lia.
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. split; [|left; reflexivity]. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch & Hach & Hchs).
assert (Hnev : st_nev S2 + buf_of.EV_BUF_OF <= EV_MAX).
{ unfold buf_of.EV_BUF_OF. unfold EV_LLVMF in HEV. clear - Hnev2 Hnev0 HEV Hi64. lia. }
assert (Hlive : blocks_bytes S2 + Z.max (k + 1) 1 <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2). destruct Hbl as [Hperm _]. rewrite (bsum_perm _ _ Hperm).
  rewrite (blocks_bytes_bsum B (e_ly g) (e_S g)) in Hlive0. cbn [app]. rewrite bsum_cons. cbn [fst snd].
  unfold LIVE_LLVMF in HLIVE. clear - Hlive0 HLIVE Hkr. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL (Z.max (k + 1) 1) 256 ltac:(clear - Hkr; lia)) as HMm.
assert (MOKm : mo_ok MT S2 (mo_malloc MT (Z.max (k + 1) 1))).
{ apply (mo_ok_le MT MTL S2 _ _ MOK). unfold MEV, EV_LLVMF. clear - HM0 HF0 HMm Hi64. nia. }
assert (HCTX : In (raZ (ms_regs ms) :: spine ch) (CTX_BUF_OF RA_LLVMF)).
{ rewrite Ura. destruct Hchs as [-> | (v & ->)]; cbn [spine map fst snd];
  unfold CTX_BUF_OF, BUF_OF_RAS; apply in_or_app; [right | left]; apply in_map_iff; exists 0x59c;
  (split; [reflexivity | cbn; left; reflexivity]). }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W2 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_buf_of)) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 1)
    buf_of.BUF_OF_STK [] buf_of.EV_BUF_OF (mf - sp0) (Z_to_bv 64 (BASE + 1436)) ch
    (fun ly' S' (_ : world SEGS) regs' (_ : word -> option byte) (_ : Model) => exists res : Z,
       getr regs' 10 = w64 res /\ 4096 <= res /\ frames S' = frames S2 /\
       ablocks B ly' S' = ablocks B ly2 S2 ++ [(res, Z.max (k + 1) 1)] /\
       mo_le MT S2 S' (mo_malloc MT (Z.max (k + 1) 1))) HJ).
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - rewrite HBS, Has. lia.
  - rewrite HBS. clear - Hmfb HSTK' Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - replace (sp0 + (mf - sp0)) with mf by lia. rewrite Us0. exact Hach.
  - intros HPRE'. eapply SRr_mono.
    { exact (HBUF ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ ch (k + 1) HPRE' HCTX Q10
        ltac:(unfold MALLOC_MAX; clear - Hkr; lia) Hnev Hlive MOKm). }
    intros W' c' _ Hp. unfold buf_of.tbuf_of_post, apost_base in Hp.
    destruct Hp as (ly' & S' & regs' & mem' & md' & Hc' & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Q1 in Hc'. split; [exact Hc'|]. split; [exact HJ'|].
    split; [exact HP'|]. exact HK'.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & (gb & Rres & Hgb4 & Hfrs3 & Eab3 & MLE3)).
replace (Z.max (k + 1) 1) with (k + 1) in * by (clear - Hkr; lia).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hgbin : In (gb, k + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 gb (k + 1) HAR3 Hgbin) as (_ & _ & Hgbce & Hgbapp & _).
pose proof (req_size_pos (k + 1) ltac:(clear - Hkr; lia)) as Hrq.
assert (HnotE2 : ~ In (gb, k + 1) (ablocks B ly2 S2)).
{ intros Hin. apply in_split in Hin as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly3 S3) ((gb, k + 1) :: (gb, k + 1) :: l1 ++ l2)).
  { rewrite Eab3, El, <- app_assoc. cbn [app].
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
    rewrite app_assoc. apply Permutation_sym, Permutation_cons_append. }
  pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 mem3 md3 _ _ _ HAR3 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd Hrq. lia. }
assert (HnotE : ~ In (gb, k + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. apply HnotE2. destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. right. exact Hin. }
assert (Hin43 : In (4, pos) (frames S3)) by (rewrite Hfrs3; exact Hin4).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 gb (k + 1) 4 pos HAR3 Hgbin Hin43) as Hgbf.
unfold zdisjoint in Hgbf. cbn [fst snd] in Hgbf. rewrite EFa3, HFB in Hgbf.
assert (Hplin2 : In (pl, k) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. left. reflexivity. }
assert (Hplin3 : In (pl, k) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hplin2).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl k HAR2 Hplin2) as (_ & Hpl4 & Hplce & Hplapp & _).
pose proof (req_size_pos k ltac:(clear - Hkr; lia)) as Hrqk.
assert (Hgbpl : gb + req_size (k + 1) <= pl \/ pl + req_size k <= gb).
{ assert (Hne : (gb, k + 1) <> (pl, k)) by (intros Heq; injection Heq as _ Hx; clear - Hx; lia).
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 gb (k + 1) pl k HAR3 Hgbin Hplin3 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
assert (KM3 : forall a, mf <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite (G1 a) by (clear - Ha Hmf0 C1; lia). apply KEEP0. clear - Ha Hmf0 C1. lia. }
assert (KFR3 : forall a, SFa g pos <= a < SFa g pos + 1024 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite (G4 4 pos a Hin4).
  - apply KEEP0. clear - Ha HSF0 HSF1 C1. lia.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. clear - Ha. lia.
  - intros (r & Hr & _). destruct Hr. }
assert (KSH3 : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite (G4 4 pos a Hin4).
  - apply KEEP0. clear - Ha Hsh1 C2 C5. lia.
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. clear - Ha. lia.
  - intros (r & Hr & _). destruct Hr. }
assert (KBL3 : forall p n j, In (p, n) (ablocks B ly2 S2) -> 0 <= j < req_size n ->
  aview SEGS (w_H W3) mem3 (p + j) = aview SEGS (w_H W2) mem2 (p + j)).
{ intros p n j Hin Hj. destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4 & Hpce & _).
  assert (Hin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hin).
  rewrite (G2 p n j Hin Hin3 Hj) by (intros (r & Hr & _); destruct Hr).
  apply KEEP0. clear - Hj Hp4 Hpce C1. lia. }
assert (FIN : forall regsF memF mdF,
  ajournal SEGS B LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3 memF mdF
    (4 * Z.of_nat i + 1 + buf_of.EV_BUF_OF) ->
  getr regsF 2 = w64 mf -> getr regsF 9 = w64 mf -> getr regsF 8 = w64 sp0 ->
  getr regsF 3 = w64 (as_gp B) -> getr regsF 4 = w64 (as_tp B) ->
  getr regsF 18 = w64 (SlotModel.rec_addr inp i) -> getr regsF 20 = w64 (SlotModel.rec_r inp i) ->
  getr regsF 22 = w64 k -> sh_reg g pos regsF -> getr regsF 24 = w64 gb -> getr regsF 27 = w64 pl ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (gb <= a < gb + k) -> ~ (mf - ESTACK <= a < mf) ->
     aview SEGS (w_H W3) memF a = aview SEGS (w_H W3) mem3 a) ->
  bytes_at8 W3 memF gb (SlotModel.rec_pl inp i) ->
  d1_C5 g pos mf i pl gb W3 (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 1460)) memF (seg_rom SEGS)) mdF)).
{ intros regsF memF mdF HJF G2r G9r G8r G3r G4r G18 G20 G22 G23 G24 G27 KF Hgbb.
  assert (KM : forall a, mf <= a < sp0 -> aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite KF by (clear - Ha Hmf0 Hgbce Hrq Hgb4 Hes C1 Hmfb Hshi H47; lia).
    apply KM3. clear - Ha Hmfb H47 Hshi. lia. }
  assert (KFR : forall a, SFa g pos <= a < SFa g pos + 1024 -> aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite KF by (clear - Ha Hgbf Hrq HSF0 HSF1 C1 Hmf0 Hes; lia). apply KFR3. exact Ha. }
  assert (KSH : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
    aview SEGS (w_H W3) memF a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha. rewrite KF.
    - apply KSH3. exact Ha.
    - clear - Ha Hsh1 C2 C5. lia.
    - intros Hx. apply (fshadow_not_app (SFa g pos) 128 gb (req_size (k + 1)) a);
      [exact HSF0 | clear - HSF1 C1; lia | exact Hgbapp | | clear - Hx Hrq; lia].
      rewrite Esh in Ha. unfold SHADOW_OFF in Ha. clear - Ha. lia.
    - clear - Ha Hsh1 C2 C5 C1 Hmf0 Hes. lia. }
  assert (KBL : forall p n j, In (p, n) (ablocks B ly2 S2) -> 0 <= j < req_size n ->
    aview SEGS (w_H W3) memF (p + j) = aview SEGS (w_H W2) mem2 (p + j)).
  { intros p n j Hin Hj.
    assert (Hin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; left; exact Hin).
    assert (Hne : (p, n) <> (gb, k + 1)) by (intros Heq; rewrite Heq in Hin; exact (HnotE2 Hin)).
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 p n gb (k + 1) HAR3 Hin3 Hgbin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4 & Hpce & _).
    rewrite KF by (clear - Hj Hd Hrq Hp4 Hpce C1 Hmf0 Hes; lia). exact (KBL3 p n j Hin Hj). }
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [Efd Efs].
  unfold d1_C5, acut. exists ly3, S3, regsF, memF, mdF.
  split; [reflexivity|].
  split; [replace (4 * Z.of_nat i + 2) with (4 * Z.of_nat i + 1 + buf_of.EV_BUF_OF) by (unfold buf_of.EV_BUF_OF; clear; lia); exact HJF|].
  split; [rewrite Hfrs3; exact Hfrs|].
  split; [unfold EV_LLVMF; clear - Hi64; lia|].
  split.
  { eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3)|]. unfold MEV. clear - HM0 HF0 HMm. nia. }
  split.
  { apply (mo_ok_step MT MTL S2 S3 (mo_malloc MT (k + 1))); [|exact MLE3].
    apply (mo_ok_le MT MTL _ _ _ MOK). unfold MEV, EV_LLVMF. clear - HM0 HF0 HMm Hi64. nia. }
  split.
  { apply (d1g_ecommon_moved g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regsF memF mdF HC).
    - rewrite G2r, Rsp. reflexivity.
    - rewrite G9r, Rs1. reflexivity.
    - rewrite G8r, Rs0. reflexivity.
    - rewrite G3r, Rgp. reflexivity.
    - rewrite G4r, Rtp. reflexivity.
    - exact KM.
    - intros a Ha. apply KFR. clear - Ha. lia.
    - intros j Hj. destruct Hinp as [[Hn0 _] | [_ Hine]]; [clear - Hj Hn0; lia|].
      assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
      { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
      pose proof (req_size_pos (e_n g) ltac:(clear - Hj; lia)) as Hrqn.
      exact (KBL _ _ j Hine2 ltac:(clear - Hj Hrqn; lia)).
    - exact Efd.
    - exact Efs. }
  split; [exact Hi|].
  split.
  { destruct Hbl as [Hperm Hfa]. split.
    - rewrite Eab3. eapply Permutation_trans; [apply Permutation_app_tail; exact Hperm|]. cbn [app]. apply perm_skip.
      apply Permutation_sym. apply Permutation_cons_append.
    - apply Forall_cons; [exact (Forall_inv Hfa)|]. apply Forall_cons; [|apply Forall_nil].
      cbn [fst snd]. try change (SlotModel.rec_k (e_pl g) i) with k. clear - Hgb4 Hkr. lia. }
  split.
  { apply (d1g_fbytes W2 W3 mem2 memF _ _); [|exact Hplb].
    intros x Hx. rewrite SlotModel.rec_pl_length in Hx. try change (SlotModel.rec_k (e_pl g) i) with k in Hx.
    replace x with (pl + (x - pl)) by ring. exact (KBL _ _ (x - pl) Hplin2 ltac:(clear - Hx Hrqk Hkr; lia)). }
  split; [exact Hgbb|].
  split; [apply (d1g_val W2 W3 mem2 memF _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V112]|].
  split; [apply (d1g_val W2 W3 mem2 memF _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V120]|].
  split; [apply (d1g_val W2 W3 mem2 memF _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V128]|].
  split; [apply (d1g_stab_moved g pos mf W2 W3 mem2 memF); [intros x Hx; apply KM; clear - Hx Hmfb; lia | exact Hstab]|].
  split; [exact G18|]. split; [exact G20|]. split; [exact G22|]. split; [exact G24|]. split; [exact G27|].
  split; [exact G23|].
  split; [apply (d1g_id_moved g pos (S i) W2 W3 mem2 memF HSF64);
    [intros x Hx; apply KFR; clear - Hx; lia | intros x Hx; apply KSH; clear - Hx; lia | exact Hid]|].
  split; [apply (d1g_hw_moved g pos mf i W2 W3 mem2 memF HSF64);
    [intros x Hx; apply KFR; clear - Hx; lia | intros x Hx; apply KSH; clear - Hx; lia
    | intros x Hx; apply KM; clear - Hx Hmfb; lia | exact Hhw]|].
  split.
  { apply (d1g_fbytes W2 W3 mem2 memF _ _); [|exact Hbef].
    unfold m_id. rewrite SlotModel.rec_id_length. unfold V_before, RcIdentModel.ID_SIZE.
    intros x Hx. apply KFR. clear - Hx. lia. }
  split; [apply (d1g_fshblk W2 W3 mem2 memF _ _); [|exact Hsbef];
    unfold V_before, N_before; rewrite d1g_shoff_frame by (first [exact HSF64 | lia]);
    intros x Hx; apply KSH; clear - Hx; lia|].
  apply (d1g_fshblk W2 W3 mem2 memF _ _); [|exact Hsid].
  unfold V_id, N_id; rewrite d1g_shoff_frame by (first [exact HSF64 | lia]).
  intros x Hx; apply KSH; clear - Hx; lia. }
let K := run_K_hi HS in jafter_call_keep_hi HS K regs3 (mrestrict (w_H W3) mem3) HP3 (@nil nat) HS3.
specialize (HS3 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS3. clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI3 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] Ev (mrestrict (w_H W3) mem3)) by constructor
end.
clear HEI0 SHOK.
assert (X516 : ew (havoc E 512 (map (getr regs3) CLOB)) 516 = getr regs3 10%bv)
  by exact (ew_havoc_new E 512 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)).
paj_run_tok RUN HS HJ3 SHOK3 Bspan; [apply awr_ok_nil|].
assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W3) mem3 (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* k = 0: straight to +0x5b4 *)
  assert (Hk0 : k = 0).
  { assert (X22 : ew (havoc E 512 (map (getr regs3) CLOB)) 22 = Z_to_bv 64 k)
      by (rewrite ew_havoc_old by (cbv; lia); rewrite (EE 22%nat 22%bv eq_refl); exact R22).
    rewrite branch_eq_U, (U_atom _ 22 k X22), U_SLit in Hc by (clear - Hkr; lia).
    rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ3 SHOK3 Bspan 0x5b4; [apply awr_ok_nil|].
  lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msn)) => rename msn into msX end.
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KEEPa a Ha).
    apply (kept_of_frame _ _ (w_H W3) (ms_mem ms0) (ms_mem msX) (fun _ => False) HFr); [|exact Ha|intros []].
    intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
  clear HF HFr HG.
  pmkst HS.
  repeat rewrite wvb_collapse in HJ3.
  prreg HS (2%bv : bv 5) F2. prreg HS (9%bv : bv 5) F9. prreg HS (8%bv : bv 5) F8.
  prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (18%bv : bv 5) F18.
  prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
  apply SRr_ret. exists gb.
  apply FIN.
  + exact HJ3.
  + rewrite F2, (EE 2%nat 2%bv eq_refl). exact Rsp.
  + rewrite F9, (EE 9%nat 9%bv eq_refl). exact Rs1.
  + rewrite F8, (EE 8%nat 8%bv eq_refl). exact Rs0.
  + rewrite F3, (EE 3%nat 3%bv eq_refl). exact Rgp.
  + rewrite F4, (EE 4%nat 4%bv eq_refl). exact Rtp.
  + rewrite F18, (EE 18%nat 18%bv eq_refl). exact R18.
  + rewrite F20, (EE 20%nat 20%bv eq_refl). exact R20.
  + rewrite F22, (EE 22%nat 22%bv eq_refl). exact R22.
  + unfold sh_reg in *. rewrite F23, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite F24. exact Rres.
  + rewrite F27, (EE 27%nat 27%bv eq_refl). exact R27.
  + intros a Ha _ _. exact (KEEPb a Ha).
  + unfold bytes_at8. intros j Hj. rewrite length_map, SlotModel.rec_pl_length in Hj. fold k in Hj.
    rewrite Hk0 in Hj. cbn in Hj. lia.
- (* k <> 0: the copy *)
  assert (Hk0 : k <> 0).
  { assert (X22 : ew (havoc E 512 (map (getr regs3) CLOB)) 22 = Z_to_bv 64 k)
      by (rewrite ew_havoc_old by (cbv; lia); rewrite (EE 22%nat 22%bv eq_refl); exact R22).
    rewrite branch_eq_U, (U_atom _ 22 k X22), U_SLit in Hc by (clear - Hkr; lia).
    rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc. exact Hc. }
  paj_run_tok RUN HS HJ3 SHOK3 Bspan; [apply awr_ok_nil|].
  lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msn)) => rename msn into msX end.
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KEEPa a Ha).
    apply (kept_of_frame _ _ (w_H W3) (ms_mem ms0) (ms_mem msX) (fun _ => False) HFr); [|exact Ha|intros []].
    intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
  clear HF HFr HG.
  pmkst HS.
  repeat rewrite wvb_collapse in HJ3.
  prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3. prreg HS (4%bv : bv 5) M4.
  prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11. prreg HS (12%bv : bv 5) M12.
  assert (M10' : getr (ms_regs msX) 10 = w64 gb) by (rewrite M10; exact Rres). rewrite (EE 27%nat 27%bv eq_refl), R27 in M11.
  rewrite (EE 22%nat 22%bv eq_refl), R22 in M12.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in M2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in M3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in M4.
  assert (UspX : spZ (ms_regs msX) = mf)
    by (unfold spZ; rewrite M2; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA IB___asan_memcpy) AMEMCPY W3 (ms_regs msX) (ms_mem msX)
      LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 _ _ gb pl k (mf - sp0)
      (Z_to_bv 64 (BASE + 1460)) HJ3).
    - exact M10'.
    - exact M11.
    - exact M12.
    - clear - Hkr. lia.
    - clear - Hgb4. lia.
    - clear - Hgbce Hrq C1. lia.
    - rewrite UspX. clear. lia.
    - clear - Hmf32 Hsp0al. lia.
    - clear - Hmfb. lia.
    - rewrite Hes. clear - Hmfb HSTK' Has. lia.
    - exact M3.
    - exact M4.
    - exact M1.
    - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
    - intros a Ha. split.
      + right. right. left. exists gb, (k + 1). split; [exact Hgbin|]. split; [exact HnotE|]. clear - Ha Hrq. lia.
      + clear - Ha Hgbce Hrq C1 Hmf0 Hes. lia.
    - apply (amem_range_sub_app gb (req_size (k + 1)) gb k Hgbapp Hgbce); clear - Hrq Hkr; lia.
    - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msX) _ gb (k + 1));
      [exact (proj1 HJ3) | exact Hgbin | apply Z.le_refl | clear - Hrq; lia].
    - intros Hk1. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msX) _ gb (k + 1));
      [exact (proj1 HJ3) | exact Hgbin | apply Z.le_refl | clear - Hrq; lia | exact Hk1].
    - cbn beta iota.
      split; [clear - Hpl4; lia|]. split; [clear - Hplce Hrqk C1; lia|].
      split.
      { intros a Ha. split.
        - rewrite (KEEPb a ltac:(clear - Ha Hpl4 Hplce Hrqk C1; lia)).
          replace a with (pl + (a - pl)) by ring.
          rewrite (KBL3 pl k (a - pl) Hplin2 ltac:(clear - Ha Hrqk; lia)).
          assert (Hlt : (Z.to_nat (a - pl) < length (map (fun b : byte => bv_unsigned b) (SlotModel.rec_pl inp i)))%nat).
          { rewrite length_map, SlotModel.rec_pl_length. fold k. clear - Ha. lia. }
          destruct (Hplb (Z.to_nat (a - pl)) Hlt) as [Hv _].
          rewrite Z2Nat.id in Hv by (clear - Ha; lia).
          exact (d1g_aview_some _ _ _ _ Hv).
        - rewrite UspX. clear - Ha Hplce Hrqk C1 Hmf0 Hes. lia. }
      split; [clear - Hgbpl Hrq Hrqk; lia|].
      split; [apply (amem_range_sub_app pl (req_size k) pl k Hplapp Hplce); clear - Hrqk Hkr; lia|].
      split; [eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msX) _ pl k);
        [exact (proj1 HJ3) | exact Hplin3 | apply Z.le_refl | clear - Hrqk; lia]|].
      intros Hk1. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem msX) _ pl k);
      [exact (proj1 HJ3) | exact Hplin3 | apply Z.le_refl | clear - Hrqk; lia | exact Hk1]. }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr & Hpres4 & Hsame).
  let K := run_K_hi HS in jafter_call_keep_hi HS K regs4 (mrestrict (w_H W3) mem4) HP4 (@nil nat) HS4.
  specialize (HS4 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS4.
  prreg HS4 (2%bv : bv 5) F2. prreg HS4 (9%bv : bv 5) F9. prreg HS4 (8%bv : bv 5) F8.
  prreg HS4 (3%bv : bv 5) F3. prreg HS4 (4%bv : bv 5) F4. prreg HS4 (18%bv : bv 5) F18.
  prreg HS4 (20%bv : bv 5) F20. prreg HS4 (22%bv : bv 5) F22. prreg HS4 (23%bv : bv 5) F23.
  prreg HS4 (24%bv : bv 5) F24. prreg HS4 (27%bv : bv 5) F27.
  apply SRr_ret. exists gb.
  apply FIN.
  + exact HJ4.
  + rewrite F2, (EE 2%nat 2%bv eq_refl). exact Rsp.
  + rewrite F9, (EE 9%nat 9%bv eq_refl). exact Rs1.
  + rewrite F8, (EE 8%nat 8%bv eq_refl). exact Rs0.
  + rewrite F3, (EE 3%nat 3%bv eq_refl). exact Rgp.
  + rewrite F4, (EE 4%nat 4%bv eq_refl). exact Rtp.
  + rewrite F18, (EE 18%nat 18%bv eq_refl). exact R18.
  + rewrite F20, (EE 20%nat 20%bv eq_refl). exact R20.
  + rewrite F22, (EE 22%nat 22%bv eq_refl). exact R22.
  + unfold sh_reg in *. rewrite F23, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite F24. exact Rres.
  + rewrite F27, (EE 27%nat 27%bv eq_refl). exact R27.
  + intros a Ha Hgb Hst. rewrite (Hfr a Ha Hgb ltac:(clear - Hst; lia)). exact (KEEPb a Ha).
  + apply (d1g_bytes_moved W2 W3 mem2 mem4 pl gb _); [|exact Hplb].
    intros kk Hkk. rewrite SlotModel.rec_pl_length in Hkk. fold k in Hkk.
    rewrite (Heff kk ltac:(clear - Hkk Hkr; lia)).
    rewrite (KEEPb (pl + kk) ltac:(clear - Hkk Hpl4 Hplce Hrqk C1 Hkr; lia)).
    exact (KBL3 pl k kk Hplin2 ltac:(clear - Hkk Hrqk Hkr; lia)).
Qed.


Lemma d1g_testbit_high : forall x i, 0 <= x < 2 ^ 64 -> 64 <= i -> Z.testbit x i = false.
Proof.
intros x i Hx Hi. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma d1g_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (E : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
{ rewrite Z.lnot_eq_pred_opp. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by lia. replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (d1g_testbit_high x i) by lia. reflexivity.
Qed.
Lemma d1g_U_not : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite d1g_lxor_ones by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma d1g_chunk1 : forall E ss (W : world SEGS) ms r b off v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> In r (ss_mem ss) -> YP09.r_base r = Some b ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) (YP09.r_chunks r) -> 0 <= v < 256 ->
  aview SEGS (w_H W) (ms_mem ms) (bv_unsigned (ew E b) + off) = Some v.
Proof.
intros E ss W ms r b off v HS Hin Hb Hc Hv.
pose proof (st_ok_mem_ok SEGS E ss _ HS) as HM.
pose proof (mem_ok_region SEGS E _ _ r HM Hin) as (_ & _ & _ & Hcs).
rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
pose proof (val_of_chunk_ok SEGS E _ _ off 1 (SLit v) v Hck ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hvm.
cbn [ms_mem restrict] in Hvm.
specialize (Hvm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hvm. rewrite Z.add_0_r in Hvm.
unfold aview. rewrite Hvm. cbn [option_map]. f_equal.
rewrite le_byte_small by (cbn; lia). cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma d1g_bytes_some : forall (W : world SEGS) mem a l j,
  bytes_at8 W mem a l -> 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W) mem (a + j) <> None.
Proof.
intros W mem a l j Hb Hj. unfold bytes_at8 in Hb.
assert (Hlt : (Z.to_nat j < length (map (fun b : byte => bv_unsigned b) l))%nat) by (rewrite length_map; lia).
destruct (Hb (Z.to_nat j) Hlt) as [Hv _]. rewrite Z2Nat.id in Hv by lia. exact (d1g_aview_some _ _ _ _ Hv).
Qed.
Lemma d1g_app_not_sh : forall p n a, in_app p n -> p <= a < p + n -> a < kLowMemEnd \/ kHighShadowEnd <= a.
Proof. intros p n a Hp Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighShadowEnd in *. lia. Qed.

Definition d1g_mfR : YP09.region := YP09.mkRegion (Some 9%nat) 152 184 152 152
  [YP09.mkChunk 152 (CVal 8 (SOff 36 0)); YP09.mkChunk 160 (CVal 8 (SOff 34 0));
   YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 176 (CVal 8 (SOff 35 0))].
Definition d1g_gkR : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition d1g_shR : YP09.region := YP09.mkRegion (Some 34%nat) 14 19 14 19 [].
Definition d1g_ss5 : sstate := mkSS 0x5b4 sr_atoms [d1g_mfR; d1g_gkR] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 0 255 0);
            (24%nat, PTR 0); (32%nat, mkAF SB SB 0); (33%nat, PTR 0)] []
           [(SAlu ALU_ADD (SOff 24 0) (SOff 22 0), SOff 33 0)]).
Definition d1g_SH5 : list shent := [mkSHE 33 0 1].

Lemma d1_c5_c6 : forall g pos mf i pl gb W2 c2, d1_C5 g pos mf i pl gb W2 c2 ->
  SRr SEGS W2 c2 (d1_C6 g pos mf i pl gb).
Proof.
intros g pos mf i pl gb W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & V168 & Vra & Vs0 &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
destruct HP as (Hi & Hbl & Hplb & Hgbb & V112 & V120 & V128 & Hstab & R18 & R20 & R22 & R24 & R27 & R23 &
  Hid & Hhw & Hbef & Hsbef & Hsid).
pose proof Hstab as (V96 & Hfix & Vbef & Vagn & Vmid).
pose proof Hfix as (_ & _ & _ & _ & _ & _ & _ & _ & _ & V160).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & Hlive0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hsh1 : kLowMemEnd <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= kHighShadowEnd).
{ rewrite Esh, C2, C5. unfold SHADOW_OFF. clear - HSF0 HSF1 C1. lia. }
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
set (nrec := SlotModel.nrec inp) in *.
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
pose proof (SlotModel.nrec_range inp) as Hnr. fold nrec in Hnr.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp nrec in Hi. clear - Hi Hnr. lia. }
(* the guard block *)
assert (Hgbin : In (gb, k + 1) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 gb (k + 1) HAR2 Hgbin) as (_ & Hgb4 & Hgbce & Hgbapp & _).
pose proof (req_size_pos (k + 1) ltac:(clear - Hkr; lia)) as Hrq.
assert (HnotE : ~ In (gb, k + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. apply in_split in Hin as (l1 & l2 & El).
  destruct Hbl as [Hperm _].
  assert (Hp2 : Permutation (ablocks B ly2 S2) ((gb, k + 1) :: (gb, k + 1) :: (pl, k) :: l1 ++ l2)).
  { eapply Permutation_trans; [exact Hperm|]. rewrite El. cbn [app].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
    eapply Permutation_trans; [apply perm_skip, Permutation_sym, Permutation_middle|]. apply perm_swap. }
  pose proof (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ _ HAR2 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd Hrq. lia. }
assert (Hplin2 : In (pl, k) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). cbn [app]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl k HAR2 Hplin2) as (_ & Hpl4 & Hplce & Hplapp & _).
pose proof (req_size_pos k ltac:(clear - Hkr; lia)) as Hrqk.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 gb (k + 1) 4 pos HAR2 Hgbin Hin4) as Hgbf.
unfold zdisjoint in Hgbf. cbn [fst snd] in Hgbf. rewrite EFa, HFB in Hgbf.
(* the environment: 32 = SB, 33 = gb + k, 34 = the frame's shadow, 35 = &again, 36 = &before *)
remember (Eimg (Ereg regs2 [w64 SB; w64 (gb + k); w64 (shadow_addr (SFa g pos));
  w64 (SFa g pos + V_again); w64 (SFa g pos + V_before)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E32 : ew E 32 = w64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 (gb + k)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 (shadow_addr (SFa g pos))) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 (SFa g pos + V_again)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = w64 (SFa g pos + V_before)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ rewrite (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U22 : bv_unsigned (ew E 22) = k).
{ rewrite (EE 22%nat 22%bv eq_refl), R22. apply unsigned_lit_small. clear - Hkr. lia. }
assert (U24 : bv_unsigned (ew E 24) = gb).
{ rewrite (EE 24%nat 24%bv eq_refl), R24. apply unsigned_lit_small. clear - Hgb4 Hgbce Hrq C1. lia. }
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; clear; lia).
assert (U33 : bv_unsigned (ew E 33) = gb + k).
{ rewrite E33. apply unsigned_lit_small. clear - Hgb4 Hgbce Hrq Hkr C1. lia. }
assert (HS : st_ok_pi SEGS VAL E d1g_ss5
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x5b4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d1g_ss5. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d1g_mfR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 Hmfb Hshi H47; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 36 0) (SFa g pos + V_before));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold V_before; clear - HSF0 HSF1 C1; lia | clear; lia | exact Vbef].
      * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 34 0) (shadow_addr (SFa g pos)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hsh1 C2 C5; lia | clear; lia | exact V160].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; clear; lia | clear; lia | exact V168].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 35 0) (SFa g pos + V_again));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold V_again; clear - HSF0 HSF1 C1; lia | clear; lia | exact Vagn].
    + unfold d1g_gkR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [clear - Hgb4 Hkr; lia|]. split; [clear - Hgbce Hrq Hkr C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 gb (k + 1) HAR2 Hgbin) as (_ & _ & _ & _ & Hpr & _).
      apply (proj1 (Hpr (gb + k + o) ltac:(clear - Ho Hrq Hkr; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d1g_mfR, d1g_gkR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
    right. clear - Hmf0 Hgbce Hrq Hkr. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U22, U24, U32, U33.
    split; [|split; [exact I|]].
    + repeat match goal with |- _ /\ _ => split end;
      clear - C1 Hmf0 Hmfb Hshi H47 Hsp0al Hmf32 Hgb4 Hgbce Hrq Hkr; try unfold SB; lia.
    + split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 24 gb ltac:(rewrite (EE 24%nat 24%bv eq_refl); exact R24) ltac:(clear - Hgb4 Hgbce Hrq C1; lia)).
      rewrite (U_atom E 22 k ltac:(rewrite (EE 22%nat 22%bv eq_refl); exact R22) ltac:(clear - Hkr; lia)).
      rewrite (U_atom E 33 (gb + k) E33 ltac:(clear - Hgb4 Hgbce Hrq Hkr C1; lia)).
      unfold zcanon, M64. rewrite Z.mod_small by (clear - Hgb4 Hgbce Hrq Hkr C1; lia). reflexivity. }
assert (SHOK : sh_ok SEGS (SOff 32 0) d1g_SH5 E (mrestrict (w_H W2) mem2)).
{ unfold d1g_SH5. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E (SOff 32 0) 33 (gb + k) 1 (gb + k) 0 1).
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 gb (k + 1));
    [exact HAR2 | exact Hgbin | clear - Hkr; lia | clear - Hrq; lia].
  - rewrite (U_atom E 32 SB E32) by (unfold SB; clear; lia). reflexivity.
  - exact (U_atom E 33 (gb + k) E33 ltac:(clear - Hgb4 Hgbce Hrq Hkr C1; lia)).
  - clear. lia.
  - clear. lia.
  - intros x Hx. clear - Hx Hgbapp Hrq Hkr C2 C3 C5. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold cfg_at. change (w64 (BASE + 0x5b4)) with (Z_to_bv 64 (BASE + 0x5b4)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ intros a (r & Hr & Ha). unfold d1g_ss5 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold d1g_mfR, d1g_gkR in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [clear - Ha; lia|].
  rewrite U33 in Ha. right. right. left. exists gb, (k + 1). split; [exact Hgbin|]. split; [exact HnotE|].
  clear - Ha Hrq Hkr. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> gb + k ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => x = gb + k) HFr); [|exact Ha|exact Hn].
  intros bb wlo whi aa Hin Hr. cbn in Hin. destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; [clear - Hr; lia | rewrite U33 in Hr; clear - Hr; lia]. }
clear HF HFr HG.
assert (X24 : ew E 24 = Z_to_bv 64 gb) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (X22 : ew E 22 = Z_to_bv 64 k) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
psrr_branch_tok RUN BR HS SHOK Bspan.
2:{ exfalso. rewrite branch_geu_U in Hc.
    rewrite (d1g_U_not E 24 gb X24 ltac:(clear - Hgb4 Hgbce Hrq C1; lia)) in Hc.
    rewrite (U_atom E 22 k X22 ltac:(clear - Hkr; lia)) in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc. clear - Hc Hgb4 Hgbce Hrq Hkr C1. lia. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5e0.
{ intros a (r & Hr & Ha). cbn in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [clear - Ha; lia|].
  rewrite U33 in Ha. right. right. left. exists gb, (k + 1). split; [exact Hgbin|]. split; [exact HnotE|].
  clear - Ha Hrq Hkr. lia. }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msn)) => rename msn into msA end.
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> a <> gb + k ->
  aview SEGS (w_H W2) (ms_mem msA) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite <- (KEEP1 a Ha Hn).
  apply (kept_of_frame E _ (w_H W2) (ms_mem ms) (ms_mem msA) (fun x => x = gb + k) HFr); [|exact Ha|exact Hn].
  intros bb wlo whi aa Hin Hr. cbn in Hin. destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; [clear - Hr; lia | rewrite U33 in Hr; clear - Hr; lia]. }
clear HF HFr HG.
pose (RUNP := SRr_run_pi_AJ B LAWS). pose (RUNC := SRr_run_pi_AJ_call B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  assert (U34x : bv_unsigned (ew Ex 34) = shadow_addr (SFa g pos))
    by (cbn [ew ewset Nat.eqb]; rewrite E34; apply unsigned_lit_small; clear - Hsh1 C2 C5; lia);
  assert (U33x : bv_unsigned (ew Ex 33) = gb + k) by (cbn [ew ewset Nat.eqb]; exact U33);
  assert (U9x : bv_unsigned (ew Ex 9) = mf) by (cbn [ew ewset Nat.eqb]; exact U9);
  assert (HS2 : st_ok_pi SEGS VAL Ex (mkSS (ss_pc ssx) (ss_regs ssx) (d1g_shR :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx))
    (restrict (w_H W2) msx))
end.
{ apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
  - unfold d1g_shR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U34x. split; [clear - Hsh1 C5; lia|]. split; [clear - Hsh1 C2; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS).
    apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
      [(4, pos)] ly2 S2 W2 (ms_mem msA) _ (4 * Z.of_nat i + 2) (shadow_addr (SFa g pos) + o) HJ ltac:(
      right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
      unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho; lia))).
  - cbn [all_disjoint ss_mem]. split; [|split; [|exact I]]; unfold extent_disjoint, d1g_shR;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U34x.
    + rewrite U9x. clear - Hsh1 Hmf0 C1 C2. lia.
    + rewrite U33x. clear - Hgbapp Hrq Hkr Hsh1 C2 C3 C5.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
clear HS. rename HS2 into HS.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). cbn in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val d1g_shR] in Ha.
  - rewrite U34x in Ha. right. right. right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ha; lia.
  - clear - Ha; lia.
  - rewrite U33x in Ha. right. right. left. exists gb, (k + 1). split; [exact Hgbin|]. split; [exact HnotE|].
    clear - Ha Hrq Hkr. lia. }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msn)) => rename msn into msB end.
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> a <> gb + k ->
  ~ (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19) ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn Hs. rewrite <- (KEEPA a Ha Hn).
  apply (kept_of_frame _ _ (w_H W2) (ms_mem msA) (ms_mem msB)
    (fun x => x = gb + k \/ shadow_addr (SFa g pos) + 14 <= x < shadow_addr (SFa g pos) + 19) HFr);
  [|exact Ha|intros [Hx|Hx]; [exact (Hn Hx) | exact (Hs Hx)]].
  intros bb wlo whi aa Hin Hr. cbn in Hin. destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; [right; rewrite U34x in Hr; clear - Hr; lia | clear - Hr; lia | left; rewrite U33x in Hr; clear - Hr; lia]. }
clear HF HFr HG.
(* the five shadow cells of `again` the run wrote *)
lazymatch type of HS with st_ok _ _ (setpc (mkSS _ _ (?r1 :: _) _ _) _) _ =>
  pose proof (d1g_chunk1 _ _ W2 msB r1 34 14 0 HS ltac:(cbn; left; reflexivity) eq_refl
    ltac:(cbn; right; right; right; right; left; reflexivity) ltac:(lia)) as SH14;
  pose proof (d1g_chunk1 _ _ W2 msB r1 34 15 0 HS ltac:(cbn; left; reflexivity) eq_refl
    ltac:(cbn; right; right; right; left; reflexivity) ltac:(lia)) as SH15;
  pose proof (d1g_chunk1 _ _ W2 msB r1 34 16 0 HS ltac:(cbn; left; reflexivity) eq_refl
    ltac:(cbn; right; right; left; reflexivity) ltac:(lia)) as SH16;
  pose proof (d1g_chunk1 _ _ W2 msB r1 34 17 0 HS ltac:(cbn; left; reflexivity) eq_refl
    ltac:(cbn; right; left; reflexivity) ltac:(lia)) as SH17;
  pose proof (d1g_chunk1 _ _ W2 msB r1 34 18 6 HS ltac:(cbn; left; reflexivity) eq_refl
    ltac:(cbn; left; reflexivity) ltac:(lia)) as SH18
end.
rewrite U34x in SH14, SH15, SH16, SH17, SH18.
assert (SHA : sh_blk W2 (ms_mem msB) (SFa g pos + V_again) N_again).
{ unfold sh_blk, block_shadow, V_again, N_again.
  split; [clear - HSF64; lia|]. split; [clear; lia|].
  intros j Hj. rewrite d1g_shoff_frame by (first [exact HSF64 | clear; lia]).
  assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj; lia).
  destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]].
  - replace (shadow_addr (SFa g pos) + 112 / 8 + 0) with (shadow_addr (SFa g pos) + 14) by (clear; lia). rewrite SH14. reflexivity.
  - replace (shadow_addr (SFa g pos) + 112 / 8 + 1) with (shadow_addr (SFa g pos) + 15) by (clear; lia). rewrite SH15. reflexivity.
  - replace (shadow_addr (SFa g pos) + 112 / 8 + 2) with (shadow_addr (SFa g pos) + 16) by (clear; lia). rewrite SH16. reflexivity.
  - replace (shadow_addr (SFa g pos) + 112 / 8 + 3) with (shadow_addr (SFa g pos) + 17) by (clear; lia). rewrite SH17. reflexivity.
  - replace (shadow_addr (SFa g pos) + 112 / 8 + 4) with (shadow_addr (SFa g pos) + 18) by (clear; lia). rewrite SH18. reflexivity. }
(* `before` at the copy *)
assert (KSHB : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  ~ (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19) ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hs. apply KEEPB; [clear - Ha Hsh1 C2 C5; lia | | exact Hs].
  intros Heq. destruct (d1g_app_not_sh gb (req_size (k + 1)) a Hgbapp ltac:(clear - Heq Hrq Hkr; lia)) as [Hx | Hx];
  clear - Hx Ha Hsh1; lia. }
assert (KFRB : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEPB; [clear - Ha HSF0 HSF1 C1; lia | clear - Ha Hgbf Hrq Hkr; lia |].
  destruct (d1g_app_not_sh _ _ a HSFapp ltac:(clear - Ha; lia)) as [Hx | Hx]; clear - Hx Hsh1; lia. }
assert (SBEF : sh_blk W2 (ms_mem msB) (SFa g pos + V_before) N_before).
{ apply (d1g_fshblk W2 W2 mem2 (ms_mem msB) _ _); [|exact Hsbef].
  unfold V_before, N_before. rewrite d1g_shoff_frame by (first [exact HSF64 | clear; lia]).
  intros x Hx. apply KSHB; clear - Hx; lia. }
assert (BBEF : bytes_at8 W2 (ms_mem msB) (SFa g pos + V_before) (m_id g i)).
{ apply (d1g_fbytes W2 W2 mem2 (ms_mem msB) _ _); [|exact Hbef].
  unfold m_id. rewrite SlotModel.rec_id_length. unfold V_before, RcIdentModel.ID_SIZE.
  intros x Hx. apply KFRB. clear - Hx. lia. }
pmkst HS.
repeat rewrite wvb_collapse in HJ.
prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3. prreg HS (4%bv : bv 5) M4.
prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11. prreg HS (12%bv : bv 5) M12.
rewrite E35 in M10. rewrite E36 in M11.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in M2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in M3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in M4.
assert (UspB : spZ (ms_regs msB) = mf)
  by (unfold spZ; rewrite M2; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA IB___asan_memcpy) AMEMCPY W2 (ms_regs msB) (ms_mem msB)
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ _
    (SFa g pos + V_again) (SFa g pos + V_before) 38 (mf - sp0) (Z_to_bv 64 (BASE + 1552)) HJ).
  - exact M10.
  - exact M11.
  - exact M12.
  - clear. lia.
  - unfold V_again. clear - HSF0. lia.
  - unfold V_again. clear - HSF1 C1. lia.
  - rewrite UspB. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - rewrite Hes. clear - Hmfb HSTK' Has. lia.
  - exact M3.
  - exact M4.
  - exact M1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - intros a Ha. unfold V_again in Ha. split.
    + right. right. right. exists 4, pos. split; [left; reflexivity|]. left.
      unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. clear - Ha. lia.
    + clear - Ha HSF1 C1 Hmf0 Hes. lia.
  - apply (amem_range_sub_app (SFa g pos) 1024 _ 38 HSFapp); unfold V_again; clear - HSF1 HSF0; lia.
  - apply (block_shadow_range _ _ _ _ _ _ SHA); [apply Z.le_refl | unfold N_again; clear; lia].
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ 4 pos);
    [exact (proj1 HJ) | exact Hin4 | rewrite EFa; unfold V_again; clear; lia
    | rewrite EFa, HFB; unfold V_again; clear; lia | clear; lia].
  - cbn beta iota.
    split; [unfold V_before; clear - HSF0; lia|]. split; [unfold V_before; clear - HSF1 C1; lia|].
    split.
    { intros a Ha. split.
      - replace a with (SFa g pos + V_before + (a - (SFa g pos + V_before))) by ring.
        apply (d1g_bytes_some W2 (ms_mem msB) _ (m_id g i) _ BBEF).
        unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. clear - Ha. lia.
      - rewrite UspB. unfold V_before in Ha. clear - Ha HSF1 C1 Hmf0 Hes. lia. }
    split; [unfold V_again, V_before; clear; lia|].
    split; [apply (amem_range_sub_app (SFa g pos) 1024 _ 38 HSFapp); unfold V_before; clear - HSF1 HSF0; lia|].
    split; [apply (block_shadow_range _ _ _ _ _ _ SBEF); [apply Z.le_refl | unfold N_before; clear; lia]|].
    intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ 4 pos);
    [exact (proj1 HJ) | exact Hin4 | rewrite EFa; unfold V_before; clear; lia
    | rewrite EFa, HFB; unfold V_before; clear; lia | clear; lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr & Hpres4 & Hsame).
let K := run_K_hi HS in jafter_call_keep_hi HS K regs4 (mrestrict (w_H W2) mem4) HP4 (@nil nat) HS4.
specialize (HS4 (Forall_nil _)). rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  lazymatch goal with HEIx : img_env _ _ (ewset (ewset E 512 _) 513 _) |- _ =>
    assert (HEI4 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEIx | cbv; lia]) end;
  assert (SHOK4 : sh_ok SEGS (SOff 32 0) [] Ev (mrestrict (w_H W2) mem4)) by constructor
end.
paj_run_to_tok RUNTO HS HJ4 SHOK4 Bspan 0x620; [apply awr_ok_nil|].
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msn)) => rename msn into msC end.
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem4 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W2) mem4 (ms_mem msC) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
pmkst HS.
repeat rewrite wvb_collapse in HJ4.
prreg HS (2%bv : bv 5) F2. prreg HS (9%bv : bv 5) F9. prreg HS (8%bv : bv 5) F8.
prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
prreg HS (11%bv : bv 5) F11. prreg HS (12%bv : bv 5) F12. prreg HS (13%bv : bv 5) F13.
prreg HS (18%bv : bv 5) F18. prreg HS (20%bv : bv 5) F20. prreg HS (22%bv : bv 5) F22.
prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> a <> gb + k ->
  ~ (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19) ->
  ~ (SFa g pos + V_again <= a < SFa g pos + V_again + 38) -> ~ (mf - ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1 H2 H3 H4. rewrite (KEEPC a Ha). rewrite (Hfr a Ha H3 ltac:(clear - H4; lia)). exact (KEEPB a Ha H1 H2). }
assert (KM : forall a, mf <= a < sp0 -> aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KALL; unfold V_again; clear - Ha Hmf0 Hmfb Hshi H47 Hgbce Hrq Hkr C1 C2 Hsh1 HSF1 Hes; lia. }
assert (KFRx : forall a, SFa g pos <= a < SFa g pos + 1024 -> ~ (SFa g pos + V_again <= a < SFa g pos + V_again + 38) ->
  aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply KALL; [clear - Ha HSF0 HSF1 C1; lia | clear - Ha Hgbf Hrq Hkr; lia | | exact Hn | clear - Ha HSF1 C1 Hmf0 Hes; lia].
  destruct (d1g_app_not_sh _ _ a HSFapp ltac:(clear - Ha; lia)) as [Hx | Hx]; clear - Hx Hsh1; lia. }
assert (KSHx : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  ~ (shadow_addr (SFa g pos) + 14 <= a < shadow_addr (SFa g pos) + 19) ->
  aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply KALL; [clear - Ha Hsh1 C2 C5; lia | | exact Hn | | clear - Ha Hsh1 C1 C2 Hmf0 Hes; lia].
  - intros Heq. destruct (d1g_app_not_sh gb (req_size (k + 1)) a Hgbapp ltac:(clear - Heq Hrq Hkr; lia)) as [Hx | Hx];
    clear - Hx Ha Hsh1; lia.
  - intros Hx. unfold V_again in Hx. destruct (d1g_app_not_sh _ _ a HSFapp ltac:(clear - Hx; lia)) as [Hy | Hy];
    clear - Hy Ha Hsh1; lia. }
assert (KBLx : forall p n j, In (p, n) (ablocks B ly2 S2) -> (p, n) <> (gb, k + 1) -> 0 <= j < req_size n ->
  aview SEGS (w_H W2) (ms_mem msC) (p + j) = aview SEGS (w_H W2) mem2 (p + j)).
{ intros p n j Hin Hne Hj.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4 & Hpce & Hpapp & _).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 p n gb (k + 1) HAR2 Hin Hgbin Hne) as Hd.
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 p n 4 pos HAR2 Hin Hin4) as Hdf.
  unfold zdisjoint in Hd, Hdf. cbn [fst snd] in Hd, Hdf. rewrite EFa, HFB in Hdf.
  apply KALL; [clear - Hj Hp4 Hpce C1; lia | clear - Hj Hd Hrq Hkr; lia | | unfold V_again; clear - Hj Hdf; lia
  | clear - Hj Hpce C1 Hmf0 Hes; lia].
  destruct (d1g_app_not_sh _ _ (p + j) Hpapp ltac:(clear - Hj; lia)) as [Hx | Hx]; clear - Hx Hsh1; lia. }
apply SRr_ret.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [Efd Efs].
unfold d1_C6, acut. exists ly2, S2, (ms_regs msC), (ms_mem msC). eexists.
split; [reflexivity|].
split; [exact HJ4|].
split; [exact Hfrs|].
split; [exact Hk|].
split; [exact MLE|].
split; [exact MOK|].
split.
{ apply (d1g_ecommon_moved g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs msC) (ms_mem msC) _ HC).
  - rewrite F2, (EE 2%nat 2%bv eq_refl). reflexivity.
  - rewrite F9, (EE 9%nat 9%bv eq_refl). reflexivity.
  - rewrite F8, (EE 8%nat 8%bv eq_refl). reflexivity.
  - rewrite F3, (EE 3%nat 3%bv eq_refl). reflexivity.
  - rewrite F4, (EE 4%nat 4%bv eq_refl). reflexivity.
  - exact KM.
  - intros a Ha. apply KFRx; unfold V_again; clear - Ha; lia.
  - intros j Hj. destruct Hinp as [[Hn0 _] | [_ Hine]]; [clear - Hj Hn0; lia|].
    assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
    assert (Hne : (e_p g, e_n g) <> (gb, k + 1)) by (intros Heq; rewrite Heq in Hine; exact (HnotE Hine)).
    pose proof (req_size_pos (e_n g) ltac:(clear - Hj; lia)) as Hrqn.
    exact (KBLx _ _ j Hine2 Hne ltac:(clear - Hj Hrqn; lia)).
  - exact Efd.
  - exact Efs. }
split; [exact Hi|].
split; [exact Hbl|].
split.
{ apply (d1g_fbytes W2 W2 mem2 (ms_mem msC) _ _); [|exact Hplb].
  intros x Hx. rewrite SlotModel.rec_pl_length in Hx. try change (SlotModel.rec_k (e_pl g) i) with k in Hx. fold k in Hx.
  replace x with (pl + (x - pl)) by ring.
  assert (Hne : (pl, k) <> (gb, k + 1)) by (intros Heq; injection Heq as _ Hx2; clear - Hx2; lia).
  exact (KBLx _ _ (x - pl) Hplin2 Hne ltac:(clear - Hx Hrqk Hkr; lia)). }
split; [apply (d1g_val W2 W2 mem2 (ms_mem msC) _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V112]|].
split; [apply (d1g_val W2 W2 mem2 (ms_mem msC) _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V120]|].
split; [apply (d1g_val W2 W2 mem2 (ms_mem msC) _ _ _); [intros x Hx; apply KM; cbn in Hx; clear - Hx Hmfb; lia | exact V128]|].
split; [apply (d1g_stab_moved g pos mf W2 W2 mem2 (ms_mem msC)); [intros x Hx; apply KM; clear - Hx Hmfb; lia | exact Hstab]|].
split; [rewrite F10; exact E35|].
split; [rewrite F11, (EE 18%nat 18%bv eq_refl); exact R18|].
split; [rewrite F12, (EE 24%nat 24%bv eq_refl); exact R24|].
split; [rewrite F13, (EE 22%nat 22%bv eq_refl); exact R22|].
split; [rewrite F18, (EE 18%nat 18%bv eq_refl); exact R18|].
split; [rewrite F20, (EE 20%nat 20%bv eq_refl); exact R20|].
split; [rewrite F22, (EE 22%nat 22%bv eq_refl); exact R22|].
split; [rewrite F24, (EE 24%nat 24%bv eq_refl); exact R24|].
split; [rewrite F27, (EE 27%nat 27%bv eq_refl); exact R27|].
split; [unfold sh_reg in *; rewrite F23, (EE 23%nat 23%bv eq_refl); exact R23|].
split; [apply (d1g_id_moved g pos (S i) W2 W2 mem2 (ms_mem msC) HSF64);
  [intros x Hx; apply KFRx; unfold V_again; clear - Hx; lia | intros x Hx; apply KSHx; clear - Hx; lia | exact Hid]|].
split; [apply (d1g_hw_moved g pos mf i W2 W2 mem2 (ms_mem msC) HSF64);
  [intros x Hx; apply KFRx; unfold V_again; clear - Hx; lia | intros x Hx; apply KSHx; clear - Hx; lia
  | intros x Hx; apply KM; clear - Hx Hmfb; lia | exact Hhw]|].
split.
{ apply (d1g_fbytes W2 W2 mem2 (ms_mem msC) _ _); [|exact Hbef].
  unfold m_id. rewrite SlotModel.rec_id_length. unfold V_before, RcIdentModel.ID_SIZE.
  intros x Hx. apply KFRx; unfold V_again; clear - Hx; lia. }
split.
{ apply (d1g_bytes_moved W2 W2 (ms_mem msB) (ms_mem msC) (SFa g pos + V_before) (SFa g pos + V_again) _); [|exact BBEF].
  intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk. unfold RcIdentModel.ID_SIZE in Hkk.
  rewrite (KEEPC (SFa g pos + V_again + kk) ltac:(unfold V_again; clear - Hkk HSF0 HSF1 C1; lia)).
  exact (Heff kk ltac:(clear - Hkk; lia)). }
split.
{ apply (d1g_fshblk W2 W2 mem2 (ms_mem msC) _ _); [|exact Hsbef].
  unfold V_before, N_before. rewrite d1g_shoff_frame by (first [exact HSF64 | clear; lia]).
  intros x Hx. apply KSHx; clear - Hx; lia. }
split.
{ apply (d1g_fshblk W2 W2 (ms_mem msB) (ms_mem msC) _ _); [|exact SHA].
  unfold V_again, N_again. rewrite d1g_shoff_frame by (first [exact HSF64 | clear; lia]).
  intros x Hx. rewrite (KEEPC x ltac:(clear - Hx Hsh1 C2 C5; lia)). apply Hfr.
  - clear - Hx Hsh1 C2 C5. lia.
  - intros Hy. unfold V_again in Hy. destruct (d1g_app_not_sh _ _ x HSFapp ltac:(clear - Hy; lia)) as [Hz | Hz];
    clear - Hz Hx Hsh1; lia.
  - clear - Hx Hsh1 C1 C2 Hmf0 Hes. lia. }
split.
{ apply (d1g_fshblk W2 W2 mem2 (ms_mem msC) _ _); [|exact Hsid].
  unfold V_id, N_id. rewrite d1g_shoff_frame by (first [exact HSF64 | clear; lia]).
  intros x Hx. apply KSHx; clear - Hx; lia. }
apply (d1g_fbytes W2 W2 mem2 (ms_mem msC) _ _); [|exact Hgbb].
intros x Hx. rewrite SlotModel.rec_pl_length in Hx. try change (SlotModel.rec_k (e_pl g) i) with k in Hx. fold k in Hx.
apply KALL.
- clear - Hx Hgb4 Hgbce Hrq Hkr C1. lia.
- clear - Hx. lia.
- intros Hy. destruct (d1g_app_not_sh gb (req_size (k + 1)) x Hgbapp ltac:(clear - Hx Hrq Hkr; lia)) as [Hz | Hz];
  clear - Hz Hy Hsh1; lia.
- unfold V_again. clear - Hx Hgbf Hrq Hkr. lia.
- clear - Hx Hgbce Hrq C1 Hmf0 Hes. lia.
Qed.

Lemma d1_c4_c6 : forall g pos mf i pl W2 c2, d1_C4 g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => exists gb, d1_C6 g pos mf i pl gb W3 c3).
Proof.
intros g pos mf i pl W2 c2 H.
eapply SRr_bind; [exact (d1_c4_c5 g pos mf i pl W2 c2 H)|].
intros W3 c3 _ (gb & H5).
eapply SRr_mono; [exact (d1_c5_c6 g pos mf i pl gb W3 c3 H5)|].
intros W4 c4 _ H6. exists gb. exact H6.
Qed.


Definition ss_fr (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition Bx_FR : sv := SLit SB.
Definition Bspan_FR : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma d1_c6_end : forall g pos mf i pl gb W2 c2, d1_C6 g pos mf i pl gb W2 c2 ->
  SRr SEGS W2 c2 (INVD1END g pos mf i pl).
Proof.
intros g pos mf i pl gb W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as (Hi & Hbl & Hplb & V112 & V120 & V128 & Hstab & R10 & R11 & R12 & R13 & R18 & R20 &
  R22 & R24 & R27 & R23 & Hid & Hhw & Hbefb & Hagnb & Hbefs & Hagns & Hids & Hgbb).
destruct Hstab as (V96 & Hfix & Hbef & Hagn & Hmid).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & Hlive0 & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
(* the model facts of this record *)
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr.
pose proof (d1_addr_range (e_pl g) i) as Har.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Hpll.
pose proof (SlotModel.rec_id_length (e_pl g) i) as Hidl.
(* the two live heap blocks *)
assert (Hplin : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
assert (Hgin : In (gb, SlotModel.rec_k (e_pl g) i + 1) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 gb (SlotModel.rec_k (e_pl g) i + 1) HAR2 Hgin)
  as (_ & Hgb4096 & Hgbce & Hgbapp & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl (SlotModel.rec_k (e_pl g) i) HAR2 Hplin)
  as (_ & Hpl4096 & Hplce & Hplapp & _).
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i + 1) ltac:(lia)) as Hgreq.
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as Hplreq.
(* the environment of the first run *)
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (AGE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E (ss_fr 0x620)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x620)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fr. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint all_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS Bx_FR [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 (BASE + 0x620)) with (Z_to_bv 64 (BASE + 0x620)).
paj_run_tok RUN HS HJ SHOK Bspan_FR; [apply awr_ok_nil | ].
(* ---- the jal changed no byte ---- *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E (ss_mem (ss_fr 0x620)) (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr);
  [intros bb wlo whi aa Hin Hr; cbn in Hin; destruct Hin | exact Ha | intros []]. }
clear HF HFr HG.
(* the three memory facts the call reads, moved to the call state *)
assert (Hagnb1 : bytes_at8 W2 (ms_mem ms) (SF + V_again) (m_id g i)).
{ unfold bytes_at8 in *.
  apply (d1_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (SF + V_again) _); [|exact Hagnb].
  intros kk Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite Hidl in Hkk.
  unfold RcIdentModel.ID_SIZE in Hkk. apply KEEP1. unfold V_again in *. clear - Hkk HSF0 HSF1 C1. lia. }
assert (Hgbb1 : bytes_at8 W2 (ms_mem ms) gb (SlotModel.rec_pl (e_pl g) i)).
{ unfold bytes_at8 in *.
  apply (d1_garr8_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) gb _); [|exact Hgbb].
  intros kk Hkk. rewrite length_map, Hpll in Hkk. apply KEEP1.
  clear - Hkk Hgb4096 Hgbce Hgreq Hkr C1. lia. }
assert (Hagns1 : sh_blk W2 (ms_mem ms) (SF + V_again) N_again).
{ unfold sh_blk in *.
  apply (block_shadow_agree (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem ms))
           SHADOW_OFF (SF + V_again) N_again); [|exact Hagns].
  intros ii Hii. apply KEEP1. unfold shadow_of_addr, SHADOW_OFF, V_again, N_again in *.
  clear - Hii HSF0 HSF1 C1. lia. }
(* ---- the registers the call receives ---- *)
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp.
prreg HS (4%bv : bv 5) Qtp. prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1.
prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Qsp.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Qgp.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Qtp.
rewrite (EE 10%nat 10%bv eq_refl), R10 in Qa0.
rewrite (EE 11%nat 11%bv eq_refl), R11 in Qa1.
rewrite (EE 12%nat 12%bv eq_refl), R12 in Qa2.
rewrite (EE 13%nat 13%bv eq_refl), R13 in Qa3.
assert (Usp : spZ (ms_regs ms) = mf)
  by (unfold spZ; rewrite Qsp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (Ura : raZ (ms_regs ms) = BASE + 1572)
  by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE; lia).
(* ---- the premises of the second reac_identity_ingest call ---- *)
assert (EBB2 : blocks_bytes S2 = bsum (ablocks B ly2 S2)) by apply blocks_bytes_bsum.
assert (EBB0 : blocks_bytes (e_S g) = bsum (ablocks B (e_ly g) (e_S g))) by apply blocks_bytes_bsum.
assert (Ebs : bsum [(pl, SlotModel.rec_k (e_pl g) i); (gb, SlotModel.rec_k (e_pl g) i + 1)]
  = SlotModel.rec_k (e_pl g) i + (SlotModel.rec_k (e_pl g) i + 1))
  by (unfold bsum; cbn [fold_right snd]; lia).
assert (Hnev : st_nev S2 + reac_identity_ingest.EV_INGEST <= EV_MAX).
{ unfold reac_identity_ingest.EV_INGEST. clear - Hnev2 Hnev0 HEV Hk. lia. }
assert (Hlive : blocks_bytes S2 + reac_identity_ingest.LIVE_INGEST <= LIVE_MAX).
{ unfold reac_identity_ingest.LIVE_INGEST. rewrite EBB2.
  destruct Hbl as [Hperm _]. rewrite (bsum_perm _ _ Hperm), bsum_app, Ebs, <- EBB0.
  unfold LIVE_LLVMF in HLIVE. clear - Hlive0 HLIVE Hkr. lia. }
assert (HREC : forall a, SF + V_again <= a < SF + V_again + 38 ->
  awr_byte LLVMF_STK sp0 [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
{ intros a Ha. unfold awr_byte, in_frames. right; right; right. exists 4, pos.
  split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB.
  unfold V_again in *. clear - Ha HSF0 HSF1. lia. }
assert (HPRESa : forall a, SF + V_again <= a < SF + V_again + 38 -> apresent (w_H W2) (ms_mem ms) a).
{ intros a Ha.
  exact (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat i + 2) a HJ (HREC a Ha))). }
assert (HRECOK : reac_identity_ingest.ting_rec_ok B LLVMF_STK sp0 [] (e_ly g) (e_S g) [(4, pos)]
                   ly2 S2 W2 (ms_mem ms) mf (SF + V_again) (m_id g i)).
{ unfold reac_identity_ingest.ting_rec_ok.
  split; [clear - HSF64; unfold V_again; lia|].
  split.
  { left. exists 4, pos. split; [exact Hin4|].
    intros a Ha. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFa, HFB.
    unfold V_again in *. clear - Ha HSF0 HSF1. lia. }
  split.
  { right. unfold reac_identity_ingest.INGEST_STK, ESTACK, V_again.
    clear - HSF0 HSF1 Hmf0 C1. lia. }
  split; [intros a Ha; split; [exact (HREC a Ha) | exact (HPRESa a Ha)]|].
  split.
  { apply (block_shadow_range (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (SF + V_again) N_again
      (SF + V_again) 38); [exact Hagns1 | clear; lia | unfold N_again; clear; lia]. }
  split; [unfold m_id; rewrite Hidl; reflexivity|].
  apply (d1_mb SEGS). exact Hagnb1. }
assert (HPAYOK : reac_identity_ingest.ting_pay_ok B ly2 S2 W2 (ms_mem ms) gb
                   (SlotModel.rec_k (e_pl g) i) (SlotModel.rec_pl (e_pl g) i)).
{ unfold reac_identity_ingest.ting_pay_ok. split.
  - intros _. exists gb, (SlotModel.rec_k (e_pl g) i + 1). split; [exact Hgin|].
    split; clear; lia.
  - apply (d1_mb SEGS). exact Hgbb1. }
(* ---- the call at +0x620 ---- *)
pmkst HS.
rewrite (PSIG IB_reac_identity_ingest AF_reac_identity_ingest eq_refl).
eapply SRr_bind.
{ eapply (HING LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 (ms_mem ms) _ (4 * Z.of_nat i + 2) (ms_regs ms)
    (SF + V_again) (SlotModel.rec_addr (e_pl g) i) gb (SlotModel.rec_k (e_pl g) i)
    (m_id g i) (SlotModel.rec_pl (e_pl g) i) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite Ura. clear - HBLO. lia.
  - exact Qa0.
  - exact Qa1.
  - exact Qa2.
  - exact Qa3.
  - clear - HSF0 HSF1 C1. unfold V_again. lia.
  - exact Har.
  - clear - Hgb4096 Hgbce Hgreq C1. lia.
  - clear - Hkr. lia.
  - rewrite Usp. clear - Hmf32. lia.
  - rewrite Usp. unfold reac_identity_ingest.INGEST_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite Hpll. reflexivity.
  - intros _. rewrite Usp. split; [exact HRECOK | exact HPAYOK].
  - exact Hnev.
  - exact Hlive. }
cbv beta. intros W3 c3 Hwle3 (-> & regsI & memI & mdI & -> & HJI & HPI & Ha0I & HKI & HbodyI).
(* ---- back at +0x624: re-seat the symbolic state on the havoc'd registers ---- *)
rewrite Rra.
unfold reac_identity_ingest.EV_INGEST in HJI. rewrite Z.add_0_r in HJI.
let K := run_K_hi HS in jafter_call_keep_hi HS K regsI (mrestrict (w_H W2) memI) HPI (@nil nat) HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) by (cbn [ms_mem restrict]; apply Forall_nil) end.
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  assert (HEI2 : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (SHOK2 : sh_ok SEGS Bx_FR [] Ev (mrestrict (w_H W2) memI)) by constructor
end.
clear SHOK HEI0.
paj_run_tok RUN HS HJI SHOK2 Bspan_FR; [apply awr_ok_nil | ].
(* ---- run 2 changed no byte ---- *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) memI a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W2) memI (ms_mem ms0) (fun _ => False) HFr);
  [intros bb wlo whi aa Hin Hr; cbn in Hin; destruct Hin | exact Ha | intros []]. }
clear HF HFr HG.
rewrite Usp in HKI. pose proof HKI as (KI1 & KI2 & KI3 & KI4 & KI5 & KI6).
assert (HEnot : forall a, alloc_ceiling <= a ->
  ~ reac_identity_ingest.ting_E (SF + V_again) gb (SlotModel.rec_k (e_pl g) i) a).
{ intros a Ha (_ & HE'). unfold V_again in HE'. clear - Ha HE' HSF0 HSF1 C1. lia. }
(* bytes of the machine stack above mf: kept by the jal, the ingest call and the two moves *)
assert (MEMB : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - reac_identity_ingest.INGEST_STK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite (KEEP2 a ltac:(clear - Ha C1; lia)).
  rewrite (KI1 a Ha Hw (HEnot a (proj1 Ha))). apply KEEP1. clear - Ha C1. lia. }
assert (STKK : forall a, mf <= a < sp0 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply MEMB; [clear - Ha Hmf0 Hmfb Hshi H47 C1; lia
  | unfold reac_identity_ingest.INGEST_STK, ESTACK; clear - Ha; lia]. }
assert (VSTK : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) a a n v); [|exact Hv].
  intros kk Hkk. apply STKK. clear - H1 H2 Hkk. lia. }
(* ---- the registers at the free ---- *)
prreg HS (1%bv : bv 5) Fra. prreg HS (2%bv : bv 5) Fsp. prreg HS (3%bv : bv 5) Fgp.
prreg HS (4%bv : bv 5) Ftp. prreg HS (8%bv : bv 5) Fs0. prreg HS (10%bv : bv 5) Fa0.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Fsp.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in Fgp.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Ftp.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Fs0.
rewrite (EE 24%nat 24%bv eq_refl), R24 in Fa0.
assert (Usp2 : spZ (ms_regs ms0) = mf)
  by (unfold spZ; rewrite Fsp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (Us02 : s0Z (ms_regs ms0) = sp0)
  by (unfold s0Z; rewrite Fs0; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (Ura2 : raZ (ms_regs ms0) = BASE + 1584)
  by (unfold raZ; rewrite Fra; apply unsigned_lit_small; clear - HBASE; lia).
(* ---- the call chain of the free ---- *)
pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & FJ1 & _).
assert (HCH : exists ch, chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms0)) (ms_regs ms0) ch /\
  (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)])).
{ assert (Ura4 : 4096 <= raZ (ms_regs ms0)) by (rewrite Ura2; clear - HBLO; lia).
  change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; exists sp0, (s0Z (e_regs g)); reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0); [| rewrite Usp2; clear - Hmf0; lia | exact Us02 | exact Ura4].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra1.
    change (bv_modulus 64) with (2 ^ 64) in Rra1.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r.
    change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply FJ1; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra1; lia].
      apply VSTK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra].
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply VSTK; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0].
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. split; [|left; reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0 []); [| rewrite Usp2; clear - Hmf0; lia | exact Us02 | exact Ura4].
    left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch & Hchain & Hchs).
(* ---- the other premises of the free ---- *)
assert (Hi64 : Z.of_nat i < 64).
{ unfold m_nrec, SlotModel.nrecn in Hi. pose proof (SlotModel.nrec_range (e_pl g)). clear - Hi H. lia. }
assert (HnotE : ~ In (gb, SlotModel.rec_k (e_pl g) i + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. destruct Hbl as [Hperm _]. apply in_split in Hin as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly2 S2)
    ((gb, SlotModel.rec_k (e_pl g) i + 1) :: (gb, SlotModel.rec_k (e_pl g) i + 1)
      :: ((pl, SlotModel.rec_k (e_pl g) i) :: l1) ++ l2)).
  { eapply Permutation_trans; [exact Hperm|]. rewrite El. cbn [app].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
    exact (Permutation_sym (Permutation_middle ((pl, SlotModel.rec_k (e_pl g) i) :: l1) l2
      (gb, SlotModel.rec_k (e_pl g) i + 1))). }
  pose proof (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2 (gb, SlotModel.rec_k (e_pl g) i + 1)
    (gb, SlotModel.rec_k (e_pl g) i + 1) (((pl, SlotModel.rec_k (e_pl g) i) :: l1) ++ l2) HAR2 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. clear - Hd Hgreq. lia. }
assert (Hnevf : st_nev S2 < EV_MAX).
{ unfold EV_LLVMF in HEV. clear - Hnev2 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0.
pose proof (mo_free_nonneg MT MTL) as HF0.
assert (MOKf : mo_ok MT S2 (mo_free MT)).
{ apply (mo_ok_le MT MTL S2 (mo_free MT) ((EV_LLVMF - (4 * Z.of_nat i + 2)) * MEV MT) MOK).
  unfold MEV, EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
(* ---- the free of the guard copy, +0x62c ---- *)
pmkst HS. ppcs.
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 2)
    gb (SlotModel.rec_k (e_pl g) i + 1) (mf - sp0) (Z_to_bv 64 (BASE + 1584)) ch HJI Hgin).
  - exact Fa0.
  - rewrite Usp2. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK' Has. lia.
  - exact Fgp.
  - exact Ftp.
  - exact Fra.
  - apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity].
  - exact Hnevf.
  - exact Hchain.
  - destruct Hchs as [-> | (fp & v & ->)].
    + eapply llvmf_univ_call0; [exact HUMF|].
      rewrite Ura2. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS. apply in_or_app. right.
      apply in_map_iff. exists 0x630. split; [reflexivity|]. cbn [In]. left. reflexivity.
    + eapply llvmf_univ_call; [exact HUMF|].
      rewrite Ura2. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS. apply in_or_app. left.
      apply in_map_iff. exists 0x630. split; [reflexivity|]. cbn [In]. left. reflexivity.
  - intros Hin. exfalso. exact (HnotE Hin).
  - exact MOKf. }
cbv beta.
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJF & HPF & (lb1 & lb2 & Ebl & Ebl2) & Hfrs4 & HKF & MLEF & HJfree).
clear HJfree.
replace (sp0 + (mf - sp0)) with mf in HKF by (clear; lia).
pose proof HKF as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6).
(* ---- the transports from the start state to the end state ---- *)
assert (HSF8 : SF mod 8 = 0).
{ pose proof (Z.div_mod SF 64 ltac:(lia)) as D. rewrite HSF64, Z.add_0_r in D.
  rewrite D. replace (64 * (SF / 64)) with (8 * (SF / 64) * 8) by (clear; lia). apply Z.mod_mul. clear. lia. }
assert (STKF : forall a, mf <= a < sp0 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  rewrite (KF1 a ltac:(clear - Ha Hmf0 Hmfb Hshi H47 C1; lia) ltac:(clear - Ha Has; lia)).
  apply STKK. exact Ha. }
assert (VSTKF : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W4 mem4) a n v).
{ intros a n v H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 mem4 a a n v); [|exact Hv].
  intros kk Hkk. apply STKF. clear - H1 H2 Hkk. lia. }
assert (HGBF : forall a, SF <= a < SF + 1024 ->
  ~ (gb <= a < gb + req_size (SlotModel.rec_k (e_pl g) i + 1))).
{ pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 gb (SlotModel.rec_k (e_pl g) i + 1) 4 pos
    HAR2 Hgin Hin4) as Hdf. unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  intros a Ha Hc. clear - Hdf Ha Hc. lia. }
assert (FRD : forall a, SF <= a < SF + 1024 -> ~ (SF + V_again <= a < SF + V_again + 38) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha HnA.
  rewrite (KF4 4 pos a Hin4
    ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa, HFB; exact Ha)
    ltac:(exact (HGBF a Ha))).
  rewrite (KEEP2 a ltac:(clear - Ha HSF0 HSF1 C1; lia)).
  rewrite (KI4 4 pos a Hin4
    ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa, HFB; exact Ha)
    ltac:(intros (_ & HE'); exact (HnA HE'))).
  apply KEEP1. clear - Ha HSF0 HSF1 C1. lia. }
assert (FRS : forall a, shadow_addr SF <= a < shadow_addr SF + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  assert (Hsha : 2147450880 + SF / 8 <= a < 2147450880 + SF / 8 + 128)
    by (unfold shadow_addr, SHADOW_OFF in Ha; exact Ha).
  assert (HnotFr : forall p n, in_app p n -> ~ (p <= a < p + n))
    by (intros p n Hap Hc; exact (fshadow_not_app SF 128 p n a HSF0 ltac:(clear - HSF1 C1; lia) Hap Hsha Hc)).
  assert (Hb64 : 0 <= a < 2 ^ 64).
  { pose proof (shadow_addr_bounds SF ltac:(clear - HSF0 HSF1 C1 C4; lia)) as Hsb.
    clear - Ha Hsb C2 C5. unfold shadow_addr in *. lia. }
  rewrite (KF4 4 pos a Hin4
    ltac:(right; unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; exact Ha)
    ltac:(exact (HnotFr gb (req_size (SlotModel.rec_k (e_pl g) i + 1)) Hgbapp))).
  rewrite (KEEP2 a Hb64).
  rewrite (KI4 4 pos a Hin4
    ltac:(right; unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; exact Ha)
    ltac:(intros (_ & HE'); exact (HnotFr SF 1024 HSFapp ltac:(unfold V_again in HE'; clear - HE'; lia)))).
  apply KEEP1. exact Hb64. }
assert (SHF : forall V N, 0 <= V -> V mod 8 = 0 -> V + N <= 1024 -> 0 <= N ->
  forall ii, 0 <= ii < (N + 7) / 8 ->
  aview SEGS (w_H W4) mem4 (shadow_of_addr SHADOW_OFF (SF + V) + ii)
  = aview SEGS (w_H W2) mem2 (shadow_of_addr SHADOW_OFF (SF + V) + ii)).
{ intros V N HV0 HV8 HVN HN ii Hii. rewrite (d1_shoff SF V HSF8 HV8). apply FRS.
  assert (HVd : 0 <= V / 8) by (apply Z.div_pos; clear - HV0; lia).
  assert (HVd2 : V / 8 + (N + 7) / 8 <= 128).
  { pose proof (Z.div_mod V 8 ltac:(lia)) as D1. pose proof (Z.div_mod (N + 7) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (N + 7) 8 ltac:(lia)) as D3. clear - HVN HV8 HN D1 D2 D3. lia. }
  unfold shadow_addr, shadow_of_addr. clear - Hii HVd HVd2. lia. }
assert (SHZ : forall V N, 0 <= V -> V mod 8 = 0 -> V + N <= 1024 -> 0 <= N ->
  sh_zero W2 mem2 (SF + V) N -> sh_zero W4 mem4 (SF + V) N).
{ intros V N HV0 HV8 HVN HN Hz. unfold sh_zero in *.
  apply (d1_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W4) mem4) SHADOW_OFF (SF + V) N);
  [|exact Hz]. intros ii Hii. apply (SHF V N HV0 HV8 HVN HN ii).
  pose proof (Z.div_mod N 8 ltac:(lia)) as D1. pose proof (Z.div_mod (N + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound N 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (N + 7) 8 ltac:(lia)) as D4.
  clear - Hii HN D1 D2 D3 D4. lia. }
assert (SHB : forall V N, 0 <= V -> V mod 8 = 0 -> V + N <= 1024 -> 0 <= N ->
  sh_blk W2 mem2 (SF + V) N -> sh_blk W4 mem4 (SF + V) N).
{ intros V N HV0 HV8 HVN HN Hb. unfold sh_blk in *.
  apply (block_shadow_agree (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W4) mem4) SHADOW_OFF (SF + V) N);
  [|exact Hb]. intros ii Hii. exact (SHF V N HV0 HV8 HVN HN ii Hii). }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= V_again \/ V_again + 38 <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W4 mem4) (SF + off) n v).
{ intros off n v H0 H1 Hd Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. replace (SF + off + kk) with (SF + (off + kk)) by (clear; lia).
  apply FRD; [clear - H0 H1 Hkk; lia | clear - Hd Hkk H0 H1; lia]. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  (off + Z.of_nat (length l) <= V_again \/ V_again + 38 <= off) ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W4 mem4) (SF + off) l).
{ intros off l H0 H1 Hd Hg. apply (d1_garr8_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (SF + off) l); [|exact Hg].
  intros kk Hkk. replace (SF + off + kk) with (SF + (off + kk)) by (clear; lia).
  apply FRD; [clear - H0 H1 Hkk; lia | clear - Hd Hkk H0 H1; lia]. }
assert (BLK : forall b m j, In (b, m) (ablocks B ly2 S2) ->
  (b, m) <> (gb, SlotModel.rec_k (e_pl g) i + 1) -> 0 <= j < req_size m ->
  aview SEGS (w_H W4) mem4 (b + j) = aview SEGS (w_H W2) mem2 (b + j)).
{ intros b m j Hin Hne Hj.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m gb (SlotModel.rec_k (e_pl g) i + 1)
    HAR2 Hin Hgin Hne) as Hdb. unfold zdisjoint in Hdb. cbn [fst snd] in Hdb.
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR2 Hin Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  rewrite (KF2 b m j Hin Hj ltac:(clear - Hdb Hj; lia)).
  rewrite (KEEP2 (b + j) ltac:(clear - Hj Hb4096 Hbce C1; lia)).
  rewrite (KI2 b m j Hin Hj ltac:(intros (_ & HE'); unfold V_again in HE'; clear - HE' Hdf Hj; lia)).
  apply KEEP1. clear - Hj Hb4096 Hbce C1. lia. }
(* the new `again` bytes, as the model's next record *)
destruct (d1_ing_model (e_pl g) i (SF + V_again) gb
  ltac:(clear - HSF0; unfold V_again; lia) ltac:(clear - Hgb4096; lia)) as (Mrf & Mret & Mid).
pose proof (HbodyI Mrf) as HBID. unfold m_id in HBID. rewrite Mid in HBID.
assert (AGNF : forall j, 0 <= j < 38 ->
  aview SEGS (w_H W4) mem4 (SF + V_again + j) = aview SEGS (w_H W2) memI (SF + V_again + j)).
{ intros j Hj.
  rewrite (KF4 4 pos (SF + V_again + j) Hin4
    ltac:(left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa, HFB;
          unfold V_again in *; clear - Hj HSF0 HSF1; lia)
    ltac:(exact (HGBF (SF + V_again + j) ltac:(unfold V_again in *; clear - Hj HSF0 HSF1; lia)))).
  apply KEEP2. unfold V_again in *. clear - Hj HSF0 HSF1 C1. lia. }
assert (AGNB : bytes_at8 W4 mem4 (SF + V_again) (m_id g (S i))).
{ unfold bytes_at8, m_id. apply (d1_gb SEGS). intros j Hj.
  rewrite (mbyte_of_aview SEGS (w_H W2) (w_H W4) memI mem4 (SF + V_again + Z.of_nat j)
    (AGNF (Z.of_nat j) ltac:(rewrite SlotModel.rec_id_length in Hj;
                             unfold RcIdentModel.ID_SIZE in Hj; clear - Hj; lia))).
  exact (HBID j Hj). }
(* the input block and the payload copy *)
assert (HINB : bytes_at8 W4 mem4 (e_p g) (e_pl g)).
{ unfold bytes_at8 in *. apply (d1_garr8_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (e_p g) _); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. right. exact Hine. }
  assert (Hne : (e_p g, e_n g) <> (gb, SlotModel.rec_k (e_pl g) i + 1))
    by (intros Heq; rewrite Heq in Hine; exact (HnotE Hine)).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply (BLK (e_p g) (e_n g) j Hine2 Hne). clear - Hj Hrq. lia. }
assert (HPLB : bytes_at8 W4 mem4 pl (SlotModel.rec_pl (e_pl g) i)).
{ unfold bytes_at8 in *. apply (d1_garr8_moved SEGS (w_H W2) (w_H W4) mem2 mem4 pl _); [|exact Hplb].
  intros j Hj. rewrite length_map, Hpll in Hj.
  assert (Hne : (pl, SlotModel.rec_k (e_pl g) i) <> (gb, SlotModel.rec_k (e_pl g) i + 1))
    by (intros Heq; injection Heq as _ Hk1; clear - Hk1; lia).
  apply (BLK pl (SlotModel.rec_k (e_pl g) i) j Hplin Hne). clear - Hj Hkr Hplreq. lia. }
(* ---- the registers at +0x630 ---- *)
let K := run_K_hi HS in jafter_call_keep_hi HS K regs4 (mrestrict (w_H W4) mem4) HPF (@nil nat) HS4.
lazymatch type of HS4 with ?Q -> _ => assert (HQ : Q) by (cbn [ms_mem restrict]; apply Forall_nil) end.
specialize (HS4 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18.
prreg HS (20%bv : bv 5) G20. prreg HS (22%bv : bv 5) G22. prreg HS (26%bv : bv 5) G26.
prreg HS (27%bv : bv 5) G27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in G2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in G3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in G4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in G8.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in G9.
rewrite (EE 18%nat 18%bv eq_refl), R18 in G18.
rewrite (EE 20%nat 20%bv eq_refl), R20 in G20.
rewrite (EE 22%nat 22%bv eq_refl), R22 in G22.
rewrite (EE 27%nat 27%bv eq_refl), R27 in G27.
assert (E516 : nth 4 (map (getr regsI) CLOB) (ew E 516) = getr regsI 10%bv) by reflexivity.
rewrite E516, Ha0I in G26. unfold m_id in G26. rewrite Mret in G26.
(* ---- the boundary inv_D1_end at +0x630 ---- *)
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF) as [Efd Efs].
assert (Hnlen : SlotModel.nlen (e_pl g) = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
pose proof (SlotModel.rec_c_range (e_pl g) (S i)) as Hcr. rewrite Hnlen in Hcr.
assert (Lid : forall j, Z.of_nat (length (map (fun b : byte => bv_unsigned b) (m_id g j))) = 38)
  by (intros j; rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length; reflexivity).
assert (Lhw : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (m_hwb g i))) = 8)
  by (rewrite length_map; unfold m_hwb; rewrite d1_hwb_length; reflexivity).
apply SRr_ret. unfold inv_D1_end, acut.
exists ly4, S4, regs4, mem4, md4.
split; [reflexivity|].
split; [replace (4 * Z.of_nat i + 3) with (4 * Z.of_nat i + 2 + 1) by (clear; lia); exact HJF|].
split; [rewrite Hfrs4; exact Hfrs|].
split; [unfold EV_LLVMF; clear - Hi64; lia|].
split.
{ eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLEF)|].
  unfold MEV. clear - HM0 HF0. nia. }
split.
{ apply (mo_ok_step MT MTL S2 S4 (mo_free MT)); [|exact MLEF].
  apply (mo_ok_le MT MTL _ _ _ MOK). unfold MEV, EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
split.
{ unfold ecommon. fold sp0. fold SF.
  split; [exact G2|]. split; [exact G9|]. split; [exact G8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact G3|]. split; [exact G4|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W24]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W32]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W40]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W48]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W56]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W64]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W72]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W80]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W88]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W96]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact W104]|].
  split; [apply (VMF 1016 8%nat); [clear; lia | clear; lia | unfold V_again; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
split.
{ unfold P_body. fold SF.
  split; [exact Hi|].
  split.
  { split; [|constructor; [cbn [fst snd]; split; [exact Hpl4096 | clear - Hkr; lia] | constructor]].
    rewrite Ebl2. cbn [app]. destruct Hbl as [Hperm _]. rewrite Ebl in Hperm. cbn [app] in Hperm.
    apply (Permutation_cons_inv (a := (gb, SlotModel.rec_k (e_pl g) i + 1))).
    eapply Permutation_trans; [apply Permutation_middle|].
    eapply Permutation_trans; [exact Hperm|]. apply perm_swap. }
  split; [exact HPLB|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidbl).
    split.
    { unfold bytes_at8 in *. apply (GF V_id);
      [unfold V_id; clear; lia | rewrite (Lid (S i)); unfold V_id; clear; lia
       | rewrite (Lid (S i)); unfold V_id, V_again; clear; lia | exact Hidb]. }
    split.
    { apply (SHZ V_id N_id); [unfold V_id; clear; lia | unfold V_id; reflexivity
      | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz]. }
    apply (SHB V_id N_id); [unfold V_id; clear; lia | unfold V_id; reflexivity
      | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidbl]. }
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split.
  { destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
    unfold mf_fixed. fold SF.
    repeat split; apply VSTKF; first [assumption | clear - Hmfb; lia]. }
  split; [unfold mf_before; fold SF; apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hbef]|].
  split; [unfold mf_again; fold SF; apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hagn]|].
  split; [unfold mf_id; fold SF; apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
  split; [exact G22|].
  split; [exact G27|].
  unfold m_cur. clear - Hcr. lia. }
split.
{ destruct Hhw as ((Hhwb & Hhwz & Hhwbl) & Hhw4 & Hhwm).
  fold SF in Hhwb. replace (SF + V_hw + 4) with (SF + 436) in Hhwb by (unfold V_hw; clear; lia).
  unfold hw_live, hw_mem. fold SF.
  replace (SF + V_hw + 4) with (SF + 436) by (unfold V_hw; clear; lia).
  split.
  { split.
    { unfold bytes_at8 in *. apply (GF 436);
      [clear; lia | rewrite Lhw; clear; lia | rewrite Lhw; unfold V_again; clear; lia | exact Hhwb]. }
    split.
    { apply (SHZ V_hw N_hw); [unfold V_hw; clear; lia | unfold V_hw; reflexivity
      | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhwz]. }
    apply (SHB V_hw N_hw); [unfold V_hw; clear; lia | unfold V_hw; reflexivity
      | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhwbl]. }
  split.
  { apply (VMF V_hw 4%nat); [unfold V_hw; clear; lia | unfold V_hw; clear; lia
    | unfold V_hw, V_again; clear; lia | exact Hhw4]. }
  apply VSTKF; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hhwm]. }
split.
{ apply (SHB V_before N_before); [unfold V_before; clear; lia | unfold V_before; reflexivity
  | unfold V_before, N_before; clear; lia | unfold N_before; clear; lia | exact Hbefs]. }
split.
{ apply (SHB V_again N_again); [unfold V_again; clear; lia | unfold V_again; reflexivity
  | unfold V_again, N_again; clear; lia | unfold N_again; clear; lia | exact Hagns]. }
split.
{ unfold bytes_at8 in *. apply (GF V_before);
  [unfold V_before; clear; lia | rewrite (Lid i); unfold V_before; clear; lia
   | rewrite (Lid i); unfold V_before, V_again; clear; lia | exact Hbefb]. }
split; [exact AGNB|].
split; [exact G18|].
split; [exact G20|].
exact G26.
Qed.


(* ---- the segment: the six stretches chained ---------------------------------------------------------- *)
Theorem seg_D1 : seg_D1_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i W2 c2 Hstart.
eapply SRr_bind; [exact (d1_hdr3 g pos mf i W2 c2 Hstart)|].
cbv beta. intros W3 c3 _ H3.
eapply SRr_bind; [exact (d1_m_c1 g pos mf i W3 c3 H3)|].
cbv beta. intros W4 c4 _ H4.
eapply SRr_bind; [exact (d1_c1_c2 g pos mf i W4 c4 H4)|].
cbv beta. intros W5 c5 _ (pl & H5).
eapply SRr_bind; [exact (d1_c2_c4 g pos mf i pl W5 c5 H5)|].
cbv beta. intros W6 c6 _ H6.
eapply SRr_bind; [exact (d1_c4_c6 g pos mf i pl W6 c6 H6)|].
cbv beta. intros W7 c7 _ (gb & H7).
eapply SRr_mono; [exact (d1_c6_end g pos mf i pl gb W7 c7 H7)|].
cbv beta. intros W8 c8 _ H8. exists pl. exact H8.
Qed.
Check (seg_D1 : seg_D1_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
