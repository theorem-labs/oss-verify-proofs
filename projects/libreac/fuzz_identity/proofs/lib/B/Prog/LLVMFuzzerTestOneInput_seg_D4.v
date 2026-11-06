(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACim.v:270-271 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530, 1556-1561 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Segment D4 of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan): the model-name case,
   0x812b8..0x81598 (BASE + 0xb44 .. BASE + 0xe24). seg_D4 of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v: from the
   case's entry inv_caseM to the join inv_tail.

   The code (the neutral listing of fuzz_identity.asan-ubsan, what each instruction does):
     0x812b8 .. 0x812c4  a2 := 17, a0 := mf+136 (= &id.model_name), a1 := 0; call memchr (0x4220c)
     0x812c8             abort unless s3 (id.has_model_name, set at 0x80df8) is not 0
     0x812d0, 0x812d8    abort unless the result is not NULL and not &id.model_name (a name of at least one byte)
     0x812e4 .. 0x812f0  s2 := len (result - &id.model_name), s3 := len + 1; abort unless len + 1 <= k (s6)
     0x812f8 .. 0x81304  UBSan: trap unless pl + 1 does not wrap (pl = s11, the payload copy)
     0x81308 .. 0x81310  call bcmp (0x42208) on &id.model_name, pl + 1, len
     0x81314 .. 0x8131c  a2 := mf+168 (the shadow base); abort unless the result is 0
     0x81320, 0x81328    join (0x81598) when len > 15 or len + 1 >= k
     0x8132c .. 0x81344  UBSan: trap unless pl <> 0 and pl + len + 1 neither wraps nor is 0
     0x81348 .. 0x81360  the ASan check of the byte at pl + len + 1 (report at 0x82728)
     0x8158c .. 0x81594  join when that byte is 0, else abort
   The plain model (lib/Prog/RcIdentModel.v ing_name): in this case the first ingest copied the w = name_len pl
   bytes pl[1 .. w] into id.model_name, then a NUL, and set has_model_name; pl[w + 1] = 0 when w < 16 and
   w + 1 < k. So memchr finds the NUL at w, bcmp answers 0 and the stopped-early byte is 0.
   The memchr call is stated against lib/B/Rt/MemchrDef.v
   (premises over all n bytes, result `exists k, first_byte ...`). *)
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
(* the pieces proved from this segment's statements file (seg_D4_hand_stmt.v) *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_D4_hand_stmt LLVMFuzzerTestOneInput_seg_D4_hand_kill
LLVMFuzzerTestOneInput_seg_D4_hand_ewclob LLVMFuzzerTestOneInput_seg_D4_hand_block_read
LLVMFuzzerTestOneInput_seg_D4_hand_frame_read.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import MemchrDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address arithmetic of
   this segment (shadow addresses, the frame's 64-byte alignment) needs it, so this file turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model of the case (lib/Prog/SlotModel.v, RcIdentModel.v) ---------------------------------- *)
(* The model lemmas of the released plain walk (lib/Prog/Seg/Tac_sb3.v n_fz_len .. n_nma, Seg/B28.v n28_name0 and
   n28_hw), restated here: those files are address-bound and are not loaded by the B walk. *)
Module D4M.
Import RcIdentModel SlotModel.
Lemma d4_fz_len : forall l, (first_zero l <= length l)%nat.
Proof.
induction l as [|b l IH]; cbn [first_zero length]; [lia|].
destruct (bz b =? 0); lia.
Qed.
Lemma d4_fz_prefix : forall l r, first_zero (firstn (first_zero l) l ++ zb 0 :: r) = first_zero l.
Proof.
induction l as [|b l IH]; intros r; [reflexivity|].
cbn [first_zero].
destruct (bz b =? 0) eqn:E; [reflexivity|].
cbn [firstn app first_zero]. rewrite E. cbv iota. f_equal. apply IH.
Qed.
Lemma d4_name_len_fz : forall p, name_len p = first_zero (firstn (Nat.min (length p - 1) (NAME_CAP - 1)) (skipn 1 p)).
Proof.
intro p. unfold name_len. cbv zeta.
pose proof (d4_fz_len (firstn (Nat.min (length p - 1) (NAME_CAP - 1)) (skipn 1 p))) as H.
rewrite length_firstn in H. lia.
Qed.
Lemma d4_name_fz : forall p r, first_zero (firstn (name_len p) (skipn 1 p) ++ zb 0 :: r) = name_len p.
Proof.
intros p r.
replace (firstn (name_len p) (skipn 1 p)) with
  (firstn (name_len p) (firstn (Nat.min (length p - 1) (NAME_CAP - 1)) (skipn 1 p))).
2: { rewrite firstn_firstn. f_equal. unfold name_len. cbv zeta. lia. }
rewrite d4_name_len_fz. apply d4_fz_prefix.
Qed.
Lemma d4_get_upd : forall (l bs : list byte) off m, (off + length bs <= length l)%nat -> (length bs <= m)%nat ->
  exists r, get (upd l off bs) off m = bs ++ r.
Proof.
intros l bs off m H1 H2. unfold get, upd.
rewrite skipn_app, length_firstn.
assert (E : skipn off (firstn off l) = []) by (apply skipn_all2; rewrite length_firstn; lia).
rewrite E. replace (off - Nat.min off (length l))%nat with 0%nat by lia.
replace (skipn 0 (bs ++ skipn (off + length bs) l)) with (bs ++ skipn (off + length bs) l) by reflexivity.
cbn [List.app]. exists (firstn (m - length bs) (skipn (off + length bs) l)).
rewrite firstn_app. f_equal. apply firstn_all2. lia.
Qed.
(* The model-name case with r = 1: id.has_model_name = 1, the name is the w = name_len pl bytes pl[1 .. w], its
   NUL is at w, 1 <= w and w + 1 <= k. *)
Lemma d4_nma : forall inp i, rec_r inp i = 1 -> rec_addr inp i = ADDR_MODEL_NAME ->
  has_model_name (rec_id inp (S i)) = 1 /\
  first_zero (model_name (rec_id inp (S i))) = name_len (rec_pl inp i) /\
  (1 <= name_len (rec_pl inp i))%nat /\
  (name_len (rec_pl inp i) + 1 <= length (rec_pl inp i))%nat /\
  firstn (name_len (rec_pl inp i)) (skipn 3 (rec_id inp (S i))) =
    firstn (name_len (rec_pl inp i)) (skipn 1 (rec_pl inp i)).
Proof.
intros inp i Hr Ha. unfold rec_r in Hr. cbn [rec_id]. rewrite Ha in *.
pose proof (rec_id_length inp i) as Lid. revert Hr Lid.
generalize (rec_id inp i) (rec_pl inp i). intros idb p Hr Lid.
pose proof (name_len_le p) as [Wa Wb].
change (ING idb ADDR_MODEL_NAME p) with (ing_name idb p) in *.
unfold ing_name in *. cbv zeta in *. revert Hr.
destruct ((2 <=? length p)%nat && (1 <=? name_len p)%nat) eqn:C; cbn [fst snd]; intros Hr; [|discriminate Hr].
apply andb_true_iff in C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.leb_le in C2.
set (w := name_len p) in *.
set (X := firstn w (skipn 1 p) ++ [zb 0]).
assert (LA : length (firstn w (skipn 1 p)) = w) by (rewrite length_firstn, length_skipn; lia).
assert (LX : length X = S w) by (unfold X; rewrite length_app, LA; cbn [length]; lia).
unfold OFF_NAME, OFF_HAS_NAME, ID_SIZE in *.
assert (LU : length (upd idb 3 X) = 38%nat) by (rewrite upd_length; lia).
destruct (d4_get_upd idb X 3 17) as [r Er]; [lia|lia|].
split.
{ unfold has_model_name, nthb, OFF_HAS_NAME.
  rewrite nth_upd_in by (rewrite ?LU; cbn [length]; lia). reflexivity. }
split.
{ unfold model_name, OFF_NAME, NAME_CAP.
  rewrite get_upd_after by (rewrite ?LU; lia). rewrite Er. unfold X. rewrite <- app_assoc. cbn [app].
  apply d4_name_fz. }
split; [exact C2|]. split; [lia|].
transitivity (firstn w (get (upd (upd idb 3 X) 20 [zb 1]) 3 17)).
{ unfold get. rewrite firstn_firstn. f_equal. lia. }
rewrite get_upd_after by (rewrite ?LU; lia). rewrite Er. unfold X. rewrite <- app_assoc.
rewrite firstn_app, LA, Nat.sub_diag, firstn_O, app_nil_r.
apply firstn_all2. rewrite LA. lia.
Qed.
Lemma d4_fz_nth : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
induction l as [|b l IH]; cbn [length first_zero]; intros H; [lia|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; [exact E|].
cbn [nth]. apply IH. lia.
Qed.
Lemma d4_fz_before : forall l j, (j < first_zero l)%nat -> bz (nth j l (zb 0)) <> 0.
Proof.
induction l as [|b l IH]; intros j H; cbn [first_zero] in H; [lia|].
destruct (Z.eqb_spec (bz b) 0) as [E|E]; [lia|].
destruct j as [|j]; cbn [nth]; [exact E|]. apply IH. lia.
Qed.
(* The stopped-early byte: pl[w + 1] = 0 when w < min (k - 1) 16. *)
Lemma d4_name0 : forall p, (name_len p < Nat.min (length p - 1) 16)%nat -> bz (nthb p (S (name_len p))) = 0.
Proof.
intros p H.
set (n' := Nat.min (length p - 1) (NAME_CAP - 1)).
assert (Ln : length (firstn n' (skipn 1 p)) = n') by (rewrite length_firstn, length_skipn; unfold n', NAME_CAP; lia).
pose proof (d4_name_len_fz p) as E. fold n' in E.
assert (Hn : (first_zero (firstn n' (skipn 1 p)) < length (firstn n' (skipn 1 p)))%nat)
  by (rewrite Ln, <- E; unfold n', NAME_CAP; lia).
pose proof (d4_fz_nth _ Hn) as Z0. rewrite <- E in Z0.
rewrite nth_first in Z0 by (unfold n', NAME_CAP in *; lia).
clear -Z0 H. unfold nthb. destruct p as [|x r]; [cbn in H; lia|]. cbn [skipn] in Z0. cbn [nth]. exact Z0.
Qed.
Lemma d4_hw : forall inp i, rec_addr inp i = ADDR_MODEL_NAME -> rec_hw inp (S i) = rec_hw inp i.
Proof. intros inp i H. cbn [rec_hw]. rewrite H. reflexivity. Qed.
(* The bytes of id.model_name are id[3 ..]. *)
Lemma d4_mn_nth : forall idb j, length idb = ID_SIZE -> (j < 17)%nat -> nth j (model_name idb) (zb 0) = nth (3 + j) idb (zb 0).
Proof.
intros idb j Hl Hj. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
rewrite (nth_skip0 (skipn 3 idb)), skipn_skipn, <- nth_skip0. f_equal. lia.
Qed.
Lemma d4_mn_len : forall idb, length idb = ID_SIZE -> length (model_name idb) = 17%nat.
Proof. intros idb Hl. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite length_firstn, length_skipn, Hl. unfold ID_SIZE. lia. Qed.
Lemma d4_hwb_length : forall inp i, length (rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold rec_hwb.
assert (H : match rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [rec_hw]; [exact I|].
  destruct ((rec_addr inp i =? ADDR_REAC_VERSION) && (8 <=? rec_k inp i)) eqn:Hc; [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, rec_pl_length. lia. }
destruct (rec_hw inp i); [exact H | reflexivity].
Qed.
Lemma d4_nth_skip : forall m (l : list byte) j d, nth j (skipn m l) d = nth (m + j)%nat l d.
Proof.
induction m as [|m IH]; intros l j d; [reflexivity|].
destruct l as [|b l]; cbn [skipn nth Nat.add]; [destruct j; reflexivity | apply IH].
Qed.
End D4M.
(* The unsigned value of an atom's offset and of a literal, for the branch conditions. *)
Lemma d4_U_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof.
intros E n c v Hn Hv Hvc. rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma d4_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. Qed.

(* ---- the symbolic states -------------------------------------------------------------------------------------- *)
(* Atoms of the environment: 0 .. 31 the registers at 0x812b8, 32 the shadow base SB (mf+168), 33 = x =
   &id.model_name (mf+136), 34 = q = pl + w + 1 (the stopped-early byte), 35 = w. Region 0: the two machine-frame
   words the segment loads, base s1 (atom 9), read-only. The alias says the code's pl + (w + 1) is atom 34. *)
Definition d4_mf : YP09.region := YP09.mkRegion (Some 9%nat) 136 176 136 136
  [YP09.mkChunk 136 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition d4_q : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition d4_facts : facts :=
  mkFacts [(19%nat, mkAF 1 1 0); (32%nat, mkAF SB SB 0); (34%nat, mkAF 1 (2 ^ 47 - 1) 0)] []
  [(SAlu ALU_ADD (SOff 35 1) (SOff 27 0), SOff 34 0)].
Definition d4_ss : sstate := mkSS 0xb44 sr_atoms [d4_mf] None d4_facts.
Definition D4Bx : sv := SOff 32 0.
Definition d4_SH : list shent := [mkSHE 34 0 1].
Definition d4_extra (x q w : Z) : list word := map (Z_to_bv 64) [SB; x; q; w].

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
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- memory helpers -------------------------------------------------------------------------------------------- *)
Lemma d4_aview_bytes : forall (W : world SEGS) m a bs j, bytes_at8 W m a bs -> (j < length bs)%nat ->
  aview SEGS (w_H W) m (a + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
intros W m a bs j H Hj. unfold bytes_at8 in H.
destruct (H j ltac:(rewrite length_map; exact Hj)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
replace (nth j (map (fun b : byte => bv_unsigned b) bs) 0) with (bv_unsigned (nth j bs (Z_to_bv 8 0)))
  by (rewrite <- (map_nth (fun b : byte => bv_unsigned b) bs (Z_to_bv 8 0) j); reflexivity).
pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (bv_modulus 8) with 256. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned (nth j bs (Z_to_bv 8 0))) 256) by lia. reflexivity.
Qed.
Lemma d4_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma d4_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd0 rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
(* A byte the view shows as 0 is a 1-byte value 0 (lib/B/Prog/check_str.v cs_val_mem1). *)
Lemma d4_val_mem1 : forall H mem a, aview SEGS H mem a = Some 0 -> val_mem SEGS (mrestrict H mem) a 1 0.
Proof.
intros H mem a Hz j Hj. assert (j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H mem (a + Z.of_nat 0) 0 ltac:(rewrite Z.add_0_r; exact Hz)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
(* The first byte equal to c in [x, x + n) is the one at w when the bytes before w differ from c and the byte at w
   is c. *)
Lemma d4_first_byte_eq : forall (W : world SEGS) m x n c kk w,
  first_byte SEGS W m x n c kk ->
  (forall j, 0 <= j < w -> exists b, aview SEGS (w_H W) m (x + j) = Some b /\ b <> c) ->
  aview SEGS (w_H W) m (x + w) = Some c -> 0 <= w < n -> kk = w.
Proof.
intros W m x n c kk w (Hk & Hlt & Hat) Hb Hw Hwn.
destruct (Z.lt_trichotomy kk w) as [H | [H | H]]; [exfalso | exact H | exfalso].
- destruct (Hb kk ltac:(lia)) as (b & Eb & Nb). rewrite (Hat ltac:(lia)) in Eb. injection Eb as Eb. exact (Nb (eq_sym Eb)).
- destruct (Hlt w ltac:(lia)) as (b & Eb & Nb). rewrite Hw in Eb. injection Eb as Eb. exact (Nb (eq_sym Eb)).
Qed.

(* ---- the memchr call ----------------------------------------------------------------------------------------- *)
(* The memchr wrapper (lib/B/Rt/MemchrDef.v amemchr_realizes) at a slot of a journal: the journal goes on through
   the call (it writes only the ESTACK window below sp), as YCbq.v aj_memcmp_at does for memcmp. *)
Lemma d4_memchr_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
  0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok SEGS W regsT memT x n -> amem_range x n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\
     (exists kk, first_byte SEGS W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
  HJ Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg Hbud);
  [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (AMEMCHR lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsx Hmx Hrx Hhx Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ---- the join -------------------------------------------------------------------------------------------- *)
(* The three paths to 0x81598 (0x81324, 0x81328 and 0x8158c) reach it with the state of the case's entry: the
   case writes nothing, and the two wrapper calls write only their window below sp = mf. So inv_tail follows
   from inv_caseM's facts transported over `mem' agrees with mem2 outside [mf - 8192, mf)`, with hw_live at
   S i, which is hw_live at i because this case does not touch `hw` (d4_hw). *)
Lemma d4_post : forall g pos mf i pl ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs' mem' md' (k : Z),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem' md' k ->
  k = 4 * Z.of_nat i + 3 ->
  frames S2 = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) ->
  ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  P_body B g pos mf i pl ly2 S2 W2 regs2 mem2 ->
  hw_live g pos mf i W2 mem2 ->
  SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_MODEL_NAME ->
  AR_laws SEGS B ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) -> aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem2 a) ->
  getr regs' 2 = w64 mf -> getr regs' 9 = w64 mf -> getr regs' 8 = w64 (e_sp0 g) ->
  getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
  getr regs' 22 = w64 (SlotModel.rec_k (e_pl g) i) -> getr regs' 27 = w64 pl ->
  inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf i pl W2 (cfg_at SEGS (BASE + 0xe24) regs' mem' md').
Proof.
intros g pos mf i pl ly2 S2 W2 regs2 mem2 md2 regs' mem' md' k HJ -> Hfrs Hk MLE MOK HC HP Hhw Haddr LAWS' KEEP
  R2 R9 R8 R3 R4 R22 R27.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64s & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS' ly2 S2 W2 mem' md' 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem' md' 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
(* the transports *)
assert (VM : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem') a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem' a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 C1; lia. }
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem') a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem' a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 Hmfb Hshi H47 C1; lia. }
assert (GA : forall a l, 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem') a l).
{ intros a l H1 H2 Hg. apply (d4_garr8_moved (w_H W2) (w_H W2) mem2 mem' a l); [|exact Hg].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 C1; lia. }
assert (SHZ : forall a n, 0 <= a -> a + n <= alloc_ceiling -> 0 <= n ->
  sh_zero W2 mem2 a n -> sh_zero W2 mem' a n).
{ intros a n H1 H2 Hn Hz. unfold sh_zero in *.
  apply (d4_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem') SHADOW_OFF a n); [|exact Hz].
  intros ii Hii. apply KEEP.
  - unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 Hn Hii Hmf0 C1. lia.
  - unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 Hn Hii Hmf0 C1. lia. }
assert (SHB : forall a n, 0 <= a -> a + n <= alloc_ceiling -> 0 <= n ->
  sh_blk W2 mem2 a n -> sh_blk W2 mem' a n).
{ intros a n H1 H2 Hn (Ha8 & Hn0 & Hb). split; [exact Ha8|]. split; [exact Hn0|].
  intros ii Hii. rewrite <- (Hb ii Hii). apply KEEP.
  - unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 Hn Hii Hmf0 C1. lia.
  - unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 Hn Hii Hmf0 C1. lia. }
(* the input block, for bytes_at8 of the input *)
assert (Hn0 : 0 <= e_n g) by (rewrite Hlen; lia).
assert (HINB : bytes_at8 W2 mem' (e_p g) (e_pl g)).
{ destruct Hinp as [[Hne Hpe] | [[Hnp Hn26] Hine]].
  - unfold bytes_at8 in *. intros j Hj. rewrite length_map in Hj.
    exfalso. clear - Hj Hne Hlen. lia.
  - destruct HP as (_ & Hbl & _).
    assert (Hpn2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hine. }
    destruct (al_blocks _ _ LAWS' ly2 S2 W2 mem' md' (e_p g) (e_n g) HAR2 Hpn2) as (_ & Hp4096 & Hpce & _ & _).
    pose proof (req_size_pos (e_n g) Hn0) as Hrq.
    apply GA; [clear - Hp4096; lia | rewrite length_map, <- Hlen; clear - Hpce Hrq; lia | exact Hinb]. }
(* the payload copy's place *)
destruct HP as (Hi & Hbl & Hpl & Hid & V96n & Hfix & Hbef & Hmag & Hmid & V112 & V120 & V128 & _ & _ & Hcur).
assert (Hinpl : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS' ly2 S2 W2 mem' md' pl (SlotModel.rec_k (e_pl g) i) HAR2 Hinpl)
  as (_ & Hpl4096 & Hplce & _ & _).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr.
pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as Hrqk.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Hpll.
(* hw at S i is hw at i: this case does not touch `hw` *)
assert (EHW : m_hwb g (S i) = m_hwb g i /\ m_have g (S i) = m_have g i).
{ unfold m_hwb, m_have, SlotModel.rec_hwb, SlotModel.rec_have.
  rewrite (D4M.d4_hw (e_pl g) i Haddr). split; reflexivity. }
destruct EHW as [EHWB EHAVE].
(* assemble *)
exists ly2, S2, regs', mem', md'.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact R3|]. split; [exact R4|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64s]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VM; [clear - HSF0; lia | clear - HSF1; lia | exact Vflag]|].
  split; [exact HPRE|].
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  split; [intros fd; rewrite Efd; reflexivity|]. split; [rewrite Efs; reflexivity | exact HINB]. }
split.
{ unfold P_body.
  split; [exact Hi|]. split; [exact Hbl|].
  split; [apply GA; [clear - Hpl4096; lia | rewrite length_map, Hpll; clear - Hplce Hrqk Hkr; lia | exact Hpl]|].
  split.
  { destruct Hid as (Hidb & Hidz & Hidbl). split; [|split].
    - apply GA; [clear - HSF0; unfold V_id; lia | | exact Hidb].
      rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
      unfold V_id, RcIdentModel.ID_SIZE. clear - HSF1; lia.
    - apply SHZ; [clear - HSF0; unfold V_id; lia | unfold V_id, N_id; clear - HSF1; lia
      | unfold N_id; lia | exact Hidz].
    - apply SHB; [clear - HSF0; unfold V_id; lia | unfold V_id, N_id; clear - HSF1; lia
      | unfold N_id; lia | exact Hidbl]. }
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96n]|].
  split.
  { destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
    unfold mf_fixed. repeat split; apply VMS; first [assumption | clear - Hmfb; lia]. }
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hbef]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmag]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V120]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V128]|].
  split; [exact R22|]. split; [exact R27 | exact Hcur]. }
destruct Hhw as ((Hhwb & Hhwz & Hhwbl) & Hhw4 & Hhw24).
split; [|split].
- split; [|split].
  + rewrite EHWB. apply GA; [clear - HSF0; unfold V_hw; lia | | exact Hhwb].
    rewrite length_map. unfold m_hwb. rewrite D4M.d4_hwb_length. unfold V_hw. clear - HSF1; lia.
  + apply SHZ; [clear - HSF0; unfold V_hw; lia | unfold V_hw, N_hw; clear - HSF1; lia
    | unfold N_hw; lia | exact Hhwz].
  + apply SHB; [clear - HSF0; unfold V_hw; lia | unfold V_hw, N_hw; clear - HSF1; lia
    | unfold N_hw; lia | exact Hhwbl].
- apply VM; [clear - HSF0; unfold V_hw; lia | clear - HSF1; unfold V_hw; lia | exact Hhw4].
- rewrite EHAVE. apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hhw24].
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
(* A run of this segment writes nothing (the case has no store), so every run keeps the bytes its predecessor
   kept; the two calls keep everything outside their window below sp = mf. *)
Lemma d4_keep_run : forall E rs (W : world SEGS) (m0 m1 m2 : word -> option byte) lo hi,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> False) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m0 a).
Proof.
intros E rs W m0 m1 m2 lo hi HFr Hw HK a Ha Hn.
rewrite <- (HK a Ha Hn). apply (kept_of_frame E rs (w_H W) m1 m2 (fun _ => False) HFr); [|exact Ha|intros []].
intros bb wlo whi aa Hin Hr. exact (Hw bb wlo whi aa Hin Hr).
Qed.
(* An alias fact at the pi level: add_alias touches only the facts, which abs_ss keeps. *)
Lemma d4_add_alias : forall E ss ms a b,
  st_ok_pi SEGS VAL E ss ms -> sv_denot E a = sv_denot E b ->
  st_ok_pi SEGS VAL E (add_alias ss a b) ms.
Proof.
intros E ss ms a b HS Hab. unfold st_ok_pi, abs_ss in *.
exact (st_ok_add_alias SEGS E (setpc ss (BASE + ss_pc ss)) ms a b HS Hab).
Qed.

(* The kept-bytes fact KEEP carried through the run that just ended (its frame_of is HFr): a run of this segment
   writes nothing, every window of its regions is empty. *)
Local Ltac d4_keep KEEP HF HG :=
  let K' := fresh "KEEPn" in
  lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
  pose proof (d4_keep_run _ _ _ _ _ _ _ _ HFr
    ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
          repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
    KEEP) as K'; clear KEEP HFr end;
  clear HF HG; rename K' into KEEP.
(* A register's value read back from the environment: drop the call havocs and the load extensions above it. *)
Local Ltac d4_ewnorm H := repeat first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia].

Lemma seg_D4 : seg_D4_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
unfold seg_D4_stmt. intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HPall).
pose proof HC as HCfull. pose proof HPall as (HPB & Hhw & Hr1 & Haddr & R19).
pose proof HPB as HPBfull.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64s & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HPB as (Hi & Hbl & Hpl & Hid & V96n & Hfix & Hbef & Hmag & Hmid & V112 & V120 & V128 & R22 & R27 & Hcur).
destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
destruct Hid as (Hidb & Hidz & Hidbl).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _ & Hro0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic & _).
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
(* ---- the model of this record ---- *)
pose proof (D4M.d4_nma (e_pl g) i Hr1 Haddr) as (Hmn1 & Hfz & Hw1 & Hwk & Hpre).
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr.
pose proof (SlotModel.rec_pl_length (e_pl g) i) as Hpll.
pose proof (SlotModel.name_len_le (SlotModel.rec_pl (e_pl g) i)) as [Hw16 _].
assert (Hidlen : length (m_id g (S i)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
set (kb := SlotModel.rec_k (e_pl g) i) in *.
set (w := Z.of_nat (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))).
set (x := SF + V_id + 3) in *.
set (q := pl + w + 1).
assert (Eq_q : q = pl + w + 1) by reflexivity.
assert (Hwlo : 1 <= w) by (unfold w; lia).
assert (Hwhi : w <= 16) by (unfold w; lia).
assert (Hwkb : w + 1 <= kb) by (unfold w; rewrite Hpll in Hwk; lia).
assert (Hinpl : In (pl, kb) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl kb HAR2 Hinpl) as (_ & Hpl4096 & Hplce & Hplapp & _).
pose proof (req_size_pos kb ltac:(lia)) as [Hrq1 Hrq2].
assert (Hq1 : 1 <= q) by (unfold q; lia).
assert (Hq2 : q <= alloc_ceiling) by (unfold q; lia).
assert (Hqlo : 0 <= pl + w + 1) by (clear - Hpl4096 Hwlo; lia).
assert (Hqhi : pl + w + 1 <= alloc_ceiling) by (clear - Hplce Hrq2 Hwkb Hkr; lia).
assert (Hx0 : 4096 <= x) by (unfold x, V_id; lia).
assert (HxS : SF + 355 = x) by (unfold x, V_id; lia).
assert (Hx1 : x + 17 <= SF + 1024) by (unfold x, V_id; lia).
assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx0 Hx1 HSF1 C1; lia).
assert (Hxw64 : 0 <= x + w < 2 ^ 64) by (clear - Hx0 Hx1 HSF1 C1 Hwlo Hwhi; lia).
assert (Hpl64 : 0 <= pl < 2 ^ 64) by (clear - Hpl4096 Hqhi Hwlo C1; lia).
assert (Hkb64 : 0 <= kb < 2 ^ 64) by (clear - Hkr; lia).
assert (Hw64 : 0 <= w < 2 ^ 64) by (clear - Hwlo Hwhi; lia).
assert (Hq64 : 0 <= q < 2 ^ 64) by (clear - Hq1 Hq2 C1; lia).
(* ---- the bytes of id.model_name and of the payload copy ---- *)
assert (HXm2 : forall j, (j < 17)%nat ->
  aview SEGS (w_H W2) mem2 (x + Z.of_nat j) =
  Some (RcIdentModel.bz (nth j (RcIdentModel.model_name (m_id g (S i))) (RcIdentModel.zb 0)))).
{ intros j Hj.
  replace (x + Z.of_nat j) with (SF + V_id + Z.of_nat (3 + j)) by (rewrite Nat2Z.inj_add; unfold x; cbn [Z.of_nat]; lia).
  rewrite (d4_aview_bytes W2 mem2 (SF + V_id) (m_id g (S i)) (3 + j) Hidb ltac:(rewrite Hidlen; lia)).
  f_equal. unfold RcIdentModel.bz, RcIdentModel.zb. f_equal.
  symmetry. apply D4M.d4_mn_nth; [exact Hidlen | exact Hj]. }
assert (HNZ2 : forall j, 0 <= j < w -> exists b, aview SEGS (w_H W2) mem2 (x + j) = Some b /\ b <> 0).
{ intros j Hj.
  exists (RcIdentModel.bz (nth (Z.to_nat j) (RcIdentModel.model_name (m_id g (S i))) (RcIdentModel.zb 0))).
  split.
  - replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia. apply HXm2. unfold w in Hj. lia.
  - apply D4M.d4_fz_before. unfold m_id. rewrite Hfz. unfold w in Hj. lia. }
assert (HZ2 : aview SEGS (w_H W2) mem2 (x + w) = Some 0).
{ replace (x + w) with (x + Z.of_nat (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)))
    by (unfold w; lia).
  rewrite HXm2 by lia. f_equal.
  unfold m_id. rewrite <- Hfz. apply D4M.d4_fz_nth.
  rewrite (D4M.d4_mn_len _ ltac:(unfold m_id in Hidlen; exact Hidlen)), Hfz. lia. }
assert (HEQ2 : forall j, 0 <= j < w -> aview SEGS (w_H W2) mem2 (x + j) = aview SEGS (w_H W2) mem2 (pl + 1 + j)).
{ intros j Hj.
  replace (x + j) with (x + Z.of_nat (Z.to_nat j)) by lia.
  rewrite HXm2 by (unfold w in Hj; lia).
  replace (pl + 1 + j) with (pl + Z.of_nat (1 + Z.to_nat j)) by (rewrite Nat2Z.inj_add; cbn [Z.of_nat]; lia).
  rewrite (d4_aview_bytes W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) (1 + Z.to_nat j) Hpl
    ltac:(rewrite Hpll; unfold w in Hj; lia)).
  f_equal. unfold RcIdentModel.bz. f_equal. change (Z_to_bv 8 0) with (RcIdentModel.zb 0).
  rewrite (D4M.d4_mn_nth (m_id g (S i)) (Z.to_nat j) Hidlen ltac:(unfold w in Hj; lia)).
  rewrite <- (D4M.d4_nth_skip 3 (m_id g (S i)) (Z.to_nat j) (RcIdentModel.zb 0)).
  rewrite <- (D4M.d4_nth_skip 1 (SlotModel.rec_pl (e_pl g) i) (Z.to_nat j) (RcIdentModel.zb 0)).
  rewrite <- (SlotModel.nth_first (skipn 3 (m_id g (S i))) (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))
    (Z.to_nat j) (RcIdentModel.zb 0) ltac:(unfold w in Hj; lia)).
  rewrite <- (SlotModel.nth_first (skipn 1 (SlotModel.rec_pl (e_pl g) i))
    (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)) (Z.to_nat j) (RcIdentModel.zb 0)
    ltac:(unfold w in Hj; lia)).
  unfold m_id. rewrite Hpre. reflexivity. }
assert (HQ2 : w <= 15 -> w + 1 < kb -> aview SEGS (w_H W2) mem2 q = Some 0).
{ intros Hle Hlt.
  replace q with (pl + Z.of_nat (S (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))))
    by (unfold q, w; rewrite Nat2Z.inj_succ; lia).
  rewrite (d4_aview_bytes W2 mem2 pl (SlotModel.rec_pl (e_pl g) i)
    (S (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))) Hpl ltac:(rewrite Hpll; unfold w in *; lia)).
  f_equal. change (bv_unsigned (nth (S (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i)))
    (SlotModel.rec_pl (e_pl g) i) (Z_to_bv 8 0)))
    with (RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i)
      (S (RcIdentModel.name_len (SlotModel.rec_pl (e_pl g) i))))).
  apply D4M.d4_name0. rewrite Hpll. unfold w in *. lia. }
(* ---- the shadow of id.model_name ---- *)
assert (HRA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF x 17).
{ apply (range_addressable_sub (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + V_id) 32);
  [| unfold x, V_id; lia | unfold x, V_id; lia].
  apply (zero_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF (SF + V_id) 32);
  [unfold V_id; clear - HSF64; lia | lia |].
  intros ii Hii. apply Hidz. unfold N_id. lia. }
(* ---- the read-only image at the entry state ---- *)
pose proof (HRO _ Hro0) as Hro1.
(* ---- the environment and the state at 0x812b8 ---- *)
remember (Eimg (Ereg regs2 (d4_extra x q w))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 x)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 q)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 w)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 (d4_extra x q w)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (E19 : ew E 19 = Z_to_bv 64 1)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold m_id; rewrite Hmn1; reflexivity).
assert (E27 : ew E 27 = Z_to_bv 64 pl) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E22 : ew E 22 = Z_to_bv 64 kb) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (ESP : ew E 2 = w64 mf) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (EGP : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Rgp).
assert (ETP : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Rtp).
assert (ES1 : ew E 9 = w64 mf) by (rewrite (EE 9%nat 9%bv eq_refl); exact Rs1).
assert (ES0 : ew E 8 = w64 sp0) by (rewrite (EE 8%nat 8%bv eq_refl); exact Rs0).
assert (HS : st_ok_pi SEGS VAL E d4_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xb44)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d4_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold d4_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 33 0) x);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - Hx0 Hx1 HSF1 C1; lia | lia | exact F136].
    + apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; lia | lia | exact V168].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok, d4_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|split; [|exact I]]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19, E32, E34. rewrite !unsigned_lit_small by (unfold SB; clear - Hq1 Hq2 Hplce C1; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; unfold SB; clear - Hq1 Hq2 Hplce C1; lia.
    + apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (d4_U_off E 35 1 w E35 ltac:(clear - Hwlo Hwhi; lia) ltac:(clear - Hwlo Hwhi; lia)).
      rewrite (d4_U_off E 27 0 pl E27 ltac:(clear - Hpl4096 Hqhi Hwlo C1; lia)
        ltac:(clear - Hpl4096 Hqhi Hwlo C1; lia)).
      rewrite (d4_U_off E 34 0 q E34 ltac:(clear - Hq1 Hq2 C1; lia) ltac:(clear - Hq1 Hq2 C1; lia)).
      rewrite !Z.add_0_r. unfold q. replace (w + 1 + pl) with (pl + w + 1) by ring.
      apply zcanon_id. unfold M64. clear - Hqlo Hqhi C1. lia. }
assert (SHOK : sh_ok SEGS D4Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + 0xb44)) with (Z_to_bv 64 (BASE + 0xb44)).
(* ---- run 1: 0x812b8 .. the memchr call 0x812c4 ---- *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ unfold d4_ss, d4_mf. cbn [ss_mem]. apply awr_ok_cons_ro;
  [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP) as KEEP1.
clear KEEP HF HFr HG.
(* ---- the memchr call 0x812c4: a0 = &id.model_name, a1 = 0, a2 = 17 ---- *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp1. prreg HS (3%bv : bv 5) Rgp1.
prreg HS (4%bv : bv 5) Rtp1.
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite Rsp1, (EE 2%nat 2%bv eq_refl), Rsp. apply unsigned_lit_small.
  clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (TRc : forall a, 0 <= a <= alloc_ceiling ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply KEEP1; clear - Ha Hmf0 C1; lia).
assert (HXc : forall j, (j < 17)%nat -> aview SEGS (w_H W2) (ms_mem ms) (x + Z.of_nat j) =
  Some (RcIdentModel.bz (nth j (RcIdentModel.model_name (m_id g (S i))) (RcIdentModel.zb 0)))).
{ intros j Hj. rewrite TRc by (clear - Hx0 Hx1 HSF1 Hj C1; lia). apply HXm2. exact Hj. }
assert (HSRC : src_ok SEGS W2 (ms_regs ms) (ms_mem ms) x 17).
{ intros a Ha. split.
  - replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite HXc by lia. discriminate.
  - rewrite Usp. clear - Ha Hx0 Hx1 HSF1 Hmf0 C1 Hes. lia. }
assert (HAMR : amem_range x 17).
{ apply amem_range_high; [lia | | clear - Hx1 HSF1; lia].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp. clear - HSFapp HxS Hx1. lia. }
assert (HRAc : range_addressable (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF x 17).
{ apply (range_addressable_kept_win (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem ms))
    (mf - 8192) mf x 17);
  [ intros s Hs Hn; apply KEEP1; [exact Hs | exact Hn]
  | unfold kHighShadowEnd; clear - Hmf0 C1; lia | clear - Hx0; lia | clear - Hx1 HSF1 C1; lia | exact HRA2]. }
assert (HHULLc : shadow_hull_vis (aview SEGS (w_H W2) (ms_mem ms)) x 17).
{ apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms) _ 4 pos x 17 (proj1 HJ) Hin4);
  [rewrite EFa; clear - HxS; lia | rewrite EFa, HFB; clear - Hx1; lia | lia]. }
assert (HROc : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms))).
{ apply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi B).
  eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B); [exact HJ | exact Hro1]. }
pmkst HS.
eapply SRr_bind.
{ eapply (d4_memchr_at W2 (ms_regs ms) (ms_mem ms) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g)
    (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 3) x 0 17 (mf - sp0) (Z_to_bv 64 (BASE + 0xb54)) HJ).
  - rewrite Ra0, E33. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - clear - Hx0. lia.
  - clear - Hx1 HSF1 C1. lia.
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK' Hes Has. lia.
  - rewrite Rgp1, (EE 3%nat 3%bv eq_refl). exact Rgp.
  - rewrite Rtp1, (EE 4%nat 4%bv eq_refl). exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HSRC.
  - exact HAMR.
  - exact HRAc.
  - intros _. exact HHULLc.
  - exact HROc. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (kk & Hfb & Ha0kk) & Hfr3 & Hpres3).
assert (Ekk : kk = w).
{ apply (d4_first_byte_eq W2 (ms_mem ms) x 17 0 kk w Hfb).
  - intros j Hj. destruct (HNZ2 j Hj) as (b & Hb & Hnb). exists b. split; [|exact Hnb].
    rewrite TRc by (clear - Hj Hwhi Hx0 Hx1 HSF1 C1; lia). exact Hb.
  - rewrite TRc by (clear - Hwhi Hx0 Hx1 HSF1 C1; lia). exact HZ2.
  - clear - Hwlo Hwhi. lia. }
subst kk.
replace (w <? 17) with true in Ha0kk by (symmetry; apply Z.ltb_lt; clear - Hwhi; lia).
(* ---- the state after the memchr call, at 0x812c8 ---- *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply region_kept_aview; [exact U9 | intros a Ha | exact Hpres3].
  apply Hfr3; [clear - Ha Hmf0 H47 Hmfb Hshi C1; lia | clear - Ha; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
set (E' := havoc E 512 (map (getr regs3) CLOB)) in *.
clear HJ SHOK. rename HJ3 into HJ.
assert (SHOK : sh_ok SEGS D4Bx [] E' (mrestrict (w_H W2) mem3)) by apply Forall_nil.
(* the carried-over bytes outside the window below mf (the two calls kept [mf - 8192, mf)) *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hfr3 a Ha ltac:(clear - Hn Hes; lia)). apply KEEP1; [exact Ha | exact Hn]. }
(* the three atoms a0 / &id.model_name / w after the call havoc *)
assert (E'516 : ew E' 516 = Z_to_bv 64 (x + w)).
{ change 516%nat with (512 + 4)%nat. unfold E'.
  apply (d4h_ewclob E 512%nat 4%nat regs3 10%bv (x + w));
  [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity | rewrite Ha0kk; reflexivity]. }
assert (E'33 : ew E' 33 = Z_to_bv 64 x) by (unfold E'; rewrite ew_havoc_old by lia; exact E33).
assert (E'35 : ew E' 35 = Z_to_bv 64 w) by (unfold E'; rewrite ew_havoc_old by lia; exact E35).
assert (E'22 : ew E' 22 = Z_to_bv 64 kb) by (unfold E'; rewrite ew_havoc_old by lia; exact E22).
assert (E'27 : ew E' 27 = Z_to_bv 64 pl) by (unfold E'; rewrite ew_havoc_old by lia; exact E27).
(* add the alias (x + w) - x = w, so the sub at 0x812e8 becomes atom 35 *)
apply (d4_add_alias _ _ _ (SAlu ALU_SUB (SOff 516 0) (SOff 33 0)) (SOff 35 0)) in HS.
2:{ apply U_inj. rewrite U_SAlu.
    rewrite (d4_U_off E' 516 0 (x + w) E'516 Hxw64 ltac:(clear - Hxw64; lia)).
    rewrite (d4_U_off E' 33 0 x E'33 Hx64 ltac:(clear - Hx64; lia)).
    rewrite (d4_U_off E' 35 0 w E'35 Hw64 ltac:(clear - Hw64; lia)).
    cbn [zalu_raw]. unfold zcanon, M64. rewrite !Z.add_0_r.
    rewrite (Z.mod_small (x + w - x)) by (clear - Hw64; lia). lia. }
(* the unsigned values of the atoms the branch conditions compare *)
assert (U516 : U E' (SOff 516 0) = x + w)
  by (rewrite (d4_U_off E' 516 0 (x + w) E'516 Hxw64 ltac:(clear - Hxw64; lia)); apply Z.add_0_r).
assert (U33' : U E' (SOff 33 0) = x)
  by (rewrite (d4_U_off E' 33 0 x E'33 Hx64 ltac:(clear - Hx64; lia)); apply Z.add_0_r).
assert (U35' : U E' (SOff 35 0) = w)
  by (rewrite (d4_U_off E' 35 0 w E'35 Hw64 ltac:(clear - Hw64; lia)); apply Z.add_0_r).
assert (U22' : U E' (SOff 22 0) = kb)
  by (rewrite (d4_U_off E' 22 0 kb E'22 Hkb64 ltac:(clear - Hkb64; lia)); apply Z.add_0_r).
assert (U27' : U E' (SOff 27 0) = pl)
  by (rewrite (d4_U_off E' 27 0 pl E'27 Hpl64 ltac:(clear - Hpl64; lia)); apply Z.add_0_r).
assert (U351 : U E' (SOff 35 1) = w + 1)
  by (apply (d4_U_off E' 35 1 w E'35 Hw64); clear - Hwlo Hwhi; lia).
assert (U271 : U E' (SOff 27 1) = pl + 1)
  by (apply (d4_U_off E' 27 1 pl E'27 Hpl64); clear - Hpl64 Hqhi Hwlo C1; lia).
assert (U0 : U E' (SLit 0) = 0) by (apply d4_U_lit; clear; lia).
assert (U2 : U E' (SLit 2) = 2) by (apply d4_U_lit; clear; lia).
(* ---- run 2: 0x812c8 .. the bcmp call 0x81310, refuting the four aborts ---- *)
(* B1 0x812d0 (bnez a0): a0 = x + w <> 0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP2) as KEEP2'.
clear KEEP2 HF HFr HG. rename KEEP2' into KEEP2.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E' (SOff 516 0) (SLit 0) (x + w) 0 U516 U0) as (KN & _);
  assert (Hbad : x + w = 0) by (apply Z.eqb_eq; apply negb_false_iff; rewrite <- KN; exact Hc);
  clear - Hbad Hx0 Hwlo; lia].
(* B2 0x812dc (bne a0,a1): a0 = x + w <> a1 = x (w >= 1) *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP2) as KEEP2'.
clear KEEP2 HF HFr HG. rename KEEP2' into KEEP2.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E' (SOff 516 0) (SOff 33 0) (x + w) x U516 U33') as (KN & _);
  assert (Hbad : x + w = x) by (apply Z.eqb_eq; apply negb_false_iff; rewrite <- KN; exact Hc);
  clear - Hbad Hwlo; lia].
(* B3 0x812f0 (bgeu s6,s3): kb >= w + 1 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP2) as KEEP2'.
clear KEEP2 HF HFr HG. rename KEEP2' into KEEP2.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E' (SOff 22 0) (SOff 35 1) kb (w + 1) U22' U351) as (_ & _ & _ & KG);
  assert (Hbad : kb < w + 1) by (apply Z.ltb_lt; apply negb_false_iff; rewrite <- KG; exact Hc);
  clear - Hbad Hwkb; lia].
(* B4 0x81300 (bgeu a1,a0): pl + 1 >= 2 (the UBSan pointer-overflow check) *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP2) as KEEP2'.
clear KEEP2 HF HFr HG. rename KEEP2' into KEEP2.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E' (SOff 27 1) (SLit 2) (pl + 1) 2 U271 U2) as (_ & _ & _ & KG);
  assert (Hbad : pl + 1 < 2) by (apply Z.ltb_lt; apply negb_false_iff; rewrite <- KG; exact Hc);
  clear - Hbad Hpl4096; lia].
(* run to the bcmp call 0x81310: a0 = &id.model_name, a1 = pl + 1, a2 = w *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
pose proof (d4_keep_run _ _ W2 mem2 _ _ (mf - 8192) mf HFr
  ltac:(intros bb wlo whi aa Hin Hr; cbn in Hin;
        repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; clear - Hr; lia |]); destruct Hin)
  KEEP2) as KEEP2'.
clear KEEP2 HF HFr HG. rename KEEP2' into KEEP2.
(* ---- the bcmp call 0x81310: a0 = x = &id.model_name, a1 = pl + 1, a2 = w ---- *)
(* the memchr call's machine state is stale: clear it, and name the current one ms *)
repeat match goal with H : context [ms] |- _ => clear H end. clear ms.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms end.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
assert (E'2 : ew E' 2 = w64 mf) by (unfold E'; rewrite ew_havoc_old by lia; exact ESP).
assert (E'3 : ew E' 3 = w64 (as_gp B)) by (unfold E'; rewrite ew_havoc_old by lia; exact EGP).
assert (E'4 : ew E' 4 = w64 (as_tp B)) by (unfold E'; rewrite ew_havoc_old by lia; exact ETP).
assert (E'9 : ew E' 9 = w64 mf) by (unfold E'; rewrite ew_havoc_old by lia; exact ES1).
assert (E'8 : ew E' 8 = w64 sp0) by (unfold E'; rewrite ew_havoc_old by lia; exact ES0).
rewrite E'33 in Qa0. rewrite E'35 in Qa2.
rewrite E'27, unsigned_lit_small in Qa1 by (clear - Hpl64; lia).
rewrite E'2 in Qsp. rewrite E'3 in Qgp. rewrite E'4 in Qtp.
assert (Usp2 : spZ (ms_regs ms) = mf)
  by (unfold spZ; rewrite Qsp; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (U9' : bv_unsigned (ew E' 9) = mf)
  by (rewrite E'9; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (TR2 : forall a, 0 <= a <= alloc_ceiling ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply KEEP2; clear - Ha Hmf0 C1; lia).
assert (PX : forall b, x <= b < x + w -> aview SEGS (w_H W2) (ms_mem ms) b <> None).
{ intros b Hb. rewrite TR2 by (clear - Hb Hx0 Hx1 Hwhi HSF1 C1; lia).
  replace b with (x + Z.of_nat (Z.to_nat (b - x))) by (clear - Hb; lia).
  rewrite HXm2 by (clear - Hb Hwhi; lia). discriminate. }
assert (PY : forall b, pl + 1 <= b < pl + 1 + w -> aview SEGS (w_H W2) (ms_mem ms) b <> None).
{ intros b Hb. rewrite TR2 by (clear - Hb Hpl4096 Hqhi C1; lia).
  replace b with (pl + Z.of_nat (Z.to_nat (b - pl))) by (clear - Hb; lia).
  rewrite (d4_aview_bytes W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) (Z.to_nat (b - pl)) Hpl)
    by (rewrite Hpll; clear - Hb Hwkb; lia). discriminate. }
assert (NSX : forall b, x <= b < x + w -> ~ (spZ (ms_regs ms) - 2 * ESTACK <= b < spZ (ms_regs ms)))
  by (intros b Hb; rewrite Usp2, Hes; clear - Hb Hx1 Hwhi HSF1 Hmf0; lia).
assert (NSY : forall b, pl + 1 <= b < pl + 1 + w -> ~ (spZ (ms_regs ms) - 2 * ESTACK <= b < spZ (ms_regs ms)))
  by (intros b Hb; rewrite Usp2, Hes; clear - Hb Hqhi Hmf0; lia).
destruct (d4h_frame_read B LAWS ly2 S2 W2 (ms_mem ms) _ (ms_regs ms) 4 pos x w (proj1 HJ) Hin4)
  as (SRX & AMX & HHX).
{ clear; lia. } { rewrite EFa. clear - HxS. lia. } { rewrite EFa, HFB. clear - Hx1 Hwhi. lia. }
{ clear - Hwlo. lia. } { exact PX. } { exact NSX. }
destruct (d4h_block_read B LAWS ly2 S2 W2 (ms_mem ms) _ (ms_regs ms) pl kb (pl + 1) w (proj1 HJ) Hinpl)
  as (SRY & AMY & RAY & HHY).
{ clear; lia. } { clear - Hwkb. lia. } { clear - Hwlo. lia. } { exact PY. } { exact NSY. }
assert (RAX : range_addressable (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF x w).
{ apply (range_addressable_sub (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF x 17);
  [| clear; lia | clear - Hwhi; lia].
  apply (range_addressable_kept_win (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem ms))
    (mf - 8192) mf x 17);
  [ intros s Hs Hn; apply KEEP2; [exact Hs | exact Hn]
  | unfold kHighShadowEnd; clear - Hmf0 C1; lia | clear - Hx0; lia | clear - Hx1 HSF1 C1; lia | exact HRA2]. }
pmkst HS.
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IB___interceptor_trampoline_bcmp) ABCMP W2 (ms_regs ms)
    (ms_mem ms) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _
    (4 * Z.of_nat i + 3) x (pl + 1) w (mf - sp0) (Z_to_bv 64 (BASE + 2976)) HJ).
  - exact Qa0.
  - exact Qa1.
  - exact Qa2.
  - clear - Hwlo Hwhi. lia.
  - clear - Hx0. lia.
  - clear - Hx1 Hwhi HSF1 C1. lia.
  - clear - Hpl4096. lia.
  - clear - Hqhi C1. lia.
  - rewrite Usp2. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - rewrite Hes. clear - Hmfb HSTK' Has. lia.
  - exact Qgp.
  - exact Qtp.
  - exact Qra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact SRX.
  - exact SRY.
  - intros b Hb. rewrite Hes. clear - Hb Hx1 Hwhi HSF1 Hmf0. lia.
  - intros b Hb. rewrite Hes. clear - Hb Hqhi Hmf0. lia.
  - exact AMX.
  - exact AMY.
  - exact RAX.
  - exact HHX.
  - exact RAY.
  - exact HHY. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hcmp & Hfr4 & Hpres4).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros j Hj. rewrite !TR2.
  - apply HEQ2. exact Hj.
  - clear - Hj Hpl4096 Hqhi C1. lia.
  - clear - Hj Hx0 Hx1 Hwhi HSF1 C1. lia. }
subst v. clear Hcmp.
(* ---- the state after the bcmp call, at 0x81314 ---- *)
jafter_call_keep_hi HS 528%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0%nat] HS4.
match type of HS4 with ?Q -> _ => assert (HQ : Q); [|specialize (HS4 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply region_kept_aview; [exact U9' | intros a Ha | exact Hpres4].
  apply Hfr4; [clear - Ha Hmf0 H47 Hmfb Hshi C1; lia | clear - Ha; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
pose proof (img_env_havoc_hi E' 528%nat (map (getr regs4) CLOB) HEI3 ltac:(cbv; lia)) as HEIb.
set (E'' := havoc E' 528 (map (getr regs4) CLOB)) in *.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8192 <= a < mf) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hfr4 a Ha ltac:(clear - Hn Hes; lia)). apply KEEP2; [exact Ha | exact Hn]. }
clear KEEP2 Hfr4 HJ SHOK. rename HJ4 into HJ.
assert (SHOK : sh_ok SEGS D4Bx [] E'' (mrestrict (w_H W2) mem4)) by apply Forall_nil.
(* the atoms after the second havoc *)
assert (E''532 : ew E'' 532 = Z_to_bv 64 0).
{ change 532%nat with (528 + 4)%nat. unfold E''.
  apply (d4h_ewclob E' 528%nat 4%nat regs4 10%bv 0);
  [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity | exact Hv0]. }
assert (E''35 : ew E'' 35 = Z_to_bv 64 w) by (unfold E''; rewrite ew_havoc_old by lia; exact E'35).
assert (E''22 : ew E'' 22 = Z_to_bv 64 kb) by (unfold E''; rewrite ew_havoc_old by lia; exact E'22).
assert (E''27 : ew E'' 27 = Z_to_bv 64 pl) by (unfold E''; rewrite ew_havoc_old by lia; exact E'27).
assert (E''32 : ew E'' 32 = Z_to_bv 64 SB)
  by (unfold E'', E'; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E32).
assert (E''34 : ew E'' 34 = Z_to_bv 64 q)
  by (unfold E'', E'; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E34).
assert (E''9 : ew E'' 9 = w64 mf)
  by (unfold E'', E'; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact ES1).
assert (U532 : U E'' (SOff 532 0) = 0)
  by (rewrite (d4_U_off E'' 532 0 0 E''532 ltac:(clear; lia) ltac:(clear; lia)); reflexivity).
assert (U35'' : U E'' (SOff 35 0) = w)
  by (rewrite (d4_U_off E'' 35 0 w E''35 Hw64 ltac:(clear - Hw64; lia)); apply Z.add_0_r).
assert (U351'' : U E'' (SOff 35 1) = w + 1)
  by (apply (d4_U_off E'' 35 1 w E''35 Hw64); clear - Hwlo Hwhi; lia).
assert (U22'' : U E'' (SOff 22 0) = kb)
  by (rewrite (d4_U_off E'' 22 0 kb E''22 Hkb64 ltac:(clear - Hkb64; lia)); apply Z.add_0_r).
assert (U27'' : U E'' (SOff 27 0) = pl)
  by (rewrite (d4_U_off E'' 27 0 pl E''27 Hpl64 ltac:(clear - Hpl64; lia)); apply Z.add_0_r).
assert (U34'' : U E'' (SOff 34 0) = q)
  by (rewrite (d4_U_off E'' 34 0 q E''34 Hq64 ltac:(clear - Hq64; lia)); apply Z.add_0_r).
assert (U32'' : U E'' (SOff 32 0) = SB)
  by (rewrite (d4_U_off E'' 32 0 SB E''32 ltac:(unfold SB; clear; lia) ltac:(unfold SB; clear; lia));
      apply Z.add_0_r).
assert (U0'' : U E'' (SLit 0) = 0) by (apply d4_U_lit; clear; lia).
assert (U15'' : U E'' (SLit 15) = 15) by (apply d4_U_lit; clear; lia).
(* ---- run 3: 0x81314 .. 0x81598 ---- *)
(* B5 0x81318 (beqz a0): the bcmp answer is 0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E'' (SOff 532 0) (SLit 0) 0 0 U532 U0'') as (_ & KE & _);
  assert (Hbad : (0 =? 0) = false) by (rewrite <- KE; exact Hc); discriminate Hbad].
(* B6 0x81320 (bltu 15, s2): w > 15 joins at once *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
psrr_branch_tok RUNTO BR HS SHOK Bspan.
{ (* join 1 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
  { cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
  d4_keep KEEP HF HG.
  prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
  prreg HS (9%bv : bv 5) Z9. prreg HS (22%bv : bv 5) Z22. prreg HS (27%bv : bv 5) Z27.
  unfold E'', E' in Z2, Z3, Z4, Z8, Z9, Z22, Z27.
  d4_ewnorm Z2. d4_ewnorm Z3. d4_ewnorm Z4. d4_ewnorm Z8. d4_ewnorm Z9. d4_ewnorm Z22. d4_ewnorm Z27.
  rewrite ESP in Z2. rewrite EGP in Z3. rewrite ETP in Z4. rewrite ES0 in Z8. rewrite ES1 in Z9.
  rewrite E22 in Z22. rewrite E27 in Z27.
  apply SRr_ret. pmkst HS.
  exact (d4_post g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HJ eq_refl Hfrs Hk MLE MOK HCfull HPBfull Hhw
    Haddr LAWS KEEP Z2 Z9 Z8 Z3 Z4 Z22 Z27). }
assert (Hw15 : w <= 15).
{ destruct (d4h_kill E'' (SLit 15) (SOff 35 0) 15 w U15'' U35'') as (_ & _ & KL & _).
  assert (Hb : (15 <? w) = false) by (rewrite <- KL; exact Hc). apply Z.ltb_ge in Hb. exact Hb. }
clear Hc.
(* B7 0x81324 (bgeu s3, s6): w + 1 >= k joins *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
psrr_branch_tok RUNTO BR HS SHOK Bspan.
{ (* join 2 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
  { cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
  d4_keep KEEP HF HG.
  prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
  prreg HS (9%bv : bv 5) Z9. prreg HS (22%bv : bv 5) Z22. prreg HS (27%bv : bv 5) Z27.
  unfold E'', E' in Z2, Z3, Z4, Z8, Z9, Z22, Z27.
  d4_ewnorm Z2. d4_ewnorm Z3. d4_ewnorm Z4. d4_ewnorm Z8. d4_ewnorm Z9. d4_ewnorm Z22. d4_ewnorm Z27.
  rewrite ESP in Z2. rewrite EGP in Z3. rewrite ETP in Z4. rewrite ES0 in Z8. rewrite ES1 in Z9.
  rewrite E22 in Z22. rewrite E27 in Z27.
  apply SRr_ret. pmkst HS.
  exact (d4_post g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HJ eq_refl Hfrs Hk MLE MOK HCfull HPBfull Hhw
    Haddr LAWS KEEP Z2 Z9 Z8 Z3 Z4 Z22 Z27). }
assert (Hwk1 : w + 1 < kb).
{ destruct (d4h_kill E'' (SOff 35 1) (SOff 22 0) (w + 1) kb U351'' U22'') as (_ & _ & _ & KG).
  assert (Hb : negb (w + 1 <? kb) = false) by (rewrite <- KG; exact Hc).
  apply negb_false_iff, Z.ltb_lt in Hb. exact Hb. }
clear Hc.
(* ---- path 3, at 0x81328: the stopped-early byte pl[w + 1] = q, which is 0; its shadow says addressable ---- *)
lazymatch type of HS with
| st_ok _ _ _ (restrict _ ?m) => rename m into msq
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msq end.
prreg HS (2%bv : bv 5) Qspq. unfold E'', E' in Qspq. d4_ewnorm Qspq. rewrite ESP in Qspq.
assert (Uspq : spZ (ms_regs msq) = mf)
  by (unfold spZ; rewrite Qspq; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (TRq : aview SEGS (w_H W2) (ms_mem msq) q = Some 0).
{ rewrite KEEP by (clear - Hq1 Hq2 Hmf0 C1; lia). apply HQ2; [exact Hw15 | exact Hwk1]. }
destruct (d4h_block_read B LAWS ly2 S2 W2 (ms_mem msq) _ (ms_regs msq) pl kb q 1 (proj1 HJ) Hinpl)
  as (_ & _ & RAQ & _).
{ clear - Hwlo. lia. } { clear - Hwk1. lia. } { clear; lia. }
{ intros b Hb. replace b with q by (clear - Hb; lia). rewrite TRq. discriminate. }
{ intros b Hb. rewrite Uspq, Hes. clear - Hb Hq2 Hmf0. lia. }
apply (st_ok_pi_add_region E'' _ _ d4_q) in HS.
2:{ vm_compute. reflexivity. }
2:{ unfold d4_q, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E''34, unsigned_lit_small by (clear - Hq64; lia).
    split; [clear - Hq1 C1; lia|]. split; [clear - Hq2 C1; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E'' _ q 0 1 (SLit 0) 0);
    [reflexivity | clear - Hq1 Hq2 C1; lia | lia | ].
    rewrite Z.add_0_r. cbn [ms_mem restrict]. apply d4_val_mem1. exact TRq. }
2:{ cbn [all_disjoint ss_mem]. split; [|exact I]. left.
    unfold d4_q. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E''34, E''9, !unsigned_lit_small by (clear - Hq64 Hmf0 H47 Hmfb Hshi C1; lia).
    clear - Hq2 Hmf0 C1. lia. }
match type of HS with context [mkSS ?a ?b ?c ?d ?e] =>
  let s := eval vm_compute in (mkSS a b c d e) in change (mkSS a b c d e) with s in HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS D4Bx d4_SH E'' (mrestrict (w_H W2) (ms_mem msq))).
{ constructor; [|constructor]. split.
  - unfold D4Bx. cbn [she_m she_lo she_hi d4_SH]. rewrite U32'', U34''.
    replace (q + 0) with q by ring. replace (1 - 0) with 1 by ring. unfold SB. exact RAQ.
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. unfold D4Bx. rewrite U32''. rewrite U34'' in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hplapp. unfold SB.
    clear - Ha Hplapp Eq_q Hwk1 Hwlo Hrq1 Hrq2. lia. }
(* B8 0x81328 (bnez s11): pl <> 0 (UBSan) *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E'' (SOff 27 0) (SLit 0) pl 0 U27'' U0'') as (KN & _);
  assert (Hbad : pl = 0) by (apply Z.eqb_eq; apply negb_false_iff; rewrite <- KN; exact Hc);
  clear - Hbad Hpl4096; lia].
(* B9 0x8133c (bgeu q, s11): pl + w + 1 does not wrap (UBSan) *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
psrr_branch_tok RUNTO BR HS SHOK Bspan; [clear Hc |
  exfalso; destruct (d4h_kill E'' (SOff 34 0) (SOff 27 0) q pl U34'' U27'') as (_ & _ & _ & KG);
  assert (Hbad : q < pl) by (apply Z.ltb_lt; apply negb_false_iff; rewrite <- KG; exact Hc);
  clear - Hbad Hq1; unfold q in *; lia].
(* join 3: the ASan check of q and the byte test at 0x8158c pass on the byte 0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0xe24.
{ cbn [ss_mem]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
d4_keep KEEP HF HG.
prreg HS (2%bv : bv 5) Z2. prreg HS (3%bv : bv 5) Z3. prreg HS (4%bv : bv 5) Z4. prreg HS (8%bv : bv 5) Z8.
prreg HS (9%bv : bv 5) Z9. prreg HS (22%bv : bv 5) Z22. prreg HS (27%bv : bv 5) Z27.
unfold E'', E' in Z2, Z3, Z4, Z8, Z9, Z22, Z27.
d4_ewnorm Z2. d4_ewnorm Z3. d4_ewnorm Z4. d4_ewnorm Z8. d4_ewnorm Z9. d4_ewnorm Z22. d4_ewnorm Z27.
rewrite ESP in Z2. rewrite EGP in Z3. rewrite ETP in Z4. rewrite ES0 in Z8. rewrite ES1 in Z9.
rewrite E22 in Z22. rewrite E27 in Z27.
apply SRr_ret. pmkst HS.
exact (d4_post g pos mf i pl ly2 S2 W2 regs2 mem2 md2 _ _ _ _ HJ eq_refl Hfrs Hk MLE MOK HCfull HPBfull Hhw
  Haddr LAWS KEEP Z2 Z9 Z8 Z3 Z4 Z22 Z27).
Qed.
Print Assumptions seg_D4.

Check (seg_D4 : seg_D4_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
