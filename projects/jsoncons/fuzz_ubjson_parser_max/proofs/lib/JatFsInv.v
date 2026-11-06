(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA ArtMem ArtBridge JatInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFsInv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2or"; "3repeat"; "4Z"; "0F"; "0FF"; "0FF'"; "0LK"]; ["0LK'"; "5word_to_le_bytes"; "0M"; "0M'"; "6cell"; "7byte_at"; "7ff_bytes"; "7fframe"; "8art_fsg"; "8art_fsinv"; "8art_fsinv_handoff"; "8fs_flag"; "8fs_frame"; "8fs_nfr"; "9art_run"; ":loaded_segments"]; [";In"; "<add"; "<le"; "<lt"; "<of_nat"; "<pow"; "<sub"; "0a"; "0c"; "0fl"; "0fs"; "0g"; "0g'"; "0i"; "0i'"; "0j"]; ["0k"; "0n"; "0rn"; "0rs"; "0rs'"; "=Z_to_bv"; "=bv"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Record art_fsg : Type := FSGH {
fg_hint : Z -> Z;
fg_gc : bool
}.
Definition art_fsg0 : art_fsg := FSGH (fun _ => 0) false.
Definition fs_nfr (c : Z) : Z := 2 ^ (14 - c).
Definition fs_flag (fs c i : Z) : Z := fs + 4096 + 32768 - 2 * fs_nfr c + i.
Definition fs_frame (fs c i : Z) : Z := fs + 4096 + 32768 + c * 2 ^ 20 + i * ff_bytes c.
Definition fs_slot (fs : Z) (f : fframe) (i : Z) : Prop := 0 <= i < fs_nfr (ff_class f) /\ ff_addr f = fs_frame fs (ff_class f) i.
Lemma fs_flag_below_frames : ltac2:(TCodec.tc2 tcn__JatFsInv "Q0';'7&Q2zr2%3221+:%5231%7231&Q3&Mr3%211%4291%=291&Q1r5+TP0%3221&Kr4%2351:%D241+QPP0%9261%@241%I241p0=1p0D1pRLM1pRBN1pRFO1").
Proof.
intros fs c i Hc Hi. unfold fs_flag, fs_nfr in *.
assert (P : 0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
assert (Q : 2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
change (2 ^ 14) with 16384 in Q. lia.
Qed.
Lemma fs_frame_above_flags : ltac2:(TCodec.tc2 tcn__JatFsInv "E';&Q2zr2%3221&Q1r5+TP0%3221+QPP0%5221&Lr4r3%33821%>251p0<1p0=1pS0B1pS2C1pRFD1").
Proof.
intros fs k j Hk Hj. unfold fs_frame, ff_bytes.
assert (P : 0 <= k * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
assert (Q : 0 <= j * (64 * 2 ^ k)) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]]).
lia.
Qed.
Lemma fs_flag_frame_apart : ltac2:(TCodec.tc2 tcn__JatFsInv "Q:';'7&Q2zr4%3221+:%5231%7231&Q3&Mr5%211%4291%=291'9&Q1&Lr9r6%33219&F%113%7231&Kr8r7%33921%J251+1%>231%M21;%A241p0L1p0M1p0E1p0L1pS0Q51pS2Q61pRLQ71pRBQ81pRFQ91").
Proof.
intros fs c i k j Hc Hi Hk Hj. right.
pose proof (fs_flag_below_frames fs c i Hc Hi). pose proof (fs_frame_above_flags fs k j Hk Hj). lia.
Qed.
Definition art_fs_geo (rn : art_run) : Prop :=
let fs := ar_fs (rn_ar rn) in
fs mod 4096 = 0 /\ 4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x10000 \/ 0x691000 <= fs) /\ app_mem fs FS_BYTES
/\ (fs + FS_BYTES <= rn_t rn \/ rn_t rn + 4096 <= fs)
/\ 0 <= rn_t rn /\ rn_t rn + 4096 <= 2 ^ 47
/\ 0x65cbe8 <= rn_tp rn /\ rn_tp rn + 8 <= 0x691000.
Definition ART_GLOBALS : list (Z * Z) := [(0x23100, 13); (0x23160, 7); (0x23180, 54); (0x23340, 16); (0x23360, 23); (0x233a0, 13); (0x233c0, 60); (0x23420, 77); (0x234a0, 73); (0x23520, 13); (0x23540, 38); (0x235a0, 70); (0x23620, 69); (0x236a0, 37); (0x23700, 43); (0x23760, 34); (0x237c0, 71); (0x23840, 28); (0x23880, 52); (0x12cda0, 104)].
Definition art_c_statics (rn : art_run) (M : word -> option byte) : Prop :=
(rn_tp rn + 16 <= 0x691000 /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= 2 ^ 47)
/\ cellA M 0x134450 8 0x125294 /\ cellA M 0x134518 8 0x11355c /\ cellA M 0x134520 8 0x1251fc
/\ cellA M (rn_tp rn + 8) 8 (rn_dtls rn) /\ cellA M (rn_dtls rn + 24) 8 (rn_tp rn)
/\ (forall x, S 0x10000 <= x < S 0x23100 \/ S 0x23120 <= x < S 0x23160 \/ S 0x231e0 <= x < S 0x23340 \/ S 0x238e0 <= x < S 0x12cda0 \/ S 0x12ce40 <= x < S 0x137140 \/ S 0x137640 <= x < S 0x691000 -> byte_at M x 0)
/\ Forall (fun g => shadow_blk M (fst g) (snd g)) ART_GLOBALS
/\ (forall a : word, in_shadow_rw (U a) -> M a <> None).
Definition cs_zone (rn : art_run) (a : Z) : Prop :=
0x134450 <= a < 0x134458 \/ 0x134518 <= a < 0x134530 \/ rn_tp rn + 8 <= a < rn_tp rn + 16 \/ rn_dtls rn + 24 <= a < rn_dtls rn + 32 \/ S 0x10000 <= a < S 0x691000.
Definition art_fsinv (rn : art_run) (g : art_fsg) (FF LK : list fframe) (M : word -> option byte) : Prop :=
let fs := ar_fs (rn_ar rn) in
art_fs_geo rn
/\ wrA M fs FS_BYTES
/\ cellA M (rn_tp rn) 8 fs /\ cellA M (rn_t rn + 72) 8 fs
/\ cellA M (fs + 88) 8 20 /\ cellA M (fs + 96) 1 (if fg_gc g then 1 else 0)
/\ (forall c, 0 <= c <= 10 -> cellA M (fs + 8 * c) 8 (fg_hint g c) /\ 0 <= fg_hint g c < 2 ^ 64)
/\ List.NoDup (map ff_addr (FF ++ LK))
/\ (forall f, In f (FF ++ LK) ->
0 <= ff_class f <= 4
/\ (exists i, fs_slot fs f i /\ cellA M (ff_addr f + ff_bytes (ff_class f) - 8) 8 (fs_flag fs (ff_class f) i))
/\ cellA M (ff_addr f + 24) 8 (ff_rs f - 32) /\ 32 <= ff_rs f <= 2 ^ 47 + 32)
/\ (forall c i, 0 <= c <= 10 -> 0 <= i < fs_nfr c ->
exists b, cellA M (fs_flag fs c i) 1 b /\ (b = 0 \/ b = 1)
/\ (b = 1 <-> exists f, In f (FF ++ LK) /\ ff_class f = c /\ ff_addr f = fs_frame fs c i))
/\ art_c_statics rn M.
Definition art_fsinv_frame_law_goal : Prop := art_fsinv_frame_law art_fsg art_fsinv.
Definition art_fsinv_client_law : Prop :=
forall rn g FF LK M M',
art_fsinv rn g FF LK M -> mem_grows M M' ->
(forall x : word, let a := U x in
(ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES \/ rn_t rn + 72 <= a < rn_t rn + 80 \/ rn_tp rn <= a < rn_tp rn + 8) ->
~ in_fframe FF a -> M' x = M x) ->
(forall x : word, cs_zone rn (U x) -> M' x = M x) ->
art_fsinv rn g FF LK M'.
Definition art_fsinv_wf_law : Prop :=
forall rn g FF LK M, art_fsinv rn g FF LK M ->
(forall f, In f FF -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES
/\ ff_addr f mod ff_bytes (ff_class f) = 0 /\ In (ff_class f) [0; 1; 2; 3; 4]
/\ defined M (ff_addr f) (ff_bytes (ff_class f))
/\ fframes_apart (ff_addr f) (ff_bytes (ff_class f)) (ff_remove (ff_addr f) FF ++ LK))
/\ app_mem (ar_fs (rn_ar rn)) FS_BYTES /\ ar_fs (rn_ar rn) + FS_BYTES <= ahl_ceil (rn_ar rn)
/\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x691000 <= ar_fs (rn_ar rn))
/\ List.NoDup (map ff_addr (FF ++ LK)) /\ defined M (ar_fs (rn_ar rn)) FS_BYTES.
Definition art_fsinv_release_law : Prop :=
forall rn g FF LK M M' F k rs,
art_fsinv rn g FF LK M -> In (F, k, rs) FF -> mem_grows M M' ->
(exists i, 0 <= i < fs_nfr k /\ F = fs_frame (ar_fs (rn_ar rn)) k i /\ cellA M' (fs_flag (ar_fs (rn_ar rn)) k i) 1 0
/\ (forall x : word, U x <> fs_flag (ar_fs (rn_ar rn)) k i ->
(ar_fs (rn_ar rn) <= U x < ar_fs (rn_ar rn) + FS_BYTES \/ rn_t rn + 72 <= U x < rn_t rn + 80 \/ rn_tp rn <= U x < rn_tp rn + 8) ->
~ in_fframe FF (U x) -> M' x = M x)) ->
(forall x : word, cs_zone rn (U x) -> M' x = M x) ->
art_fsinv rn g (ff_remove F FF) LK M'.
Definition art_fsinv_leak_law : Prop :=
forall rn g FF LK M FX, art_fsinv rn g FF LK M -> incl FX FF ->
art_fsinv rn g (filter (fun f => negb (existsb (fun h => Z.eqb (ff_addr h) (ff_addr f)) FX)) FF) (FX ++ LK) M.
Definition art_fsinv_handoff : Prop :=
forall rn M, art_fs_geo rn -> wrA M (ar_fs (rn_ar rn)) FS_BYTES ->
cellA M (rn_tp rn) 8 (ar_fs (rn_ar rn)) -> cellA M (rn_t rn + 72) 8 (ar_fs (rn_ar rn)) -> cellA M (ar_fs (rn_ar rn) + 88) 8 20 ->
(forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + 4096 + 32768 -> ~ (ar_fs (rn_ar rn) + 88 <= a < ar_fs (rn_ar rn) + 96) -> byte_at M a 0) ->
art_c_statics rn M ->
art_fsinv rn art_fsg0 [] [] M.
Lemma fs_frame_inj : ltac2:(TCodec.tc2 tcn__JatFsInv "D';'8&Lr4r3r2%43321r1%63541%83931&Q2z%2219%<3=:9p021p061pRN@1pRLA1pS2B1pRFC1").
Proof.
intros fs k i i' E Hk. unfold fs_frame, ff_bytes in E.
assert (P : 0 < 64 * 2 ^ k) by (assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia); lia).
assert (E' : i * (64 * 2 ^ k) = i' * (64 * 2 ^ k)) by lia.
apply Z.mul_reg_r in E'; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_fsinv_flagptr := (ltac2:(TCodec.tc2 tcn__JatFsInv "R9'N'H'1&G%211'QFyR0%211'4y8%511%311p051';&Ir>r=r;r:r7%6554321r?r9%9527514&Q0'6%12==%221>(5r6%24AA;1r5%446C21%9361Ar8%74FF1@%84:G15r<%>3;21&D&O&Q6&Q1&F%11:%32G1+8%6221u8%:59Q021B%71L%92Q11%;216%>5=Q415Hp051p0A1p0G1p0Q21p0Q61pRDQ>1pS:Q?1pS8Q@1pS2QA1pJQB1pQ8QD1pQ6QE1pQ2QN1pNQO1pQ0R01pLR11pRJR51pRHR61pS6R81")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 0%nat 0%nat).
Variable g : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 1%nat 0%nat).
Variable g' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 2%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 3%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 4%nat 0%nat).
Variable FF' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 5%nat 0%nat).
Variable LK' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 7%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 8%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 9%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 10%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 11%nat 0%nat).
Variable rs' : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 12%nat 0%nat).
Variable fl : ltac:(sec_ty2 constr:(SEC_T_art_fsinv_flagptr) 13%nat 0%nat).
Lemma art_fsinv_flagptr : ltac:(sec_stmt2 constr:(SEC_T_art_fsinv_flagptr) 14%nat 0%nat).
Proof.
intros I1 I2 H1 H2 C.
destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & FR1 & _). destruct I2 as (_ & _ & _ & _ & _ & _ & _ & _ & FR2 & _).
destruct (FR1 (F, k, rs) ltac:(apply in_or_app; left; exact H1)) as (K1 & (i & (Hi & A1) & C1) & _).
destruct (FR2 (F, k, rs') ltac:(apply in_or_app; left; exact H2)) as (K2 & (i' & (Hi' & A2) & C2) & _).
unfold ff_class, ff_addr in *. cbn [fst snd] in *.
assert (E : i = i') by (apply (fs_frame_inj (ar_fs (rn_ar rn)) k); [congruence | lia]). subst i'.
unfold cell in *. rewrite C2. rewrite <- C1. exact C.
Qed.
End SE.
Lemma le8_zero : ltac2:(TCodec.tc2 tcn__JatFsInv "A'8'1'QFy8%211%411&Au8&QEyR0z%3221%6251&:%62;4%23;18%@3;41").
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.
Lemma le1_zero : ltac2:(TCodec.tc2 tcn__JatFsInv "C'8'1'QFy8%211%411&Au1&QEyR0z%3221%6251(0%62;4(3%11<%43=31%B3=61").
Proof. vm_compute. repeat f_equal; apply bv_eq; reflexivity. Qed.
Lemma cell_zero_bytes : ltac2:(TCodec.tc2 tcn__JatFsInv "QJ'QFyR0%211'4y8%511%311p051';'2'9'8r1u1%33521u8%53741%7231&Q2zr3%3221&Q1r4&Q4%115%4231&Q5+2+R0%3221%=251'7%?2>E&Q3r5%<11%32I1%6251&Er8r7r2%E221%5341Ip071pS0Q61&D&Or6%35291?Op051p0E1p0Q01p0Q51pS4Q>1pR@Q@1pQ6QB1").
Proof.
intros M a n Hn Ha Hhi HB. unfold cell.
assert (UA : bv_unsigned (Z_to_bv 64 a) = a) by (apply art_u_lit; destruct Hn as [-> | ->]; lia).
rewrite (MemSplit.rdn_const _ M (Z_to_bv 64 a) n (Z_to_bv 8 0)).
- destruct Hn as [-> | ->]; [rewrite le1_zero | rewrite le8_zero]; reflexivity.
- rewrite UA. lia.
- intros x Hx. rewrite UA in Hx. specialize (HB (bv_unsigned x - a) ltac:(lia)). unfold byte_at in HB.
replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in HB by lia. rewrite Z_to_bv_bv_unsigned in HB. exact HB.
Qed.
Theorem art_fsinv_handoff_proved : ltac2:(TCodec.tc2 tcn__JatFsInv "1&J").
Proof.
intros rn M GEO W CTP CT C88 Z0 CS. unfold art_fsinv. cbn zeta.
pose proof GEO as (G1 & G2 & G3 & G4 & (G5 & G6 & G7) & G8). unfold FS_BYTES in *.
set (fs := ar_fs (rn_ar rn)) in *.
split; [exact GEO|]. split; [exact W|]. split; [exact CTP|]. split; [exact CT|]. split; [exact C88|].
split. { cbn [fg_gc art_fsg0]. apply cell_zero_bytes; [left; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
split. { intros c Hc. cbn [fg_hint art_fsg0]. split; [|lia]. apply cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
split. { cbn. constructor. }
split. { intros f Hf. cbn in Hf. contradiction. }
split; [|exact CS].
intros c i Hc Hi. exists 0. pose proof (fs_flag_below_frames fs c i Hc Hi) as FB.
split. { apply cell_zero_bytes; [left; reflexivity | lia | lia |]. intros j Hj. apply Z0; lia. }
split; [left; reflexivity|]. split; [intros X; discriminate X | intros (f & Hf & _); cbn in Hf; contradiction].
Qed.
