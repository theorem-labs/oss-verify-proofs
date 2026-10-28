(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r UI1w UI5o UI21 UI5l
YI00 YI05 YI5a UI5f UI56 UI57 UI23 YI59 UIZt.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition HDRZ : Z := Eval vm_compute in (ubs0_A_read_frameconfig + 0x38).
Definition BNEZ : Z := Eval vm_compute in (ubs0_A_read_frameconfig + 0x18c).
Definition hdr_ends : list Z := [2; 4; 6; 7; 9].
Definition hdr_conds (k : nat) : list acond :=
map (fun e => mkAC BC_GEU (SOff 33 0) (SOff 34 e)) (firstn k hdr_ends) ++
match nth_error hdr_ends k with Some e => [mkAC BC_LTU (SOff 33 0) (SOff 34 e)] | None => [] end.
Definition hdr_nbytes (k : nat) : nat := nth k [0; 2; 4; 6; 7; 9]%nat 9%nat.
Definition byte_chunks (k0 cnt : nat) : list YP09.chunk :=
map (fun i => mkChunk (Z.of_nat i) (CVal 1 (SOff (k0 + i) 0))) (seq 0 cnt).
Definition hdr_breg (k : nat) : list YP09.region :=
match k with O => [] | _ => [YP09.mkRegion (Some 35%nat) 0 (Z.of_nat (hdr_nbytes k)) 0 0 (byte_chunks 36 (hdr_nbytes k))] end.
Definition byte_facts : list (nat * afact) := map (fun i => ((36 + i)%nat, mkAF 0 255 0)) (seq 0 9).
Definition ss_hdr (k : nat) : sstate :=
mkSS RFC sr_atoms
([ YP09.mkRegion (Some 2%nat) (-RFC_FRAME) 0 (-RFC_FRAME) 0 [] ;
YP09.mkRegion (Some 10%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0))] ;
YP09.mkRegion (Some 11%nat) 0 32 0 32 [] ] ++ hdr_breg k)
None
(mkFacts ([ (2%nat, mkAF (CEIL_MIN + RFC_DEPTH) (2^63) 4); (10%nat, mkAF CEIL_MIN (2^63) 3);
(11%nat, mkAF CEIL_MIN (2^63) 3); (12%nat, mkAF 1 100000000 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 CEIL_MAX 0);
(34%nat, mkAF 0 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0) ] ++ byte_facts)
(hdr_conds k)
[ (SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 35 0) ]).
Lemma region_ok_bytes : forall E mem n P (cnt : nat) k0,
bv_unsigned (ew E n) = P -> 0 <= P -> P + Z.of_nat cnt <= 2 ^ 64 ->
(forall j, (j < cnt)%nat -> ew E (k0 + j)%nat = Z_to_bv 64 (byte_at mem (P + Z.of_nat j)) /\ present mem (P + Z.of_nat j)) ->
region_ok ubs0segs E mem (YP09.mkRegion (Some n) 0 (Z.of_nat cnt) 0 0 (byte_chunks k0 cnt)).
Proof using.
intros E mem n P cnt k0 Hn HP Hhi Hb.
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. unfold byte_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj).
apply in_seq in Hj. destruct (Hb j ltac:(lia)) as [He Hp].
pose proof (byte_at_range mem (P + Z.of_nat j)) as Hr.
eapply (chunk_ok_val _ _ _ _ _ _ _ (byte_at mem (P + Z.of_nat j))).
- cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- apply byte_at_val. exact Hp.
Qed.
Definition rfc_post_x (MR : MR_t) (regs : bvmap 5 word) (STK sp0 : Z) (FP : list (Z * Z)) L A mem md
(Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (memc : word -> option byte) (PAYLOAD : list Z) (b : rbound) (c' : config) : Prop :=
exists L2 A2 regs2 mem2 md2 (res cur2 : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs memc (b + i)) /\
word_mem ubs0segs mem2 st pdata /\ word_mem ubs0segs mem2 (st + 8) nb /\
word_mem ubs0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ fst (fst (parse_frameN N (skipn (Z.to_nat cur) PAYLOAD))) = false /\
(exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ res_ok A2 (rfc_rb_fail b)) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx (LPAL IMG : list Z),
obj_at ubs0segs mem2 dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (blocks L2 A2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
parse_frameN N (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr, fgen, delay, tidx, nlp, LPAL, IMG), skipn (Z.to_nat cur2) PAYLOAD) /\
garr8 ubs0segs mem2 img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem2 lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
res_ok A2 (rfc_rb_ok b fattr nlp N))).
Definition rfc_case_x (MR : MR_t) (C : Z -> Prop) : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (PAYLOAD : list Z) (b : rbound),
C (nb - cur) ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> word_mem ubs0segs memc (st + 16) cur ->
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac b -> rfc_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs)) mdc)
(rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD b).
Lemma rfc_specX_of_cases : forall API,
rfc_case_x (aa_MR API) (fun av => av < 2) -> rfc_case_x (aa_MR API) (fun av => 2 <= av < 4) ->
rfc_case_x (aa_MR API) (fun av => 4 <= av < 6) -> rfc_case_x (aa_MR API) (fun av => 6 <= av < 7) ->
rfc_case_x (aa_MR API) (fun av => 7 <= av < 9) -> rfc_case_x (aa_MR API) (fun av => 9 <= av) ->
rfc_specX API.
Proof using.
intros API C0 C1 C2 C3 C4 C5. unfold rfc_specX. intros until b. intros HJ.
destruct (Z_lt_le_dec (nb - cur) 2) as [H|H]; [revert HJ; apply C0; exact H|].
destruct (Z_lt_le_dec (nb - cur) 4) as [H1|H1]; [revert HJ; apply C1; lia|].
destruct (Z_lt_le_dec (nb - cur) 6) as [H2|H2]; [revert HJ; apply C2; lia|].
destruct (Z_lt_le_dec (nb - cur) 7) as [H3|H3]; [revert HJ; apply C3; lia|].
destruct (Z_lt_le_dec (nb - cur) 9) as [H4|H4]; [revert HJ; apply C4; lia|].
revert HJ; apply C5; lia.
Qed.
Lemma word_mem_mod : forall m a v, word_mem ubs0segs m a v -> word_mem ubs0segs m a (v mod 2 ^ 64).
Proof using.
intros m a v H k Hk. rewrite (H k Hk). f_equal. unfold le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma Z_to_bv64_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof using.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma val_mem_2_bytes : forall m a b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
mbyte ubs0segs m a = Some (Z_to_bv 8 b0) -> mbyte ubs0segs m (a + 1) = Some (Z_to_bv 8 b1) ->
val_mem ubs0segs m a 2 (b0 + 256 * b1).
Proof using.
intros m a b0 b1 R0 R1 H0 H1 k Hk. unfold le_byte. change (8 * Z.of_nat 2) with 16.
rewrite (Z.mod_small (b0 + 256 * b1)) by lia.
assert (E0 : (b0 + 256 * b1) mod 256 = b0) by (symmetry; apply (Z.mod_unique (b0 + 256 * b1) 256 b1 b0); lia).
assert (E1 : (b0 + 256 * b1) / 256 = b1) by (symmetry; apply (Z.div_unique (b0 + 256 * b1) 256 b1 b0); lia).
destruct k as [|[|k]]; [| |lia].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Z.mul_0_r, Z.shiftr_0_r, H0, E0. reflexivity.
- change (Z.of_nat 1) with 1. change (8 * 1) with 8. rewrite H1, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite E1, (Z.mod_small b1) by lia. reflexivity.
Qed.
End f.
Ltac wr4_tac HU2 HU10 HU11 slv :=
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; slv |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU10 | cbn [r_wlo r_whi]; intros _; slv |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU11 | cbn [r_wlo r_whi]; intros _; slv |];
repeat (apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]); apply wr_ok_nil.
Ltac frame_wordE HS HU2 HE n rr :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (- dd) (SOff n 0) spv (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 20
| ew_havocF; exact HU2
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Ltac dst_byte HS HU11 n HBj :=
eapply (st_chunk_byte _ _ _ 2%nat _ 11%nat _ (SOff n 0) _ _ HS);
[ reflexivity | reflexivity | cbv; auto 30 | ew_havocF; exact HU11
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HBj, Z_to_bv_bv_unsigned; reflexivity
| apply byte_at_range ].
Ltac dst_zero HS HU11 off len :=
lazymatch goal with |- mbyte _ _ (?d + ?c) = _ =>
replace (d + c) with (d + off + (c - off)) by lia;
eapply (st_chunk_zero _ _ _ 2%nat _ 11%nat off len d (c - off) HS);
[ reflexivity | reflexivity | cbv; auto 30 | ew_havocF; exact HU11 | lia ]
end.
Ltac hdr_frames HU2 HU10 HU11 slv :=
repeat match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(rewrite ?HU2, ?HU10, ?HU11; slv)
end.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Definition hdr_bytes (m : word -> option byte) (dst b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) : Prop :=
mbyte ubs0segs m (dst + 16) = Some (Z_to_bv 8 b0) /\ mbyte ubs0segs m (dst + 17) = Some (Z_to_bv 8 b1) /\
mbyte ubs0segs m (dst + 18) = Some (Z_to_bv 8 0) /\ mbyte ubs0segs m (dst + 19) = Some (Z_to_bv 8 0) /\
mbyte ubs0segs m (dst + 20) = Some (Z_to_bv 8 b2) /\ mbyte ubs0segs m (dst + 21) = Some (Z_to_bv 8 b3) /\
mbyte ubs0segs m (dst + 22) = Some (Z_to_bv 8 0) /\ mbyte ubs0segs m (dst + 23) = Some (Z_to_bv 8 0) /\
mbyte ubs0segs m (dst + 24) = Some (Z_to_bv 8 b4) /\ mbyte ubs0segs m (dst + 25) = Some (Z_to_bv 8 b5) /\
mbyte ubs0segs m (dst + 26) = Some (Z_to_bv 8 b7) /\ mbyte ubs0segs m (dst + 27) = Some (Z_to_bv 8 b8) /\
mbyte ubs0segs m (dst + 28) = Some (Z_to_bv 8 b6).
Lemma hdr_bytes_frame : forall m m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8,
hdr_bytes m dst b0 b1 b2 b3 b4 b5 b6 b7 b8 ->
(forall i, 16 <= i < 29 -> mbyte ubs0segs m' (dst + i) = mbyte ubs0segs m (dst + i)) ->
hdr_bytes m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8.
Proof using.
intros m m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8 H Hf. unfold hdr_bytes in *.
rewrite !Hf by lia. exact H.
Qed.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Lemma rfc_fail_of_img : forall b N, 0 <= N -> rb_le (rb_free (rb_malloc b N) N) (rfc_rb_fail b).
Proof using.
intros b N HN. unfold rfc_rb_fail. apply (rb_le_trans _ (rb_acc b 1 0)); [apply rb_free_malloc_acc; lia|].
apply rb_acc_mono; [apply rb_le_refl | lia | lia].
Qed.
Lemma rfc_room_N : forall b N, rfc_room b N -> 0 <= N -> room b N.
Proof using.
intros b N HR HN. apply (room_mono b (rb_acc b 1 PALSLACK) N (Z.max N PALMAX)); [apply rb_acc_le; unfold PALSLACK; lia | lia | exact HR].
Qed.
Lemma rx_garr8_byte_at : forall m q (P : list Z) j, garr8 ubs0segs m q P -> (j < length P)%nat -> nth j P 0 = byte_at m (q + Z.of_nat j).
Proof using.
intros m q P j H Hj. unfold byte_at. rewrite (garr8_mbyte _ m q P j H Hj). rewrite Z_to_bv_unsigned.
pose proof (proj2 (H j Hj)) as Rg. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma hdr_at_of_garr8 : forall memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8,
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur -> cur + 9 <= nb ->
b0 = byte_at memc (pdata + cur) -> b1 = byte_at memc (pdata + cur + 1) -> b2 = byte_at memc (pdata + cur + 2) ->
b3 = byte_at memc (pdata + cur + 3) -> b4 = byte_at memc (pdata + cur + 4) -> b5 = byte_at memc (pdata + cur + 5) ->
b6 = byte_at memc (pdata + cur + 6) -> b7 = byte_at memc (pdata + cur + 7) -> b8 = byte_at memc (pdata + cur + 8) ->
hdr_at PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8.
Proof using.
intros memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8 HPL HPLn Hcur Hle -> -> -> -> -> -> -> -> ->.
unfold hdr_at. repeat split; (rewrite (rx_garr8_byte_at memc pdata PAYLOAD) by (exact HPL || lia); f_equal; lia).
Qed.
Lemma post_of_pal_x : forall (regs : bvmap 5 word) STK sp0 FP L A mem md (Bb : list (Z * Z)) (st dst N pdata nb cur cur1 r : Z)
(memc mem1 : word -> option byte) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) (PAYLOAD : list Z) (bq : rbound) c',
pal_post_x API regs STK sp0 FP L A mem md Bb st dst N nb cur1 (3 * (b7 + 256 * b8)) r mem1 pdata PAYLOAD bq c' ->
alloc_ceiling + RFC_STK <= spZ regs -> spZ regs <= st -> spZ regs <= dst -> (st + 24 <= dst \/ dst + 32 <= st) ->
dst + 32 <= 2 ^ 63 -> st + 24 <= 2 ^ 63 -> 0 <= pdata < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_DEPTH <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs mem1 a = mbyte ubs0segs memc a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem1 (b + i) = mbyte ubs0segs memc (b + i)) ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> cur <= cur1 -> 1 <= N ->
Z.land b0 1 <> 0 ->
(r = 0 -> hdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 b6 b7 b8) ->
bytes_ok [b0; b1; b2; b3; b4; b5; b6; b7; b8] ->
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur ->
(r = 0 -> cur1 = cur + 9 /\ cur + 9 <= nb /\
b0 = byte_at memc (pdata + cur) /\ b1 = byte_at memc (pdata + cur + 1) /\ b2 = byte_at memc (pdata + cur + 2) /\
b3 = byte_at memc (pdata + cur + 3) /\ b4 = byte_at memc (pdata + cur + 4) /\ b5 = byte_at memc (pdata + cur + 5) /\
b6 = byte_at memc (pdata + cur + 6) /\ b7 = byte_at memc (pdata + cur + 7) /\ b8 = byte_at memc (pdata + cur + 8)) ->
(r <> 0 -> nb < cur + 9) ->
rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD bq c'.
Proof using.
intros regs STK sp0 FP L A mem md Bb st dst N pdata nb cur cur1 r memc mem1 b0 b1 b2 b3 b4 b5 b6 b7 b8 PAYLOAD bq c'
HP Hsp Hst1 Hdst1 Hsd Hdst2 Hst2 Hpd Hnb Hfr1 Hbb1 Wp Wn Hcc HN Hodd Hhb HB HPL HPLn Hcur0 Hr9 Hn9.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFRv : RFC_FRAME = 64) by reflexivity.
assert (HDPv : RFC_DEPTH = 8256) by reflexivity. assert (HSTKv : RFC_STK = 8272) by reflexivity.
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & lp & lpb & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|].
assert (Hm : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs mem2 a = mbyte ubs0segs memc a).
{ intros a Ha Hn1 Hn2 Hn3. rewrite (Hfr2 a Ha) by lia. apply (Hfr1 a Ha); lia. }
split; [exact Hm|].
split.
{ intros b m i Hb Hi. rewrite (Hbb2 b m i Hb Hi). apply (Hbb1 b m i Hb Hi). }
split.
{ intros k Hk. rewrite (Hm (st + Z.of_nat k)) by lia. apply Wp. exact Hk. }
split.
{ intros k Hk. rewrite (Hm (st + 8 + Z.of_nat k)) by lia. apply Wn. exact Hk. }
split; [exact Wc2|]. split; [lia|].
assert (HAT : r = 0 -> hdr_at PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8).
{ intros Hz. destruct (Hr9 Hz) as (Hc1 & Hle & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
exact (hdr_at_of_garr8 memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8 HPL HPLn Hcur0 Hle E0 E1 E2 E3 E4 E5 E6 E7 E8). }
assert (Hfl : YO07.flag (b0 + 256 * b1) 1 = true).
{ unfold YO07.flag. rewrite land1_low by lia. destruct (Z.eqb_spec (Z.land b0 1) 0) as [Hz|Hz]; [exfalso; exact (Hodd Hz) | reflexivity]. }
destruct ALT as [(Hres & Hleak & Hwhy & HRf) | (Hres & Hr & Wl & Wi & (lpa & -> & Hlpa & Hgl) & HB2 & Hfit2 & Hc2 & Hgi & HRok)].
{ left. split; [exact Hres|]. split; [| split; [exact Hleak | exact HRf]].
apply (parse_frameN_fail N PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur0 HN).
destruct (Z.eq_dec r 0) as [Hz|Hz].
- right. destruct (Hr9 Hz) as (Hc1 & Hle & _). split; [exact (HAT Hz)|]. split; [lia|].
unfold hdr_palsz. rewrite Hfl. destruct Hwhy as [Hw|Hw]; [exfalso; exact (Hw Hz) | rewrite HPLn; lia].
- left. rewrite HPLn. pose proof (Hn9 Hz). lia. }
right. split; [exact Hres|].
specialize (Hhb Hr). destruct (Hr9 Hr) as (Hc1 & Hle & _).
assert (Hhb2 : hdr_bytes mem2 dst b0 b1 b2 b3 b4 b5 b6 b7 b8).
{ eapply hdr_bytes_frame; [exact Hhb|]. intros i Hi. apply Hfr2; lia. }
destruct Hhb2 as (M16 & M17 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27 & M28).
pose proof (Z.mod_pos_bound lp (2 ^ 64) ltac:(lia)) as Hlp64.
assert (Himg : In (img, N) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 img N (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) Himg ltac:(lia)) as (Hi0 & Hi1 & _).
exists (lp mod 2 ^ 64), lpa, img, (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5), (b7 + 256 * b8), b6,
(firstn (Z.to_nat (3 * (b7 + 256 * b8))) (skipn (Z.to_nat (cur + 9)) PAYLOAD)),
(firstn (Z.to_nat N) (skipn (Z.to_nat (cur + 9 + 3 * (b7 + 256 * b8))) PAYLOAD)).
split.
{ apply frameconfig_obj; try assumption; try lia. apply word_mem_mod. exact Wl. }
split.
{ intros Hz. exfalso. rewrite land1_low in Hz by lia. exact (Hodd Hz). }
split; [rewrite Z_to_bv64_mod; exact Hlpa|].
rewrite land1_low by lia. destruct (Z.eqb_spec (Z.land b0 1) 0) as [Hz|Hz]; [exfalso; exact (Hodd Hz)|].
split; [exact HB2|].
split.
{ rewrite (parse_frameN_ok N PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur0 HN (HAT Hr) ltac:(lia)).
2:{ unfold hdr_palsz. rewrite Hfl. rewrite HPLn. lia. }
unfold hdr_palsz. rewrite Hfl. rewrite Hc2, Hc1. reflexivity. }
split; [rewrite Hc1 in Hgi; exact Hgi|].
split; [rewrite length_firstn, length_skipn; lia|].
split; [intros _; split; [rewrite Hc1 in Hgl; exact Hgl | rewrite length_firstn, length_skipn; lia]|].
unfold rfc_rb_ok. rewrite land1_low by lia. destruct (Z.eqb_spec (Z.land b0 1) 0) as [Hz'|Hz']; [exfalso; exact (Hodd Hz') | exact HRok].
Qed.
Lemma post_of_img_x : forall (regs : bvmap 5 word) STK sp0 FP L A mem md (Bb : list (Z * Z)) (st dst N pdata nb cur cur1 r : Z)
(memc mem1 : word -> option byte) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) (PAYLOAD : list Z) (bq : rbound) c',
img_post_x API regs STK sp0 FP L A mem md Bb [] st dst N nb cur1 0 r mem1 pdata PAYLOAD bq c' ->
alloc_ceiling + RFC_STK <= spZ regs -> spZ regs <= st -> spZ regs <= dst -> (st + 24 <= dst \/ dst + 32 <= st) ->
dst + 32 <= 2 ^ 63 -> st + 24 <= 2 ^ 63 -> 0 <= pdata < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_DEPTH <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs mem1 a = mbyte ubs0segs memc a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem1 (b + i) = mbyte ubs0segs memc (b + i)) ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> cur <= cur1 -> 1 <= N ->
(r = 0 -> Z.land b0 1 = 0 /\ hdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 b6 b7 b8) ->
bytes_ok [b0; b1; b2; b3; b4; b5; b6; b7; b8] ->
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur ->
(r = 0 -> cur1 = cur + 9 /\ cur + 9 <= nb /\
b0 = byte_at memc (pdata + cur) /\ b1 = byte_at memc (pdata + cur + 1) /\ b2 = byte_at memc (pdata + cur + 2) /\
b3 = byte_at memc (pdata + cur + 3) /\ b4 = byte_at memc (pdata + cur + 4) /\ b5 = byte_at memc (pdata + cur + 5) /\
b6 = byte_at memc (pdata + cur + 6) /\ b7 = byte_at memc (pdata + cur + 7) /\ b8 = byte_at memc (pdata + cur + 8)) ->
(r <> 0 -> nb < cur + 9) ->
rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD bq c'.
Proof using.
intros regs STK sp0 FP L A mem md Bb st dst N pdata nb cur cur1 r memc mem1 b0 b1 b2 b3 b4 b5 b6 b7 b8 PAYLOAD bq c'
HP Hsp Hst1 Hdst1 Hsd Hdst2 Hst2 Hpd Hnb Hfr1 Hbb1 Wp Wn Hcc HN Hhb HB HPL HPLn Hcur0 Hr9 Hn9.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFRv : RFC_FRAME = 64) by reflexivity.
assert (HDPv : RFC_DEPTH = 8256) by reflexivity. assert (HSTKv : RFC_STK = 8272) by reflexivity.
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|].
assert (Hm : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs0segs mem2 a = mbyte ubs0segs memc a).
{ intros a Ha Hn1 Hn2 Hn3. rewrite (Hfr2 a Ha) by lia. apply (Hfr1 a Ha); lia. }
split; [exact Hm|].
split.
{ intros b m i Hb Hi. rewrite (Hbb2 b m i Hb Hi). apply (Hbb1 b m i Hb Hi). }
split.
{ intros k Hk. rewrite (Hm (st + Z.of_nat k)) by lia. apply Wp. exact Hk. }
split.
{ intros k Hk. rewrite (Hm (st + 8 + Z.of_nat k)) by lia. apply Wn. exact Hk. }
split; [exact Wc2|]. split; [lia|].
assert (HAT : r = 0 -> hdr_at PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8).
{ intros Hz. destruct (Hr9 Hz) as (Hc1 & Hle & E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
exact (hdr_at_of_garr8 memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8 HPL HPLn Hcur0 Hle E0 E1 E2 E3 E4 E5 E6 E7 E8). }
destruct ALT as [(Hres & Hleak & Hwhy & HRf) | (Hres & Hr & Wl & Wi & HB2 & Hfit2 & Hc2 & Hlpk & Hgi & HRok)].
{ left. split; [exact Hres|]. split; [| split; [exact Hleak | exact (res_ok_mono _ _ _ (rfc_fail_of_img bq N ltac:(lia)) HRf)]].
apply (parse_frameN_fail N PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur0 HN).
destruct (Z.eq_dec r 0) as [Hz|Hz].
- right. destruct (Hr9 Hz) as (Hc1 & Hle & _). destruct (Hhb Hz) as [Heven _]. split; [exact (HAT Hz)|]. split; [lia|].
unfold hdr_palsz, YO07.flag. rewrite land1_low, Heven by lia. cbn [Z.eqb negb].
destruct Hwhy as [Hw|Hw]; [exfalso; exact (Hw Hz) | rewrite HPLn; lia].
- left. rewrite HPLn. pose proof (Hn9 Hz). lia. }
right. split; [exact Hres|].
destruct (Hhb Hr) as [Heven Hhb1]. destruct (Hr9 Hr) as (Hc1 & Hle & _).
assert (Hhb2 : hdr_bytes mem2 dst b0 b1 b2 b3 b4 b5 b6 b7 b8).
{ eapply hdr_bytes_frame; [exact Hhb1|]. intros i Hi. apply Hfr2; lia. }
destruct Hhb2 as (M16 & M17 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26 & M27 & M28).
assert (Himg : In (img, N) (blocks L2 A2)) by (eapply blocks_perm_in; [exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 img N (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) Himg ltac:(lia)) as (Hi0 & Hi1 & _).
exists 0, 0, img, (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5), (b7 + 256 * b8), b6,
(@nil Z), (firstn (Z.to_nat N) (skipn (Z.to_nat (cur + 9)) PAYLOAD)).
split.
{ apply frameconfig_obj; try assumption; try lia. }
split; [intros _; reflexivity|]. split; [reflexivity|].
rewrite land1_low, Heven by lia. cbn [Z.eqb].
split; [exact HB2|].
split.
{ rewrite (parse_frameN_ok N PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8 Hcur0 HN (HAT Hr) ltac:(lia)).
2:{ unfold hdr_palsz, YO07.flag. rewrite land1_low, Heven by lia. cbn [Z.eqb negb]. rewrite HPLn. lia. }
unfold hdr_palsz, YO07.flag. rewrite land1_low, Heven by lia. cbn [Z.eqb negb]. rewrite Z.add_0_r, Hc2, Hc1. reflexivity. }
split; [rewrite Hc1 in Hgi; exact Hgi|].
split; [rewrite length_firstn, length_skipn; lia|].
split; [intros Hnz; exfalso; apply Hnz; reflexivity|].
unfold rfc_rb_ok. rewrite land1_low, Heven by lia. cbn [Z.eqb]. exact HRok.
Qed.
Lemma cs_hdr_val_range : forall memc pdata nb cur i, 0 <= hdr_val memc pdata nb cur i < 256.
Proof using.
intros memc pdata nb cur i. unfold hdr_val, hdr_valk. destruct (hdr_src i) as [j e]. cbn beta iota.
match goal with |- context [if ?c then _ else _] => destruct c end; [apply byte_at_range | lia].
Qed.
Lemma cs_hdr_val_at : forall memc pdata nb cur i j e, hdr_src i = (j, e) -> 0 < e <= 9 -> cur + e <= nb ->
hdr_val memc pdata nb cur i = byte_at memc (pdata + cur + j).
Proof using.
intros memc pdata nb cur i j e Hs He Hn. unfold hdr_val, hdr_valk. rewrite Hs. cbn beta iota.
assert (E1 : (0 <? e) = true) by (apply Z.ltb_lt; lia). assert (E2 : (e <=? 9) = true) by (apply Z.leb_le; lia).
assert (E3 : (cur + e <=? nb) = true) by (apply Z.leb_le; lia). rewrite E1, E2, E3. reflexivity.
Qed.
Lemma rfc_case_all : rfc_case_x MR (fun _ => True).
Proof using IMG LAWS.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFRv : RFC_FRAME = 64) by reflexivity. assert (HDPv : RFC_DEPTH = 8256) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hroom : room bq N) by (apply (rfc_room_N bq N HRm); lia).
assert (Hrv : hdr_rv nb cur 9 = 0 \/ hdr_rv nb cur 9 = 2 ^ 64 - 1).
{ unfold hdr_rv. destruct (cur + 9 <=? nb); [left | right]; reflexivity. }
assert (Hcur1 : cur <= hdr_cur nb cur 9 <= nb) by (unfold hdr_cur; destruct (Z.leb_spec (cur + 9) nb); lia).
assert (Hr0 : hdr_rv nb cur 9 = 0 -> cur + 9 <= nb /\ hdr_cur nb cur 9 = cur + 9).
{ unfold hdr_rv, hdr_cur. destruct (Z.leb_spec (cur + 9) nb); intros Hz; [split; [lia | reflexivity] | lia]. }
assert (Hrn : hdr_rv nb cur 9 <> 0 -> nb < cur + 9).
{ unfold hdr_rv. destruct (Z.leb_spec (cur + 9) nb); intros Hz; [exfalso; apply Hz; reflexivity | lia]. }
eapply SR_bind.
{ exact (rfc_hdr_x API IMG STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HJ HBc Hpd Hra0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 Hcur Hnb Wp Wn Wc). }
intros c1 HP1.
destruct HP1 as (regs1 & mem1 & -> & HJ1 & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R22 & R23 & R24 & R25 & R26 & R27
& S8 & S16 & S24 & S32 & S40 & S48 & S56 & Wp1 & Wn1 & Wc1 & HDB & Hfr & Hbb).
assert (HPL1 : garr8 ubs0segs mem1 pdata PAYLOAD).
{ eapply (garr8_frame ubs0segs); [exact HPL|]. intros a Ha. rewrite HPLn in Ha.
replace a with (pdata + (a - pdata)) by lia. apply (Hbb pdata nb); [exact Hpd | lia]. }
pose proof (cs_hdr_val_range memc pdata nb cur 16) as V0. pose proof (cs_hdr_val_range memc pdata nb cur 17) as V1.
pose proof (cs_hdr_val_range memc pdata nb cur 20) as V2. pose proof (cs_hdr_val_range memc pdata nb cur 21) as V3.
pose proof (cs_hdr_val_range memc pdata nb cur 24) as V4. pose proof (cs_hdr_val_range memc pdata nb cur 25) as V5.
pose proof (cs_hdr_val_range memc pdata nb cur 28) as V6. pose proof (cs_hdr_val_range memc pdata nb cur 26) as V7.
pose proof (cs_hdr_val_range memc pdata nb cur 27) as V8.
assert (Hhb : hdr_bytes mem1 dst (hdr_val memc pdata nb cur 16) (hdr_val memc pdata nb cur 17) (hdr_val memc pdata nb cur 20)
(hdr_val memc pdata nb cur 21) (hdr_val memc pdata nb cur 24) (hdr_val memc pdata nb cur 25) (hdr_val memc pdata nb cur 28)
(hdr_val memc pdata nb cur 26) (hdr_val memc pdata nb cur 27)).
{ unfold hdr_bytes. repeat split; first [apply HDB; lia | rewrite HDB by lia; reflexivity]. }
assert (HBok : bytes_ok [hdr_val memc pdata nb cur 16; hdr_val memc pdata nb cur 17; hdr_val memc pdata nb cur 20;
hdr_val memc pdata nb cur 21; hdr_val memc pdata nb cur 24; hdr_val memc pdata nb cur 25; hdr_val memc pdata nb cur 28;
hdr_val memc pdata nb cur 26; hdr_val memc pdata nb cur 27]).
{ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; apply cs_hdr_val_range. }
assert (HRI : hdr_rv nb cur 9 = 0 -> hdr_cur nb cur 9 = cur + 9 /\ cur + 9 <= nb /\
hdr_val memc pdata nb cur 16 = byte_at memc (pdata + cur) /\ hdr_val memc pdata nb cur 17 = byte_at memc (pdata + cur + 1) /\
hdr_val memc pdata nb cur 20 = byte_at memc (pdata + cur + 2) /\ hdr_val memc pdata nb cur 21 = byte_at memc (pdata + cur + 3) /\
hdr_val memc pdata nb cur 24 = byte_at memc (pdata + cur + 4) /\ hdr_val memc pdata nb cur 25 = byte_at memc (pdata + cur + 5) /\
hdr_val memc pdata nb cur 28 = byte_at memc (pdata + cur + 6) /\ hdr_val memc pdata nb cur 26 = byte_at memc (pdata + cur + 7) /\
hdr_val memc pdata nb cur 27 = byte_at memc (pdata + cur + 8)).
{ intros Hz. destruct (Hr0 Hz) as [Hle Hc9]. split; [exact Hc9|]. split; [exact Hle|].
split. { rewrite <- (Z.add_0_r (pdata + cur)). eapply cs_hdr_val_at; [reflexivity | lia | lia]. }
repeat split; (eapply cs_hdr_val_at; [reflexivity | lia | lia]). }
assert (HV26 : val_mem ubs0segs mem1 (dst + 26) 2 (hdr_val memc pdata nb cur 26 + 256 * hdr_val memc pdata nb cur 27)).
{ apply val_mem_2_bytes; [apply cs_hdr_val_range | apply cs_hdr_val_range | apply HDB; lia |].
replace (dst + 26 + 1) with (dst + 27) by lia. apply HDB. lia. }
unfold hdr_pc.
destruct (Z.land (hdr_val memc pdata nb cur 16) 1 =? 0) eqn:Hodd.
- apply Z.eqb_eq in Hodd.
assert (HW0 : word_mem ubs0segs mem1 dst 0).
{ intros k Hk. rewrite HDB by lia. do 8 (destruct k as [|k]; [reflexivity|]). lia. }
eapply SR_mono.
{ eapply (rfc_img_x API IMG (hdr_rv nb cur 9) Hrv STK sp0 FP L A mem md Lc Ac mdc regs regs1 mem1 Bb [] st dst N pdata nb
(hdr_cur nb cur 9) 0 0 PAYLOAD bq).
all: first [assumption | exact HBc | (left; split; reflexivity) | lia]. }
cbv beta. intros c' HP.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur (hdr_cur nb cur 9) (hdr_rv nb cur 9) memc mem1
(hdr_val memc pdata nb cur 16) (hdr_val memc pdata nb cur 17) (hdr_val memc pdata nb cur 20) (hdr_val memc pdata nb cur 21)
(hdr_val memc pdata nb cur 24) (hdr_val memc pdata nb cur 25) (hdr_val memc pdata nb cur 28) (hdr_val memc pdata nb cur 26)
(hdr_val memc pdata nb cur 27) PAYLOAD bq c' HP).
all: first [assumption | lia | (intros _; split; [exact Hodd | exact Hhb])].
- apply Z.eqb_neq in Hodd.
eapply SR_mono.
{ eapply (rfc_pal_x API IMG (hdr_rv nb cur 9) Hrv STK sp0 FP L A mem md Lc Ac mdc regs regs1 mem1 Bb st dst N pdata nb
(hdr_cur nb cur 9) (3 * (hdr_val memc pdata nb cur 26 + 256 * hdr_val memc pdata nb cur 27))
(hdr_val memc pdata nb cur 26 + 256 * hdr_val memc pdata nb cur 27) PAYLOAD bq).
all: first [assumption | reflexivity | lia]. }
cbv beta. intros c' HP.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur (hdr_cur nb cur 9) (hdr_rv nb cur 9) memc mem1
(hdr_val memc pdata nb cur 16) (hdr_val memc pdata nb cur 17) (hdr_val memc pdata nb cur 20) (hdr_val memc pdata nb cur 21)
(hdr_val memc pdata nb cur 24) (hdr_val memc pdata nb cur 25) (hdr_val memc pdata nb cur 28) (hdr_val memc pdata nb cur 26)
(hdr_val memc pdata nb cur 27) PAYLOAD bq c' HP).
all: first [assumption | lia | (intros _; exact Hhb)].
Qed.
Lemma rfc_case_weaken : forall C : Z -> Prop, rfc_case_x MR (fun _ => True) -> rfc_case_x MR C.
Proof using.
intros C H STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD b _.
exact (H STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD b I).
Qed.
Lemma rfc_caseX_5 : rfc_case_x MR (fun av => 9 <= av).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Lemma rfc_caseX_4 : rfc_case_x MR (fun av => 7 <= av < 9).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Lemma rfc_caseX_3 : rfc_case_x MR (fun av => 6 <= av < 7).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Lemma rfc_caseX_2 : rfc_case_x MR (fun av => 4 <= av < 6).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Lemma rfc_caseX_1 : rfc_case_x MR (fun av => 2 <= av < 4).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Lemma rfc_caseX_0 : rfc_case_x MR (fun av => av < 2).
Proof using IMG LAWS. exact (rfc_case_weaken _ rfc_case_all). Qed.
Theorem ubs0_read_frameconfig_x : rfc_specX API.
Proof using IMG.
apply rfc_specX_of_cases; [apply rfc_caseX_0 | apply rfc_caseX_1 | apply rfc_caseX_2 | apply rfc_caseX_3 | apply rfc_caseX_4 | apply rfc_caseX_5].
Qed.
End S.
End g.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
