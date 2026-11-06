(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e
YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3b YI06 YI5b YI09 YI08 YI0r YI1w YI5o YI21 YI5l
YI00 YI05 YI5a YI5f YI56 YI57 YI23 YI59.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition HDRZ : Z := Eval vm_compute in (src0_A_read_frameconfig + 0x38).
Definition BNEZ : Z := Eval vm_compute in (src0_A_read_frameconfig + 0x18c).
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
region_ok src0segs E mem (YP09.mkRegion (Some n) 0 (Z.of_nat cnt) 0 0 (byte_chunks k0 cnt)).
Proof.
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
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom src0segs)) md2 /\
journal src0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
mbyte src0segs mem2 a = mbyte src0segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs mem2 (b + i) = mbyte src0segs memc (b + i)) /\
word_mem src0segs mem2 st pdata /\ word_mem src0segs mem2 (st + 8) nb /\
word_mem src0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ fst (fst (parse_frameN N (skipn (Z.to_nat cur) PAYLOAD))) = false /\
(exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) /\ res_ok A2 (rfc_rb_fail b)) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx (LPAL IMG : list Z),
obj_at src0segs mem2 dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (blocks L2 A2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
parse_frameN N (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr, fgen, delay, tidx, nlp, LPAL, IMG), skipn (Z.to_nat cur2) PAYLOAD) /\
garr8 src0segs mem2 img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 src0segs mem2 lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp) /\
res_ok A2 (rfc_rb_ok b fattr nlp N))).
Definition rfc_case_x (MR : MR_t) (C : Z -> Prop) : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (PAYLOAD : list Z) (b : rbound),
C (nb - cur) ->
journal src0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp src0_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
word_mem src0segs memc st pdata -> word_mem src0segs memc (st + 8) nb -> word_mem src0segs memc (st + 16) cur ->
garr8 src0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
res_ok Ac b -> rfc_room b N ->
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_read_frameconfig) memc (seg_rom src0segs)) mdc)
(rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD b).
Lemma rfc_specX_of_cases : forall API,
rfc_case_x (aa_MR API) (fun av => av < 2) -> rfc_case_x (aa_MR API) (fun av => 2 <= av < 4) ->
rfc_case_x (aa_MR API) (fun av => 4 <= av < 6) -> rfc_case_x (aa_MR API) (fun av => 6 <= av < 7) ->
rfc_case_x (aa_MR API) (fun av => 7 <= av < 9) -> rfc_case_x (aa_MR API) (fun av => 9 <= av) ->
rfc_specX API.
Proof.
intros API C0 C1 C2 C3 C4 C5. unfold rfc_specX. intros until b. intros HJ.
destruct (Z_lt_le_dec (nb - cur) 2) as [H|H]; [revert HJ; apply C0; exact H|].
destruct (Z_lt_le_dec (nb - cur) 4) as [H1|H1]; [revert HJ; apply C1; lia|].
destruct (Z_lt_le_dec (nb - cur) 6) as [H2|H2]; [revert HJ; apply C2; lia|].
destruct (Z_lt_le_dec (nb - cur) 7) as [H3|H3]; [revert HJ; apply C3; lia|].
destruct (Z_lt_le_dec (nb - cur) 9) as [H4|H4]; [revert HJ; apply C4; lia|].
revert HJ; apply C5; lia.
Qed.
Lemma word_mem_mod : forall m a v, word_mem src0segs m a v -> word_mem src0segs m a (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. unfold le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma Z_to_bv64_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma val_mem_2_bytes : forall m a b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
mbyte src0segs m a = Some (Z_to_bv 8 b0) -> mbyte src0segs m (a + 1) = Some (Z_to_bv 8 b1) ->
val_mem src0segs m a 2 (b0 + 256 * b1).
Proof.
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
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Definition hdr_bytes (m : word -> option byte) (dst b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) : Prop :=
mbyte src0segs m (dst + 16) = Some (Z_to_bv 8 b0) /\ mbyte src0segs m (dst + 17) = Some (Z_to_bv 8 b1) /\
mbyte src0segs m (dst + 18) = Some (Z_to_bv 8 0) /\ mbyte src0segs m (dst + 19) = Some (Z_to_bv 8 0) /\
mbyte src0segs m (dst + 20) = Some (Z_to_bv 8 b2) /\ mbyte src0segs m (dst + 21) = Some (Z_to_bv 8 b3) /\
mbyte src0segs m (dst + 22) = Some (Z_to_bv 8 0) /\ mbyte src0segs m (dst + 23) = Some (Z_to_bv 8 0) /\
mbyte src0segs m (dst + 24) = Some (Z_to_bv 8 b4) /\ mbyte src0segs m (dst + 25) = Some (Z_to_bv 8 b5) /\
mbyte src0segs m (dst + 26) = Some (Z_to_bv 8 b7) /\ mbyte src0segs m (dst + 27) = Some (Z_to_bv 8 b8) /\
mbyte src0segs m (dst + 28) = Some (Z_to_bv 8 b6).
Lemma hdr_bytes_frame : forall m m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8,
hdr_bytes m dst b0 b1 b2 b3 b4 b5 b6 b7 b8 ->
(forall i, 16 <= i < 29 -> mbyte src0segs m' (dst + i) = mbyte src0segs m (dst + i)) ->
hdr_bytes m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8.
Proof.
intros m m' dst b0 b1 b2 b3 b4 b5 b6 b7 b8 H Hf. unfold hdr_bytes in *.
rewrite !Hf by lia. exact H.
Qed.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Lemma rfc_fail_of_img : forall b N, 0 <= N -> rb_le (rb_free (rb_malloc b N) N) (rfc_rb_fail b).
Proof.
intros b N HN. unfold rfc_rb_fail. apply (rb_le_trans _ (rb_acc b 1 0)); [apply rb_free_malloc_acc; lia|].
apply rb_acc_mono; [apply rb_le_refl | lia | lia].
Qed.
Lemma rfc_room_N : forall b N, rfc_room b N -> 0 <= N -> room b N.
Proof.
intros b N HR HN. apply (room_mono b (rb_acc b 1 PALSLACK) N (Z.max N PALMAX)); [apply rb_acc_le; unfold PALSLACK; lia | lia | exact HR].
Qed.
Lemma rx_garr8_byte_at : forall m q (P : list Z) j, garr8 src0segs m q P -> (j < length P)%nat -> nth j P 0 = byte_at m (q + Z.of_nat j).
Proof.
intros m q P j H Hj. unfold byte_at. rewrite (garr8_mbyte _ m q P j H Hj). rewrite Z_to_bv_unsigned.
pose proof (proj2 (H j Hj)) as Rg. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma hdr_at_of_garr8 : forall memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8,
garr8 src0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur -> cur + 9 <= nb ->
b0 = byte_at memc (pdata + cur) -> b1 = byte_at memc (pdata + cur + 1) -> b2 = byte_at memc (pdata + cur + 2) ->
b3 = byte_at memc (pdata + cur + 3) -> b4 = byte_at memc (pdata + cur + 4) -> b5 = byte_at memc (pdata + cur + 5) ->
b6 = byte_at memc (pdata + cur + 6) -> b7 = byte_at memc (pdata + cur + 7) -> b8 = byte_at memc (pdata + cur + 8) ->
hdr_at PAYLOAD cur b0 b1 b2 b3 b4 b5 b6 b7 b8.
Proof.
intros memc pdata PAYLOAD nb cur b0 b1 b2 b3 b4 b5 b6 b7 b8 HPL HPLn Hcur Hle -> -> -> -> -> -> -> -> ->.
unfold hdr_at. repeat split; (rewrite (rx_garr8_byte_at memc pdata PAYLOAD) by (exact HPL || lia); f_equal; lia).
Qed.
Lemma post_of_pal_x : forall (regs : bvmap 5 word) STK sp0 FP L A mem md (Bb : list (Z * Z)) (st dst N pdata nb cur cur1 r : Z)
(memc mem1 : word -> option byte) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Z) (PAYLOAD : list Z) (bq : rbound) c',
pal_post_x API regs STK sp0 FP L A mem md Bb st dst N nb cur1 (3 * (b7 + 256 * b8)) r mem1 pdata PAYLOAD bq c' ->
alloc_ceiling + RFC_STK <= spZ regs -> spZ regs <= st -> spZ regs <= dst -> (st + 24 <= dst \/ dst + 32 <= st) ->
dst + 32 <= 2 ^ 63 -> st + 24 <= 2 ^ 63 -> 0 <= pdata < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_FRAME <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte src0segs mem1 a = mbyte src0segs memc a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs mem1 (b + i) = mbyte src0segs memc (b + i)) ->
word_mem src0segs memc st pdata -> word_mem src0segs memc (st + 8) nb -> cur <= cur1 -> 1 <= N ->
Z.land b0 1 <> 0 ->
(r = 0 -> hdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 b6 b7 b8) ->
bytes_ok [b0; b1; b2; b3; b4; b5; b6; b7; b8] ->
garr8 src0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur ->
(r = 0 -> cur1 = cur + 9 /\ cur + 9 <= nb /\
b0 = byte_at memc (pdata + cur) /\ b1 = byte_at memc (pdata + cur + 1) /\ b2 = byte_at memc (pdata + cur + 2) /\
b3 = byte_at memc (pdata + cur + 3) /\ b4 = byte_at memc (pdata + cur + 4) /\ b5 = byte_at memc (pdata + cur + 5) /\
b6 = byte_at memc (pdata + cur + 6) /\ b7 = byte_at memc (pdata + cur + 7) /\ b8 = byte_at memc (pdata + cur + 8)) ->
(r <> 0 -> nb < cur + 9) ->
rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD bq c'.
Proof.
intros regs STK sp0 FP L A mem md Bb st dst N pdata nb cur cur1 r memc mem1 b0 b1 b2 b3 b4 b5 b6 b7 b8 PAYLOAD bq c'
HP Hsp Hst1 Hdst1 Hsd Hdst2 Hst2 Hpd Hnb Hfr1 Hbb1 Wp Wn Hcc HN Hodd Hhb HB HPL HPLn Hcur0 Hr9 Hn9.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFRv : RFC_FRAME = 48) by reflexivity.
assert (HDPv : RFC_DEPTH = 8240) by reflexivity. assert (HSTKv : RFC_STK = 8272) by reflexivity.
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & lp & lpb & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|].
assert (Hm : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte src0segs mem2 a = mbyte src0segs memc a).
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
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_FRAME <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte src0segs mem1 a = mbyte src0segs memc a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src0segs mem1 (b + i) = mbyte src0segs memc (b + i)) ->
word_mem src0segs memc st pdata -> word_mem src0segs memc (st + 8) nb -> cur <= cur1 -> 1 <= N ->
(r = 0 -> Z.land b0 1 = 0 /\ hdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 b6 b7 b8) ->
bytes_ok [b0; b1; b2; b3; b4; b5; b6; b7; b8] ->
garr8 src0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb -> 0 <= cur ->
(r = 0 -> cur1 = cur + 9 /\ cur + 9 <= nb /\
b0 = byte_at memc (pdata + cur) /\ b1 = byte_at memc (pdata + cur + 1) /\ b2 = byte_at memc (pdata + cur + 2) /\
b3 = byte_at memc (pdata + cur + 3) /\ b4 = byte_at memc (pdata + cur + 4) /\ b5 = byte_at memc (pdata + cur + 5) /\
b6 = byte_at memc (pdata + cur + 6) /\ b7 = byte_at memc (pdata + cur + 7) /\ b8 = byte_at memc (pdata + cur + 8)) ->
(r <> 0 -> nb < cur + 9) ->
rfc_post_x MR regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc PAYLOAD bq c'.
Proof.
intros regs STK sp0 FP L A mem md Bb st dst N pdata nb cur cur1 r memc mem1 b0 b1 b2 b3 b4 b5 b6 b7 b8 PAYLOAD bq c'
HP Hsp Hst1 Hdst1 Hsd Hdst2 Hst2 Hpd Hnb Hfr1 Hbb1 Wp Wn Hcc HN Hhb HB HPL HPLn Hcur0 Hr9 Hn9.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFRv : RFC_FRAME = 48) by reflexivity.
assert (HDPv : RFC_DEPTH = 8240) by reflexivity. assert (HSTKv : RFC_STK = 8272) by reflexivity.
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|].
assert (Hm : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) ->
~ (st + 16 <= a < st + 24) -> mbyte src0segs mem2 a = mbyte src0segs memc a).
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
Lemma rfc_caseX_5 : rfc_case_x MR (fun av => 9 <= av).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 5) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ apply (region_ok_bytes _ memc 35 P 9 36); [rewrite HX35; apply unsigned_lit_small; lia | lia | lia |].
intros j Hj. split; [apply HB; exact Hj|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
jrun LAWS src0tbl_ok HS HJ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Heven : Z.land (byte_at memc P) 1 = 0) by (apply Z.eqb_eq; exact Hc).
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 0 (or_introl eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb (cur + 9) 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 34 9) st (cur + 9) HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite HX34, unsigned_lit_small by lia; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 16 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur (cur + 9) 0 memc _
(byte_at memc P) (byte_at memc (P + 1)) (byte_at memc (P + 2)) (byte_at memc (P + 3)) (byte_at memc (P + 4))
(byte_at memc (P + 5)) (byte_at memc (P + 6)) (byte_at memc (P + 7)) (byte_at memc (P + 8)) PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros _. split; [exact Heven|]. unfold hdr_bytes. cbn [ms_mem mkst].
repeat split;
first [ dst_byte HS HU11 36%nat HB0 | dst_byte HS HU11 37%nat HB1 | dst_byte HS HU11 38%nat HB2
| dst_byte HS HU11 39%nat HB3 | dst_byte HS HU11 40%nat HB4 | dst_byte HS HU11 41%nat HB5
| dst_byte HS HU11 42%nat HB6 | dst_byte HS HU11 43%nat HB7 | dst_byte HS HU11 44%nat HB8
| dst_zero HS HU11 18 2 | dst_zero HS HU11 22 2 ].
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; apply byte_at_range.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Hodd : Z.land (byte_at memc P) 1 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc).
jrun_to LAWS src0tbl_ok HS HJ PALPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_pal_x API IMG 0 (or_introl eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb (cur + 9)
(3 * (byte_at memc (P + 7) + 256 * byte_at memc (P + 8))) (byte_at memc (P + 7) + 256 * byte_at memc (P + 8)) PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - lia. - reflexivity. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
let T := fresh "T" in pose proof (st_ok_reg src0segs Ec ssc msc 10%bv HS) as T; eval_sr_get_in T;
rewrite (denot_pal3 _ 44 43 _ _ HB8 HB7) in T by lia; exact T end.
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 34 9) st (cur + 9) HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite HX34, unsigned_lit_small by lia; reflexivity | lia].
-
first [ apply val_mem_2_bytes; [lia | lia | dst_byte HS HU11 43%nat HB7 | replace (dst + 26 + 1) with (dst + 27) by lia; dst_byte HS HU11 44%nat HB8]
| apply (val_mem_2_bytes _ _ 0 0); [lia | lia | |]; [ | replace (dst + 26 + 1) with (dst + 27) by lia];
first [solve [dst_zero HS HU11 26 2] | solve [dst_zero HS HU11 26 6] | solve [dst_zero HS HU11 22 10] | solve [dst_zero HS HU11 18 14]] ].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- exact HRm. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur (cur + 9) 0 memc _
(byte_at memc P) (byte_at memc (P + 1)) (byte_at memc (P + 2)) (byte_at memc (P + 3)) (byte_at memc (P + 4))
(byte_at memc (P + 5)) (byte_at memc (P + 6)) (byte_at memc (P + 7)) (byte_at memc (P + 8)) PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | exact Hodd | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros _. unfold hdr_bytes. cbn [ms_mem mkst].
repeat split;
first [ dst_byte HS HU11 36%nat HB0 | dst_byte HS HU11 37%nat HB1 | dst_byte HS HU11 38%nat HB2
| dst_byte HS HU11 39%nat HB3 | dst_byte HS HU11 40%nat HB4 | dst_byte HS HU11 41%nat HB5
| dst_byte HS HU11 42%nat HB6 | dst_byte HS HU11 43%nat HB7 | dst_byte HS HU11 44%nat HB8
| dst_zero HS HU11 18 2 | dst_zero HS HU11 22 2 ].
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; apply byte_at_range.
Qed.
Lemma rfc_caseX_4 : rfc_case_x MR (fun av => 7 <= av < 9).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 4) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ apply (region_ok_bytes _ memc 35 P 7 36); [rewrite HX35; apply unsigned_lit_small; lia | lia | lia |].
intros j Hj. split; [apply HB; lia|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
jrun LAWS src0tbl_ok HS HJ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Heven : Z.land (byte_at memc P) 1 = 0) by (apply Z.eqb_eq; exact Hc).
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb nb 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 16 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Hodd : Z.land (byte_at memc P) 1 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc).
jrun_to LAWS src0tbl_ok HS HJ PALPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_pal_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb nb
(3 * (0 + 256 * 0)) (0 + 256 * 0) PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - lia. - reflexivity. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
-
first [ apply val_mem_2_bytes; [lia | lia | dst_byte HS HU11 43%nat HB7 | replace (dst + 26 + 1) with (dst + 27) by lia; dst_byte HS HU11 44%nat HB8]
| apply (val_mem_2_bytes _ _ 0 0); [lia | lia | |]; [ | replace (dst + 26 + 1) with (dst + 27) by lia];
first [solve [dst_zero HS HU11 26 2] | solve [dst_zero HS HU11 26 6] | solve [dst_zero HS HU11 22 10] | solve [dst_zero HS HU11 18 14]] ].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- exact HRm. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | exact Hodd | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
Qed.
Lemma rfc_caseX_3 : rfc_case_x MR (fun av => 6 <= av < 7).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 3) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ apply (region_ok_bytes _ memc 35 P 6 36); [rewrite HX35; apply unsigned_lit_small; lia | lia | lia |].
intros j Hj. split; [apply HB; lia|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
jrun LAWS src0tbl_ok HS HJ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Heven : Z.land (byte_at memc P) 1 = 0) by (apply Z.eqb_eq; exact Hc).
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb nb 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 16 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Hodd : Z.land (byte_at memc P) 1 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc).
jrun_to LAWS src0tbl_ok HS HJ PALPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_pal_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb nb
(3 * (0 + 256 * 0)) (0 + 256 * 0) PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - lia. - reflexivity. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
-
first [ apply val_mem_2_bytes; [lia | lia | dst_byte HS HU11 43%nat HB7 | replace (dst + 26 + 1) with (dst + 27) by lia; dst_byte HS HU11 44%nat HB8]
| apply (val_mem_2_bytes _ _ 0 0); [lia | lia | |]; [ | replace (dst + 26 + 1) with (dst + 27) by lia];
first [solve [dst_zero HS HU11 26 2] | solve [dst_zero HS HU11 26 6] | solve [dst_zero HS HU11 22 10] | solve [dst_zero HS HU11 18 14]] ].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- exact HRm. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | exact Hodd | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
Qed.
Lemma rfc_caseX_2 : rfc_case_x MR (fun av => 4 <= av < 6).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 2) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ apply (region_ok_bytes _ memc 35 P 4 36); [rewrite HX35; apply unsigned_lit_small; lia | lia | lia |].
intros j Hj. split; [apply HB; lia|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
jrun LAWS src0tbl_ok HS HJ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Heven : Z.land (byte_at memc P) 1 = 0) by (apply Z.eqb_eq; exact Hc).
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb nb 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 16 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Hodd : Z.land (byte_at memc P) 1 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc).
jrun_to LAWS src0tbl_ok HS HJ PALPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_pal_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb nb
(3 * (0 + 256 * 0)) (0 + 256 * 0) PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - lia. - reflexivity. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
-
first [ apply val_mem_2_bytes; [lia | lia | dst_byte HS HU11 43%nat HB7 | replace (dst + 26 + 1) with (dst + 27) by lia; dst_byte HS HU11 44%nat HB8]
| apply (val_mem_2_bytes _ _ 0 0); [lia | lia | |]; [ | replace (dst + 26 + 1) with (dst + 27) by lia];
first [solve [dst_zero HS HU11 26 2] | solve [dst_zero HS HU11 26 6] | solve [dst_zero HS HU11 22 10] | solve [dst_zero HS HU11 18 14]] ].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- exact HRm. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | exact Hodd | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
Qed.
Lemma rfc_caseX_1 : rfc_case_x MR (fun av => 2 <= av < 4).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 1) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ apply (region_ok_bytes _ memc 35 P 2 36); [rewrite HX35; apply unsigned_lit_small; lia | lia | lia |].
intros j Hj. split; [apply HB; lia|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
jrun LAWS src0tbl_ok HS HJ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jbranch src0tbl HS.
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Heven : Z.land (byte_at memc P) 1 = 0) by (apply Z.eqb_eq; exact Hc).
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb nb 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 16 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
-
rewrite branch_eq_U, (U_and1_byte _ 36 _ HB0), U_lit in Hc by lia.
assert (Hodd : Z.land (byte_at memc P) 1 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc).
jrun_to LAWS src0tbl_ok HS HJ PALPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_pal_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb nb
(3 * (0 + 256 * 0)) (0 + 256 * 0) PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - lia. - reflexivity. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
-
first [ apply val_mem_2_bytes; [lia | lia | dst_byte HS HU11 43%nat HB7 | replace (dst + 26 + 1) with (dst + 27) by lia; dst_byte HS HU11 44%nat HB8]
| apply (val_mem_2_bytes _ _ 0 0); [lia | lia | |]; [ | replace (dst + 26 + 1) with (dst + 27) by lia];
first [solve [dst_zero HS HU11 26 2] | solve [dst_zero HS HU11 26 6] | solve [dst_zero HS HU11 22 10] | solve [dst_zero HS HU11 18 14]] ].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- exact HRm. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_pal_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | exact Hodd | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
Qed.
Lemma rfc_caseX_0 : rfc_case_x MR (fun av => av < 2).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur PAYLOAD bq
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc HPL HPLn HRq HRm.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RFC_FRAME = 48) by reflexivity. assert (HDPv : RFC_DEPTH = 8240) by reflexivity.
assert (HSTKv : RFC_STK = 8272) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3);
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6); byte_at memc (P + 7); byte_at memc (P + 8)]).
set (E := Ereg regs (map (Z_to_bv 64) xvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error xvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; lia).
assert (HX32 : ew E 32 = Z_to_bv 64 pdata) by (apply (HX 0%nat); reflexivity).
assert (HX33 : ew E 33 = Z_to_bv 64 nb) by (apply (HX 1%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 cur) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 P) by (apply (HX 3%nat); reflexivity).
assert (HB : forall j, (j < 9)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 9 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 9)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src0segs E (ss_hdr 0) (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))).
{ unfold ss_hdr. replace src0_A_read_frameconfig with RFC by reflexivity. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [hdr_breg hdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack src0segs _ memc 2 sp); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | lia | cbn; lia | apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- cbn [hdr_breg hdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms byte_facts map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6. pose proof (HBr 7%nat ltac:(lia)) as B7. pose proof (HBr 8%nat ltac:(lia)) as B8.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6, B7, B8.
repeat split; try lia; assumption.
+ cbn [f_conds hdr_conds hdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RFC) memc (seg_rom src0segs))) in HJ.
jrun_to LAWS src0tbl_ok HS HJ HDRZ. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 32)).
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB7 : ew E 43 = Z_to_bv 64 (byte_at memc (P + 7))) by (apply (HB 7%nat); lia).
assert (HB8 : ew E 44 = Z_to_bv 64 (byte_at memc (P + 8))) by (apply (HB 8%nat); lia).
pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 7)) as R7. pose proof (byte_at_range memc (P + 8)) as R8.
jrun_to LAWS src0tbl_ok HS HJ IMGPC. { wr4_tac HU2 HU10 HU11 ltac:(lia). }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img_x API IMG 18446744073709551615 (or_intror eq_refl) STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb [] st dst N pdata nb nb 0 0 PAYLOAD bq) end.
- exact HJ. - exact Hid. - exact Hbase. - exact HBc. - exact Hpd. - left; split; reflexivity. - lia. - exact Hra0. - exact Htp0. - exact Hal16.
- lia. - lia. - exact Hst1. - exact Hst2. - exact Hdst1. - exact Hdst2. - exact Hsd. - exact Hst8. - exact Hdst8. - exact H63.
- exact HN. - lia. - exact Hnb.
- reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
- reg_nowF HS ltac:(rewrite HU11; reflexivity).
- reg_nowF HS ltac:(rewrite HU10; reflexivity).
- reg_nowF HS ltac:(rewrite HU12; reflexivity).
- reg_nowF HS ltac:(reflexivity).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 21%nat 21%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
- frame_wordE HS HU2 HE 1%nat (1%bv:reg).
- frame_wordE HS HU2 HE 8%nat (8%bv:reg).
- frame_wordE HS HU2 HE 9%nat (9%bv:reg).
- frame_wordE HS HU2 HE 18%nat (18%bv:reg).
- frame_wordE HS HU2 HE 19%nat (19%bv:reg).
- frame_wordE HS HU2 HE 20%nat (20%bv:reg).
- rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU10 | cbn [sv_denot]; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
- rewrite <- (Z.add_0_r dst).
eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 32 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | exact HU11 | lia | lia].
- cbn [ms_mem mkst]; eapply (garr8_frame src0segs); [exact HPL|]; intros a Ha; rewrite HPLn in Ha; hdr_frames HU2 HU10 HU11 ltac:(lia); reflexivity.
- exact HPLn.
- exact HRq.
- apply (rfc_room_N bq N HRm); clear - HN; lia. }
cbv beta. intros c' HP.
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
unfold hideP in Hsd.
eapply (post_of_img_x regs STK sp0 FP L A mem md Bb st dst N pdata nb cur nb 18446744073709551615 memc _
(byte_at memc P) 0 0 0 0 0 0 0 0 PAYLOAD bq c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | lia | | | exact HPL | exact HPLn | clear - Hcur; lia | first [intros HH0; discriminate HH0 | intros _; repeat split; first [reflexivity | clear - HC; lia]] | first [intros HH0; exfalso; apply HH0; reflexivity | intros _; clear - HC Hcur; lia] ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
hdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros Hr. exfalso. clear - Hr. lia.
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; first [apply byte_at_range | lia].
Qed.
Theorem src0_read_frameconfig_x : rfc_specX API.
Proof.
apply rfc_specX_of_cases; [apply rfc_caseX_0 | apply rfc_caseX_1 | apply rfc_caseX_2 | apply rfc_caseX_3 | apply rfc_caseX_4 | apply rfc_caseX_5].
Qed.
End S.
End g.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
