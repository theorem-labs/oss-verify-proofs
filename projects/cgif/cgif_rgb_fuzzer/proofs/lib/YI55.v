(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO3m YI00 YI02 YI01 YI03
YI1e YI1i YI59 YI56 YI0x YL0e YI08 YI0c YI3h
YI4y YI54 YO0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac rframe_wordE HS HU2 HE n rr :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (- dd) (SOff n 0) spv (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 20
| ew_havocF; exact HU2
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Ltac rdst_byte HS HU11 n HBj :=
eapply (st_chunk_byte _ _ _ 2%nat _ 11%nat _ (SOff n 0) _ _ HS);
[ reflexivity | reflexivity | cbv; auto 30 | ew_havocF; exact HU11
| cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HBj, Z_to_bv_bv_unsigned; reflexivity
| apply byte_at_range ].
Ltac rdst_zero HS HU11 off len :=
lazymatch goal with |- mbyte _ _ (?d + ?c) = _ =>
replace (d + c) with (d + off + (c - off)) by lia;
eapply (st_chunk_zero _ _ _ 2%nat _ 11%nat off len d (c - off) HS);
[ reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia ]
end.
Ltac rhdr_frames HU2 HU10 HU11 slv :=
repeat match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(rewrite ?HU2, ?HU10, ?HU11; slv)
end.
Ltac rhdr_fin HS HJ Hid HE Hra0 cur2 :=
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in
pose proof (st_ok_reg src2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (HE 1%nat 1%bv eq_refl) in Q1;
lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdl] =>
eexists _, _, rg, mm, mdl end;
exists (2 ^ 64 - 1), cur2;
split; [ cbn [ms_regs mkst]; rewrite Q1, Hra0; reflexivity |];
split; [ exact HJ |];
split; [ exact Hid |];
split; [ apply regs_preserved_intro; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity) |];
split; [ pose proof (st_ok_reg src2segs Ef ssf msf 10%bv HS) as Q10; eval_sr_get_in Q10; cbn [sv_denot] in Q10; cbn [ms_regs mkst]; rewrite Q10; reflexivity |];
split; [ lia |];
split; [| split; [| split; [| split; [| split; [| split ]]]]]
end.
Ltac rdst_zero_any HS HU11 :=
first [ rdst_zero HS HU11 0 24 | rdst_zero HS HU11 0 12 | rdst_zero HS HU11 14 10 | rdst_zero HS HU11 14 2
| rdst_zero HS HU11 18 6 | rdst_zero HS HU11 18 2 | rdst_zero HS HU11 22 2 ].
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RHDRZ : Z := Eval vm_compute in (src2_A_read_frameconfig + 0x38).
Definition rhdr_ends : list Z := [2; 4; 6; 7].
Definition rhdr_conds (k : nat) : list acond :=
map (fun e => mkAC BC_GEU (SOff 33 0) (SOff 34 e)) (firstn k rhdr_ends) ++
match nth_error rhdr_ends k with Some e => [mkAC BC_LTU (SOff 33 0) (SOff 34 e)] | None => [] end.
Definition rhdr_nbytes (k : nat) : nat := nth k [0; 2; 4; 6; 7]%nat 7%nat.
Definition byte_chunks (k0 cnt : nat) : list YQ0b.chunk :=
map (fun i => mkChunk (Z.of_nat i) (CVal 1 (SOff (k0 + i) 0))) (seq 0 cnt).
Definition rhdr_breg (k : nat) : list YQ0b.region :=
match k with O => [] | _ => [YQ0b.mkRegion (Some 35%nat) 0 (Z.of_nat (rhdr_nbytes k)) 0 0 (byte_chunks 36 (rhdr_nbytes k))] end.
Definition rbyte_facts (k : nat) : list (nat * afact) := map (fun i => ((36 + i)%nat, mkAF 0 255 0)) (seq 0 (rhdr_nbytes k)).
Definition ss_rhdr (k : nat) : sstate :=
mkSS RRFC sr_atoms
([ YQ0b.mkRegion (Some 2%nat) (-RRFC_FRAME) 0 (-RRFC_FRAME) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 24 16 24 [mkChunk 0 (CVal 8 (SOff 32 0)); mkChunk 8 (CVal 8 (SOff 33 0)); mkChunk 16 (CVal 8 (SOff 34 0))] ;
YQ0b.mkRegion (Some 11%nat) 0 24 0 24 [] ] ++ rhdr_breg k)
None
(mkFacts ([ (2%nat, mkAF (CEIL_MIN + RRFC_STK) (2^63) 4); (10%nat, mkAF CEIL_MIN (2^63) 3);
(11%nat, mkAF CEIL_MIN (2^63) 3); (12%nat, mkAF 1 RGB_NMAX 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 1 CEIL_MAX 0);
(34%nat, mkAF 0 CEIL_MAX 0); (35%nat, mkAF 4096 CEIL_MAX 0) ] ++ rbyte_facts k)
(rhdr_conds k)
[ (SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 35 0) ]).
Lemma region_ok_bytes : forall E mem n P (cnt : nat) k0,
bv_unsigned (ew E n) = P -> 0 <= P -> P + Z.of_nat cnt <= 2 ^ 64 ->
(forall j, (j < cnt)%nat -> ew E (k0 + j)%nat = Z_to_bv 64 (byte_at mem (P + Z.of_nat j)) /\ present mem (P + Z.of_nat j)) ->
region_ok src2segs E mem (YQ0b.mkRegion (Some n) 0 (Z.of_nat cnt) 0 0 (byte_chunks k0 cnt)).
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
Lemma fmt_branch : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
branch_taken BC_GEU (sv_denot E (SOff n (-5))) (sv_denot E (SLit 18446744073709551614)) = fmt_okb b.
Proof.
intros E n b Hn Hb. rewrite branch_geu_U. unfold U. cbn [sv_denot]. rewrite Hn.
rewrite (unsigned_lit_small b) by lia.
rewrite (unsigned_lit_small 18446744073709551614) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold fmt_okb.
destruct (Z_lt_le_dec b 5) as [Hl|Hl].
- replace ((b + -5) mod 2 ^ 64) with (b + -5 + 2 ^ 64).
2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
destruct (Z.eqb_spec b 3) as [->|H3]; [reflexivity|]. destruct (Z.eqb_spec b 4) as [->|H4]; [reflexivity|].
cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia.
destruct (Z.eqb_spec b 3) as [->|H3]; [lia|]. destruct (Z.eqb_spec b 4) as [->|H4]; [lia|].
cbn [orb]. apply Bool.negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma fmt_okb_true : forall b, fmt_okb b = true -> b = 3 \/ b = 4.
Proof.
intros b H. unfold fmt_okb in H. destruct (Z.eqb_spec b 3); [left; assumption|]. destruct (Z.eqb_spec b 4); [right; assumption|]. discriminate H.
Qed.
Lemma Z_to_bv64_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Section S.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
Definition rhdr_bytes (m : word -> option byte) (dst b0 b1 b2 b3 b4 b5 : Z) : Prop :=
mbyte src2segs m (dst + 12) = Some (Z_to_bv 8 b0) /\ mbyte src2segs m (dst + 13) = Some (Z_to_bv 8 b1) /\
mbyte src2segs m (dst + 14) = Some (Z_to_bv 8 0) /\ mbyte src2segs m (dst + 15) = Some (Z_to_bv 8 0) /\
mbyte src2segs m (dst + 16) = Some (Z_to_bv 8 b2) /\ mbyte src2segs m (dst + 17) = Some (Z_to_bv 8 b3) /\
mbyte src2segs m (dst + 18) = Some (Z_to_bv 8 0) /\ mbyte src2segs m (dst + 19) = Some (Z_to_bv 8 0) /\
mbyte src2segs m (dst + 20) = Some (Z_to_bv 8 b4) /\ mbyte src2segs m (dst + 21) = Some (Z_to_bv 8 b5) /\
mbyte src2segs m (dst + 22) = Some (Z_to_bv 8 0) /\ mbyte src2segs m (dst + 23) = Some (Z_to_bv 8 0).
Lemma rhdr_bytes_frame : forall m m' dst b0 b1 b2 b3 b4 b5,
rhdr_bytes m dst b0 b1 b2 b3 b4 b5 ->
(forall i, 12 <= i < 24 -> mbyte src2segs m' (dst + i) = mbyte src2segs m (dst + i)) ->
rhdr_bytes m' dst b0 b1 b2 b3 b4 b5.
Proof.
intros m m' dst b0 b1 b2 b3 b4 b5 H Hf. unfold rhdr_bytes in *. rewrite !Hf by lia. exact H.
Qed.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Lemma post_of_rimg : forall (regs : bvmap 5 word) STK sp0 FP L A mem md (Bb : list (Z * Z)) (st dst N pdata nb cur cur1 fmt : Z)
(memc mem1 : word -> option byte) (b0 b1 b2 b3 b4 b5 : Z) c',
rimg_post API regs STK sp0 FP L A mem md Bb st dst N nb cur1 fmt mem1 c' ->
alloc_ceiling + RRFC_STK <= spZ regs -> spZ regs <= st -> spZ regs <= dst -> (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) ->
dst + RGBFC_SIZE <= 2 ^ 63 -> st + 24 <= 2 ^ 63 -> 0 <= pdata < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_FRAME <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) ->
~ (st + 16 <= a < st + 24) -> mbyte src2segs mem1 a = mbyte src2segs memc a) ->
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte src2segs mem1 (b + i) = mbyte src2segs memc (b + i)) ->
word_mem src2segs memc st pdata -> word_mem src2segs memc (st + 8) nb -> cur <= cur1 -> (fmt = 3 \/ fmt = 4) ->
rhdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 ->
bytes_ok [b0; b1; b2; b3; b4; b5] ->
rrfc_post API regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc c'.
Proof.
intros regs STK sp0 FP L A mem md Bb st dst N pdata nb cur cur1 fmt memc mem1 b0 b1 b2 b3 b4 b5 c'
HP Hsp Hst1 Hdst1 Hsd Hdst2 Hst2 Hpd Hnb Hfr1 Hbb1 Wp Wn Hcc Hfmt Hhb HB.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HFRv : RRFC_FRAME = 64) by reflexivity.
assert (HDPv : RRFC_STK = 8256) by reflexivity. assert (HFCv : RGBFC_SIZE = 24) by reflexivity.
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hres & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|]. split; [lia|].
assert (Hm : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) ->
~ (st + 16 <= a < st + 24) -> mbyte src2segs mem2 a = mbyte src2segs memc a).
{ intros a Ha Hn1 Hn2 Hn3. rewrite (Hfr2 a Ha) by lia. apply (Hfr1 a Ha); lia. }
split; [exact Hm|].
split.
{ intros b m i Hb Hi. rewrite (Hbb2 b m i Hb Hi). apply (Hbb1 b m i Hb Hi). }
split.
{ intros k Hk. rewrite (Hm (st + Z.of_nat k)) by lia. apply Wp. exact Hk. }
split.
{ intros k Hk. rewrite (Hm (st + 8 + Z.of_nat k)) by lia. apply Wn. exact Hk. }
split; [exact Wc2|]. split; [lia|].
destruct ALT as [(Hres0 & HB0) | (Hres1 & Wi & Ri & Vf & HB2)]; [left; auto|].
right. split; [lia|].
assert (Hhb2 : rhdr_bytes mem2 dst b0 b1 b2 b3 b4 b5).
{ eapply rhdr_bytes_frame; [exact Hhb|]. intros i Hi. apply Hfr2; lia. }
destruct Hhb2 as (M12 & M13 & M14 & M15 & M16 & M17 & M18 & M19 & M20 & M21 & M22 & M23).
exists img, fmt, (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5).
split.
{ apply rgbfc_obj; try assumption; try lia. }
split. { intros Hf. exfalso. unfold fmt_okb in Hf. destruct Hfmt as [-> | ->]; discriminate Hf. }
split; [exact Ri|].
unfold img_block. replace (fmt_okb fmt) with true by (destruct Hfmt as [-> | ->]; reflexivity). exact HB2.
Qed.
Definition rrfc_case (C : Z -> Prop) : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z),
C (nb - cur) ->
journal src2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp src2_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RRFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + RGBFC_SIZE <= sp0 -> (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= RGB_NMAX -> 0 <= cur <= nb -> 0 < nb ->
word_mem src2segs memc st pdata -> word_mem src2segs memc (st + 8) nb -> word_mem src2segs memc (st + 16) cur ->
SR src2segs (mkCfg (mkst regs (Z_to_bv 64 src2_A_read_frameconfig) memc (seg_rom src2segs)) mdc)
(rrfc_post API regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc).
Lemma rrfc_case_4 : rrfc_case (fun av => 7 <= av).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
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
byte_at memc (P + 4); byte_at memc (P + 5); byte_at memc (P + 6)]).
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
assert (HB : forall j, (j < 7)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 7 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 7)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src2segs E (ss_rhdr 4) (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))).
{ unfold ss_rhdr. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [rhdr_breg rhdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia |].
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
intros j Hj. split; [apply HB; exact Hj|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [rhdr_breg rhdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, HX35, unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms rbyte_facts rhdr_nbytes nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2.
pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
pose proof (HBr 6%nat ltac:(lia)) as B6.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5, B6.
repeat split; try lia; assumption.
+ cbn [f_conds rhdr_conds rhdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))) in HJ.
Ltac wr4 HU2 HU10 HU11 :=
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU10 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU11 | cbn [r_wlo r_whi]; intros _; lia |];
repeat (apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; lia|]); apply wr_ok_nil.
jrun_to LAWS src2tbl_ok HS HJ RHDRZ. { wr4 HU2 HU10 HU11. }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 24)).
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
assert (HB6 : ew E 42 = Z_to_bv 64 (byte_at memc (P + 6))) by (apply (HB 6%nat); lia).
pose proof (byte_at_range memc (P + 6)) as R6.
jbranch src2tbl HS.
-
rewrite (fmt_branch _ 42 _ HB6 R6) in Hc. apply fmt_okb_true in Hc.
jrun_to LAWS src2tbl_ok HS HJ RR_MAL. { wr4 HU2 HU10 HU11. }
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rfc_img API IMG STK sp0 FP L A mem md Lc Ac mdc regs rg mm Bb st dst N pdata nb (cur + 7) (byte_at memc (P + 6))) end.
+ exact HJ. + exact Hid. + exact Hbase. + exact HBc. + exact Hpd. + exact Hra0. + exact Htp0. + exact Hal16.
+ lia. + lia. + exact Hst1. + exact Hst2. + exact Hdst1. + exact Hdst2. + exact Hsd. + exact Hst8. + exact Hdst8. + exact H63.
+ exact HN. + lia. + exact Hnb. + exact Hc.
+ reg_nowF HS ltac:(rewrite HU2, HFRv; f_equal; lia).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 3%nat 3%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 4%nat 4%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite HU11; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact HB6).
+ reg_nowF HS ltac:(rewrite HU12; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 22%nat 22%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 23%nat 23%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 24%nat 24%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 25%nat 25%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 26%nat 26%bv eq_refl)).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply (HE 27%nat 27%bv eq_refl)).
+ rframe_wordE HS HU2 HE 1%nat (1%bv:reg).
+ rframe_wordE HS HU2 HE 8%nat (8%bv:reg).
+ rframe_wordE HS HU2 HE 9%nat (9%bv:reg).
+ rframe_wordE HS HU2 HE 18%nat (18%bv:reg).
+ rframe_wordE HS HU2 HE 19%nat (19%bv:reg).
+ rframe_wordE HS HU2 HE 20%nat (20%bv:reg).
+ rframe_wordE HS HU2 HE 21%nat (21%bv:reg).
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 34 7) st (cur + 7) HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite HX34, unsigned_lit_small by lia; reflexivity | lia]. }
cbv beta. intros c' HP. unfold hideP in Hsd.
eapply (post_of_rimg regs STK sp0 FP L A mem md Bb st dst N pdata nb cur (cur + 7) (byte_at memc (P + 6)) memc _
(byte_at memc P) (byte_at memc (P + 1)) (byte_at memc (P + 2)) (byte_at memc (P + 3)) (byte_at memc (P + 4)) (byte_at memc (P + 5)) c' HP);
[ subst sp; lia | exact Hst1 | exact Hdst1 | exact Hsd | lia | lia | lia | lia | | | exact Wp | exact Wn | lia | exact Hc | | ].
+ intros a Ha Hn1 Hn2 Hn3. cbn [ms_mem mkst] in *. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi. cbn [ms_mem mkst] in *.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ unfold rhdr_bytes. cbn [ms_mem mkst].
repeat split;
first [ rdst_byte HS HU11 36%nat HB0 | rdst_byte HS HU11 37%nat HB1 | rdst_byte HS HU11 38%nat HB2
| rdst_byte HS HU11 39%nat HB3 | rdst_byte HS HU11 40%nat HB4 | rdst_byte HS HU11 41%nat HB5
| rdst_zero HS HU11 14 2 | rdst_zero HS HU11 18 2 | rdst_zero HS HU11 22 2 ].
+ unfold bytes_ok. repeat apply Forall_cons; try apply Forall_nil; apply byte_at_range.
-
rewrite (fmt_branch _ 42 _ HB6 R6) in Hc.
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold hideP in Hsd.
rhdr_fin HS HJ Hid HE Hra0 (cur + 7); cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 34 7) st (cur + 7) HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite HX34, unsigned_lit_small by lia; reflexivity | lia].
+ lia.
+ right. split; [lia|].
exists 0, 0, (byte_at memc P + 256 * byte_at memc (P + 1)), (byte_at memc (P + 2) + 256 * byte_at memc (P + 3)), (byte_at memc (P + 4) + 256 * byte_at memc (P + 5)).
split.
{ pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 1)) as R1. pose proof (byte_at_range memc (P + 2)) as R2.
pose proof (byte_at_range memc (P + 3)) as R3. pose proof (byte_at_range memc (P + 4)) as R4. pose proof (byte_at_range memc (P + 5)) as R5.
apply rgbfc_obj; try assumption; try lia.
- rewrite <- (Z.add_0_r dst). eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 12 dst 0 HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocF; exact HU11 | lia | lia].
- eapply (st_chunk_zero_val src2segs _ _ _ 2%nat _ 11%nat 0 12 dst 8 4%nat HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocF; exact HU11 | lia | cbn; lia].
- rdst_byte HS HU11 36%nat HB0. - rdst_byte HS HU11 37%nat HB1. - rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_byte HS HU11 38%nat HB2. - rdst_byte HS HU11 39%nat HB3. - rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_byte HS HU11 40%nat HB4. - rdst_byte HS HU11 41%nat HB5. }
split; [intros _; reflexivity|]. split; [lia|]. cbn [img_block fmt_okb Z.eqb orb app]. exact HBc.
Qed.
Lemma rrfc_case_3 : rrfc_case (fun av => 6 <= av < 7).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3); byte_at memc (P + 4); byte_at memc (P + 5)]).
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
assert (HB : forall j, (j < 6)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 6 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 6)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src2segs E (ss_rhdr 3) (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))).
{ unfold ss_rhdr. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [rhdr_breg rhdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia |].
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
intros j Hj. split; [apply HB; exact Hj|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [rhdr_breg rhdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, ?HX35, ?unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms rbyte_facts rhdr_nbytes nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3. pose proof (HBr 4%nat ltac:(lia)) as B4. pose proof (HBr 5%nat ltac:(lia)) as B5.
cbn [Nat.add] in B0, B1, B2, B3, B4, B5.
repeat split; try lia; assumption.
+ cbn [f_conds rhdr_conds rhdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ RHDRZ. { wr4 HU2 HU10 HU11. }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 24)).
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
assert (HB4 : ew E 40 = Z_to_bv 64 (byte_at memc (P + 4))) by (apply (HB 4%nat); lia).
assert (HB5 : ew E 41 = Z_to_bv 64 (byte_at memc (P + 5))) by (apply (HB 5%nat); lia).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold hideP in Hsd.
rhdr_fin HS HJ Hid HE Hra0 nb; cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ lia.
+ right. split; [lia|].
exists 0, 0, (byte_at memc P + 256 * byte_at memc (P + 1)), (byte_at memc (P + 2) + 256 * byte_at memc (P + 3)), (byte_at memc (P + 4) + 256 * byte_at memc (P + 5)).
split.
{ pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 1)) as R1. pose proof (byte_at_range memc (P + 2)) as R2. pose proof (byte_at_range memc (P + 3)) as R3. pose proof (byte_at_range memc (P + 4)) as R4. pose proof (byte_at_range memc (P + 5)) as R5.
apply rgbfc_obj; try assumption; try lia.
- rewrite <- (Z.add_0_r dst). eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 _ dst 0 HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | lia].
- eapply (st_chunk_zero_val src2segs _ _ _ 2%nat _ 11%nat 0 _ dst 8 4%nat HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | cbn; lia].
- rdst_byte HS HU11 36%nat HB0.
- rdst_byte HS HU11 37%nat HB1.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_byte HS HU11 38%nat HB2.
- rdst_byte HS HU11 39%nat HB3.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_byte HS HU11 40%nat HB4.
- rdst_byte HS HU11 41%nat HB5.
}
split; [intros _; reflexivity|]. split; [lia|]. cbn [img_block fmt_okb Z.eqb orb app]. exact HBc.
Qed.
Lemma rrfc_case_2 : rrfc_case (fun av => 4 <= av < 6).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1); byte_at memc (P + 2); byte_at memc (P + 3)]).
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
assert (HB : forall j, (j < 4)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 4 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 4)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src2segs E (ss_rhdr 2) (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))).
{ unfold ss_rhdr. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [rhdr_breg rhdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia |].
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
intros j Hj. split; [apply HB; exact Hj|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [rhdr_breg rhdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, ?HX35, ?unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms rbyte_facts rhdr_nbytes nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1. pose proof (HBr 2%nat ltac:(lia)) as B2. pose proof (HBr 3%nat ltac:(lia)) as B3.
cbn [Nat.add] in B0, B1, B2, B3.
repeat split; try lia; assumption.
+ cbn [f_conds rhdr_conds rhdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ RHDRZ. { wr4 HU2 HU10 HU11. }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 24)).
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
assert (HB2 : ew E 38 = Z_to_bv 64 (byte_at memc (P + 2))) by (apply (HB 2%nat); lia).
assert (HB3 : ew E 39 = Z_to_bv 64 (byte_at memc (P + 3))) by (apply (HB 3%nat); lia).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold hideP in Hsd.
rhdr_fin HS HJ Hid HE Hra0 nb; cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ lia.
+ right. split; [lia|].
exists 0, 0, (byte_at memc P + 256 * byte_at memc (P + 1)), (byte_at memc (P + 2) + 256 * byte_at memc (P + 3)), (0 + 256 * 0).
split.
{ pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 1)) as R1. pose proof (byte_at_range memc (P + 2)) as R2. pose proof (byte_at_range memc (P + 3)) as R3.
apply rgbfc_obj; try assumption; try lia.
- rewrite <- (Z.add_0_r dst). eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 _ dst 0 HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | lia].
- eapply (st_chunk_zero_val src2segs _ _ _ 2%nat _ 11%nat 0 _ dst 8 4%nat HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | cbn; lia].
- rdst_byte HS HU11 36%nat HB0.
- rdst_byte HS HU11 37%nat HB1.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_byte HS HU11 38%nat HB2.
- rdst_byte HS HU11 39%nat HB3.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
}
split; [intros _; reflexivity|]. split; [lia|]. cbn [img_block fmt_okb Z.eqb orb app]. exact HBc.
Qed.
Lemma rrfc_case_1 : rrfc_case (fun av => 2 <= av < 4).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P; byte_at memc P; byte_at memc (P + 1)]).
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
assert (HB : forall j, (j < 2)%nat -> ew E (36 + j) = Z_to_bv 64 (byte_at memc (P + Z.of_nat j))).
{ intros j Hj. replace (36 + j)%nat with (32 + (4 + j))%nat by lia. apply HX.
do 2 (destruct j as [|j]; [cbn; rewrite ?Z.add_0_r; reflexivity|]). lia. }
assert (HBr : forall j, (j < 2)%nat -> 0 <= bv_unsigned (ew E (36 + j)) <= 255).
{ intros j Hj. rewrite (HB j Hj). pose proof (byte_at_range memc (P + Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
assert (HS : st_ok src2segs E (ss_rhdr 1) (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))).
{ unfold ss_rhdr. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [rhdr_breg rhdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia |].
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
intros j Hj. split; [apply HB; exact Hj|]. subst P. rewrite <- Z.add_assoc. apply Hpres. lia.
- cbn [rhdr_breg rhdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, ?HX35, ?unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms rbyte_facts rhdr_nbytes nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
pose proof (HBr 0%nat ltac:(lia)) as B0. pose proof (HBr 1%nat ltac:(lia)) as B1.
cbn [Nat.add] in B0, B1.
repeat split; try lia; assumption.
+ cbn [f_conds rhdr_conds rhdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ RHDRZ. { wr4 HU2 HU10 HU11. }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 24)).
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
assert (HB0 : ew E 36 = Z_to_bv 64 (byte_at memc P)) by (replace (byte_at memc P) with (byte_at memc (P + Z.of_nat 0)) by (f_equal; lia); apply (HB 0%nat); lia).
assert (HB1 : ew E 37 = Z_to_bv 64 (byte_at memc (P + 1))) by (apply (HB 1%nat); lia).
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold hideP in Hsd.
rhdr_fin HS HJ Hid HE Hra0 nb; cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ lia.
+ right. split; [lia|].
exists 0, 0, (byte_at memc P + 256 * byte_at memc (P + 1)), (0 + 256 * 0), (0 + 256 * 0).
split.
{ pose proof (byte_at_range memc P) as R0. pose proof (byte_at_range memc (P + 1)) as R1.
apply rgbfc_obj; try assumption; try lia.
- rewrite <- (Z.add_0_r dst). eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 _ dst 0 HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | lia].
- eapply (st_chunk_zero_val src2segs _ _ _ 2%nat _ 11%nat 0 _ dst 8 4%nat HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | cbn; lia].
- rdst_byte HS HU11 36%nat HB0.
- rdst_byte HS HU11 37%nat HB1.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
}
split; [intros _; reflexivity|]. split; [lia|]. cbn [img_block fmt_okb Z.eqb orb app]. exact HBc.
Qed.
Lemma rrfc_case_0 : rrfc_case (fun av => av < 2).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HC HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
apply hideP_i in Hsd.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HFRv : RRFC_FRAME = 64) by reflexivity. assert (HDPv : RRFC_STK = 8256) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hpres : forall i, 0 <= i < nb -> present memc (pdata + i)).
{ intros i Hi. exact (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc pdata nb i HH Hpdc Hi)). }
set (sp := spZ regs) in *.
assert (Hwhi : sp <= sp0) by (clear - Hst1 Hst2; lia).
set (P := pdata + cur).
set (xvals := [pdata; nb; cur; P]).
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
assert (HS : st_ok src2segs E (ss_rhdr 0) (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))).
{ unfold ss_rhdr. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [rhdr_breg rhdr_nbytes nth app]. constructor; [|constructor; [|constructor; [|constructor]]].
+ apply (region_ok_stack src2segs _ memc 2 sp); [exact HU2 | lia | lia |].
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
- cbn [rhdr_breg rhdr_nbytes nth app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10, HU11, ?HX35, ?unsigned_lit_small by lia. unfold hideP in Hsd.
repeat split; lia.
- split; [|split].
+ cbn [f_atoms rbyte_facts rhdr_nbytes nth map seq app Nat.add atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12, HX32, HX33, HX34, HX35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption.
+ cbn [f_conds rhdr_conds rhdr_ends firstn nth_error map app conds_ok].
repeat split;
first [ eapply (cond_geu _ 33 0 34 _ nb cur HX33 HX34); lia
| eapply (cond_ltu _ 33 0 34 _ nb cur HX33 HX34); lia ].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply (alias_add _ 32 34 35 pdata cur HX32 HX34 HX35); lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom src2segs))) in HJ.
jrun_to LAWS src2tbl_ok HS HJ RHDRZ. { wr4 HU2 HU10 HU11. }
sym_add_chunk HS (Some 11%nat) (mkChunk 0 (CZero 24)).
jrun LAWS src2tbl_ok HS HJ. { wr4 HU2 HU10 HU11. }
eapply (SR_ret_at src2segs src2tbl); [exact src2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold hideP in Hsd.
rhdr_fin HS HJ Hid HE Hra0 nb; cbn [ms_mem mkst] in *.
+ intros a Ha Hn1 Hn2 Hn3. rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ intros b m i Hb Hi.
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
rhdr_frames HU2 HU10 HU11 ltac:(lia). reflexivity.
+ rewrite <- (Z.add_0_r st).
eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 0 (SOff 32 0) st pdata HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 8 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ eapply (st_chunk_word _ _ _ 1%nat _ 10%nat 16 (SOff 33 0) st nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocF; exact HU10 | cbn [sv_denot]; ew_havocF; rewrite Z.add_0_r, HX33, Z_to_bv_bv_unsigned; reflexivity | lia].
+ lia.
+ right. split; [lia|].
exists 0, 0, (0 + 256 * 0), (0 + 256 * 0), (0 + 256 * 0).
split.
{
apply rgbfc_obj; try assumption; try lia.
- rewrite <- (Z.add_0_r dst). eapply (st_chunk_zero_word _ _ _ 2%nat _ 11%nat 0 _ dst 0 HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | lia].
- eapply (st_chunk_zero_val src2segs _ _ _ 2%nat _ 11%nat 0 _ dst 8 4%nat HS); [reflexivity | reflexivity | cbv; solve [auto 30] | ew_havocF; exact HU11 | lia | cbn; lia].
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11. - rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
- rdst_zero_any HS HU11.
}
split; [intros _; reflexivity|]. split; [lia|]. cbn [img_block fmt_okb Z.eqb orb app]. exact HBc.
Qed.
Theorem src2_read_frameconfig : rrfc_spec API.
Proof.
unfold rrfc_spec. intros until cur. intros HJ.
destruct (Z_lt_le_dec (nb - cur) 2) as [H|H]; [revert HJ; apply rrfc_case_0; exact H|].
destruct (Z_lt_le_dec (nb - cur) 4) as [H1|H1]; [revert HJ; apply rrfc_case_1; lia|].
destruct (Z_lt_le_dec (nb - cur) 6) as [H2|H2]; [revert HJ; apply rrfc_case_2; lia|].
destruct (Z_lt_le_dec (nb - cur) 7) as [H3|H3]; [revert HJ; apply rrfc_case_3; lia|].
revert HJ; apply rrfc_case_4; lia.
Qed.
End S.
End f.
