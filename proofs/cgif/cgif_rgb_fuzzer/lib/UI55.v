(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h
UI4y UI54 UO0e UIZe UIZf YI0d.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition byte_chunks (k0 cnt : nat) : list YQ0b.chunk :=
map (fun i => mkChunk (Z.of_nat i) (CVal 1 (SOff (k0 + i) 0))) (seq 0 cnt).
Lemma region_ok_bytes : forall E mem n P (cnt : nat) k0,
bv_unsigned (ew E n) = P -> 0 <= P -> P + Z.of_nat cnt <= 2 ^ 64 ->
(forall j, (j < cnt)%nat -> ew E (k0 + j)%nat = Z_to_bv 64 (byte_at mem (P + Z.of_nat j)) /\ present mem (P + Z.of_nat j)) ->
region_ok ubs2segs E mem (YQ0b.mkRegion (Some n) 0 (Z.of_nat cnt) 0 0 (byte_chunks k0 cnt)).
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
Lemma fmt_okb_true : forall b, fmt_okb b = true -> b = 3 \/ b = 4.
Proof.
intros b H. unfold fmt_okb in H. destruct (Z.eqb_spec b 3); [left; assumption|]. destruct (Z.eqb_spec b 4); [right; assumption|]. discriminate H.
Qed.
Lemma Z_to_bv64_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 (2 ^ 64 - 1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Definition rhdr_bytes (m : word -> option byte) (dst b0 b1 b2 b3 b4 b5 : Z) : Prop :=
mbyte ubs2segs m (dst + 12) = Some (Z_to_bv 8 b0) /\ mbyte ubs2segs m (dst + 13) = Some (Z_to_bv 8 b1) /\
mbyte ubs2segs m (dst + 14) = Some (Z_to_bv 8 0) /\ mbyte ubs2segs m (dst + 15) = Some (Z_to_bv 8 0) /\
mbyte ubs2segs m (dst + 16) = Some (Z_to_bv 8 b2) /\ mbyte ubs2segs m (dst + 17) = Some (Z_to_bv 8 b3) /\
mbyte ubs2segs m (dst + 18) = Some (Z_to_bv 8 0) /\ mbyte ubs2segs m (dst + 19) = Some (Z_to_bv 8 0) /\
mbyte ubs2segs m (dst + 20) = Some (Z_to_bv 8 b4) /\ mbyte ubs2segs m (dst + 21) = Some (Z_to_bv 8 b5) /\
mbyte ubs2segs m (dst + 22) = Some (Z_to_bv 8 0) /\ mbyte ubs2segs m (dst + 23) = Some (Z_to_bv 8 0).
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Definition RR_C1 : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 88).
Definition RR_C2 : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 108).
Definition RR_C3 : Z := Eval vm_compute in (ubs2_A_read_frameconfig + 128).
Lemma rfc_offsets : RR_MAL = RRFC + 148 /\ RR_M1 = RRFC + 164 /\ RR_EPI = RRFC + 248.
Proof. vm_compute. repeat split. Qed.
Definition rfc_pc (k : nat) : Z := nth k [RRFC; RR_C1; RR_C2; RR_C3; RR_MAL] RR_MAL.
Definition rfc_rdn (k : nat) : Z := nth k [0; 2; 4; 6; 7] 7.
Definition rfc_cur (cur nb : Z) (k : nat) : Z := if cur + rfc_rdn k <=? nb then cur + rfc_rdn k else nb.
Definition rfc_res (cur nb : Z) (k : nat) : Z := if cur + rfc_rdn k <=? nb then 0 else 2 ^ 64 - 1.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition rrfc_hyps STK sp0 FP L A mem md Lc Ac (memc : word -> option byte) mdc (regs : bvmap 5 word)
(Bb : list (Z * Z)) (st dst N pdata nb cur : Z) : Prop :=
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc /\ st_init_done Ac = true /\
(forall b, In b (blocks L A) -> In b Bb) /\ Permutation (blocks Lc Ac) Bb /\ In (pdata, nb) Bb /\
YK0s.ret_ok (getr regs 1) /\ getr regs 4 = Z_to_bv 64 (ms_tp ubs2_msyms) /\
getr regs 10 = Z_to_bv 64 st /\ getr regs 11 = Z_to_bv 64 dst /\ getr regs 12 = Z_to_bv 64 N /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - RRFC_STK /\ spZ regs <= st /\ st + 24 <= sp0 /\
spZ regs <= dst /\ dst + RGBFC_SIZE <= sp0 /\ (st + 24 <= dst \/ dst + RGBFC_SIZE <= st) /\ st mod 8 = 0 /\ dst mod 8 = 0 /\ sp0 < 2 ^ 63 /\
1 <= N <= RGB_NMAX /\ 0 <= cur <= nb /\ 0 < nb /\
word_mem ubs2segs memc st pdata /\ word_mem ubs2segs memc (st + 8) nb /\ word_mem ubs2segs memc (st + 16) cur.
Definition rfc_cut (k : nat) STK sp0 FP L A mem md Lc Ac (memc : word -> option byte) mdc (regs : bvmap 5 word)
(st dst N pdata nb cur : Z) (c : config) : Prop :=
exists (regs1 : bvmap 5 word) (mem1 : word -> option byte) (fb b0 b1 b2 b3 b4 b5 : Z),
c = mkCfg (mkst regs1 (Z_to_bv 64 (rfc_pc k)) mem1 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem1 mdc /\
getr regs1 2 = Z_to_bv 64 (spZ regs - RRFC_FRAME) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = Z_to_bv 64 dst /\ getr regs1 9 = Z_to_bv 64 st /\ getr regs1 18 = Z_to_bv 64 N /\
getr regs1 10 = Z_to_bv 64 (rfc_res cur nb k) /\
((2 <= k)%nat -> getr regs1 19 = Z_to_bv 64 (rfc_res cur nb 1)) /\
((3 <= k)%nat -> getr regs1 20 = Z_to_bv 64 (rfc_res cur nb 2)) /\
((4 <= k)%nat -> getr regs1 21 = Z_to_bv 64 (rfc_res cur nb 3)) /\
getr regs1 22 = getr regs 22 /\ getr regs1 23 = getr regs 23 /\ getr regs1 24 = getr regs 24 /\
getr regs1 25 = getr regs 25 /\ getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27 /\
word_mem ubs2segs mem1 (spZ regs - 64) (bv_unsigned (getr regs 22)) /\
word_mem ubs2segs mem1 (spZ regs - 56) (bv_unsigned (getr regs 21)) /\
word_mem ubs2segs mem1 (spZ regs - 48) (bv_unsigned (getr regs 20)) /\
word_mem ubs2segs mem1 (spZ regs - 40) (bv_unsigned (getr regs 19)) /\
word_mem ubs2segs mem1 (spZ regs - 32) (bv_unsigned (getr regs 18)) /\
word_mem ubs2segs mem1 (spZ regs - 24) (bv_unsigned (getr regs 9)) /\
word_mem ubs2segs mem1 (spZ regs - 16) (bv_unsigned (getr regs 8)) /\
word_mem ubs2segs mem1 (spZ regs - 8) (bv_unsigned (getr regs 1)) /\
mbyte ubs2segs mem1 (spZ regs - 65) = Some (Z_to_bv 8 fb) /\ 0 <= fb < 256 /\
((k < 4)%nat \/ nb < cur + 7 -> fb = 0) /\
word_mem ubs2segs mem1 st pdata /\ word_mem ubs2segs mem1 (st + 8) nb /\
word_mem ubs2segs mem1 (st + 16) (rfc_cur cur nb k) /\
(forall i, 0 <= i < 12 -> mbyte ubs2segs mem1 (dst + i) = Some (Z_to_bv 8 0)) /\
rhdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 /\ bytes_ok [b0; b1; b2; b3; b4; b5] /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs2segs mem1 a = mbyte ubs2segs memc a).
Definition s0_ss : sstate :=
mkSS RRFC sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [] ;
YQ0b.mkRegion (Some 11%nat) 0 24 0 24 [] ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RRFC_STK) (2^63) 4); (11%nat, mkAF CEIL_MIN (2^63) 3); (10%nat, mkAF CEIL_MIN (2^63) 3);
(12%nat, mkAF 1 RGB_NMAX 0) ] [] []).
Lemma s0_word0 : forall (m : word -> option byte) a i, word_mem ubs2segs m a 0 -> 0 <= i < 8 ->
mbyte ubs2segs m (a + i) = Some (Z_to_bv 8 0).
Proof.
intros m a i H Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (H (Z.to_nat i) ltac:(lia)).
f_equal. unfold le_byte. rewrite Z.mod_0_l by lia. rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma s0_mb_at : forall (m : word -> option byte) a b, mbyte ubs2segs m a = Some b ->
mbyte ubs2segs m a = Some (Z_to_bv 8 (byte_at m a)).
Proof. intros m a b H. unfold byte_at. rewrite H, Z_to_bv_bv_unsigned. reflexivity. Qed.
Ltac s0_sw HS HU2 HE off n rr :=
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat off (SOff n 0) _ _ HS);
[ reflexivity | reflexivity | cbv; auto 12 | exact HU2
| cbn [sv_denot]; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| lazymatch goal with |- 0 <= bv_unsigned ?w < _ =>
let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; lia end ].
Lemma rfc_seg0 : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z),
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom ubs2segs)) mdc)
(rfc_cut 1 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur Hh.
pose proof Hh as (HJ & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp & Wn & Wc).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFRv : RRFC_FRAME = 80) by reflexivity. assert (HDPv : RRFC_STK = 8272) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HRDS : RD_STK = 32) by reflexivity.
assert (HRDN : 2 <= RD_NMAX) by (unfold RD_NMAX; lia).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
set (E := Ereg regs []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = st) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = dst) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HU12 : bv_unsigned (ew E 12) = N) by (rewrite (HE 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; unfold RGB_NMAX in HN; lia).
assert (HS : st_ok ubs2segs E s0_ss (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom ubs2segs))).
{ unfold s0_ss. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ memc 2 (spZ regs)); [exact HU2 | lia | lia |].
intros a Ha. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU11.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU11. repeat split; lia.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HU11, HU12.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 RRFC) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_readdata.
{ wr_norm.
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU11 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
jreg HS (1%bv:reg) as D1.
jreg HS (2%bv:reg) as D2. rewrite HU2 in D2.
jreg HS (10%bv:reg) as D10. rewrite (HE 10%nat 10%bv eq_refl), G10 in D10.
jreg HS (11%bv:reg) as D11. rewrite HU11 in D11.
jreg HS (12%bv:reg) as D12.
jreg HS (8%bv:reg) as D8. rewrite (HE 11%nat 11%bv eq_refl), G11 in D8.
jreg HS (9%bv:reg) as D9. rewrite (HE 10%nat 10%bv eq_refl), G10 in D9.
jreg HS (18%bv:reg) as D18. rewrite (HE 12%nat 12%bv eq_refl), G12 in D18.
jreg HS (3%bv:reg) as D3. rewrite (HE 3%nat 3%bv eq_refl) in D3.
jreg HS (4%bv:reg) as D4. rewrite (HE 4%nat 4%bv eq_refl) in D4.
jreg HS (22%bv:reg) as D22. rewrite (HE 22%nat 22%bv eq_refl) in D22.
jreg HS (23%bv:reg) as D23. rewrite (HE 23%nat 23%bv eq_refl) in D23.
jreg HS (24%bv:reg) as D24. rewrite (HE 24%nat 24%bv eq_refl) in D24.
jreg HS (25%bv:reg) as D25. rewrite (HE 25%nat 25%bv eq_refl) in D25.
jreg HS (26%bv:reg) as D26. rewrite (HE 26%nat 26%bv eq_refl) in D26.
jreg HS (27%bv:reg) as D27. rewrite (HE 27%nat 27%bv eq_refl) in D27.
assert (Hspz : spZ (ms_regs ms) = spZ regs - 80).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite D2, unsigned_lit_small by lia. lia. }
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> ~ (dst <= a < dst + 24) ->
mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha H1 H2. mb_frame HF; try (rewrite ?HU2, ?HU11; lia). reflexivity. }
assert (W00 : word_mem ubs2segs (ms_mem ms) (dst + 0) 0).
{ eapply (st_chunk_word _ _ _ 1%nat _ 11%nat 0 (SLit 0) dst 0 HS); [reflexivity | reflexivity | cbv; auto 12 | exact HU11 | reflexivity | lia]. }
assert (W08 : word_mem ubs2segs (ms_mem ms) (dst + 8) 0).
{ eapply (st_chunk_word _ _ _ 1%nat _ 11%nat 8 (SLit 0) dst 0 HS); [reflexivity | reflexivity | cbv; auto 12 | exact HU11 | reflexivity | lia]. }
assert (W16 : word_mem ubs2segs (ms_mem ms) (dst + 16) 0).
{ eapply (st_chunk_word _ _ _ 1%nat _ 11%nat 16 (SLit 0) dst 0 HS); [reflexivity | reflexivity | cbv; auto 12 | exact HU11 | reflexivity | lia]. }
assert (Z24 : forall i, 0 <= i < 24 -> mbyte ubs2segs (ms_mem ms) (dst + i) = Some (Z_to_bv 8 0)).
{ intros i Hi.
destruct (Z_lt_le_dec i 8) as [H8|H8]; [replace (dst + i) with (dst + 0 + i) by lia; apply s0_word0; [exact W00 | lia] |].
destruct (Z_lt_le_dec i 16) as [H16|H16]; [replace (dst + i) with (dst + 8 + (i - 8)) by lia; apply s0_word0; [exact W08 | lia] |].
replace (dst + i) with (dst + 16 + (i - 16)) by lia; apply s0_word0; [exact W16 | lia]. }
assert (FB : mbyte ubs2segs (ms_mem ms) (spZ regs - 65) = Some (Z_to_bv 8 0)).
{ replace (spZ regs - 65) with (spZ regs + -65) by lia.
eapply (st_chunk_byte _ _ _ 0%nat _ 2%nat (-65) (SLit 0) (spZ regs) 0 HS); [reflexivity | reflexivity | cbv; auto 12 | exact HU2 | reflexivity | lia]. }
assert (S22 : word_mem ubs2segs (ms_mem ms) (spZ regs + -64) (bv_unsigned (getr regs 22))) by s0_sw HS HU2 HE (-64) 22%nat (22%bv : reg).
assert (S21 : word_mem ubs2segs (ms_mem ms) (spZ regs + -56) (bv_unsigned (getr regs 21))) by s0_sw HS HU2 HE (-56) 21%nat (21%bv : reg).
assert (S20 : word_mem ubs2segs (ms_mem ms) (spZ regs + -48) (bv_unsigned (getr regs 20))) by s0_sw HS HU2 HE (-48) 20%nat (20%bv : reg).
assert (S19 : word_mem ubs2segs (ms_mem ms) (spZ regs + -40) (bv_unsigned (getr regs 19))) by s0_sw HS HU2 HE (-40) 19%nat (19%bv : reg).
assert (S18 : word_mem ubs2segs (ms_mem ms) (spZ regs + -32) (bv_unsigned (getr regs 18))) by s0_sw HS HU2 HE (-32) 18%nat (18%bv : reg).
assert (S9 : word_mem ubs2segs (ms_mem ms) (spZ regs + -24) (bv_unsigned (getr regs 9))) by s0_sw HS HU2 HE (-24) 9%nat (9%bv : reg).
assert (S8 : word_mem ubs2segs (ms_mem ms) (spZ regs + -16) (bv_unsigned (getr regs 8))) by s0_sw HS HU2 HE (-16) 8%nat (8%bv : reg).
assert (S1 : word_mem ubs2segs (ms_mem ms) (spZ regs + -8) (bv_unsigned (getr regs 1))) by s0_sw HS HU2 HE (-8) 1%nat (1%bv : reg).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (ubs2_readdata API IMG STK sp0 FP L A mem md Lc Ac _ mdc _ st (dst + 12) 2 pdata nb cur);
[ exact HJ | rewrite D1; apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspz; replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16
| rewrite Hspz, HRDS; lia | rewrite Hspz; lia | lia | exact Hst8
| exact D10 | exact D11 | exact D12 | lia | lia | lia
| apply word_mem_frame with (m := memc); [exact Wp | intros i Hi; apply KEEPC; lia]
| apply word_mem_frame with (m := memc); [exact Wn | intros i Hi; apply KEEPC; lia]
| apply word_mem_frame with (m := memc); [exact Wc | intros i Hi; apply KEEPC; lia]
| intros Hfit ].
rewrite Hspz, HRDS.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (pdata + cur + i) with (pdata + (cur + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb (cur + i) HHc Hpdc ltac:(lia))). }
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply writable_off_img_present; [lia | unfold in_img1; lia |].
apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
split.
{ intros a Ha. left. lia. }
split; [right; lia|]. split; [lia|]. right; lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Hcase & Hout2).
rewrite Hspz, HRDS in Hout2.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 - 32 <= a < spZ regs - 80) -> ~ (st + 16 <= a < st + 24) ->
~ (dst + 12 <= a < dst + 14) -> mbyte ubs2segs mem2 a = mbyte ubs2segs (ms_mem ms) a).
{ intros a Ha H1 H2 H3. apply Hout2; lia. }
assert (R10 : getr regs2 10 = Z_to_bv 64 (rfc_res cur nb 1)).
{ unfold rfc_res, rfc_rdn. cbn [nth]. destruct Hcase as [(Hfit & Q10 & _) | (Hno & Q10 & _)].
- rewrite (proj2 (Z.leb_le (cur + 2) nb) Hfit). exact Q10.
- rewrite (proj2 (Z.leb_gt (cur + 2) nb) Hno). exact Q10. }
assert (WC1 : word_mem ubs2segs mem2 (st + 16) (rfc_cur cur nb 1)).
{ unfold rfc_cur, rfc_rdn. cbn [nth]. destruct Hcase as [(Hfit & _ & Wc2 & _) | (Hno & _ & Wc2)].
- rewrite (proj2 (Z.leb_le (cur + 2) nb) Hfit). exact Wc2.
- rewrite (proj2 (Z.leb_gt (cur + 2) nb) Hno). exact Wc2. }
assert (P12 : forall i, 0 <= i < 2 -> exists b, mbyte ubs2segs mem2 (dst + 12 + i) = Some b).
{ intros i Hi. destruct Hcase as [(Hfit & _ & _ & Hby) | (Hno & _ & _)].
- destruct (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb (cur + i) HHc Hpdc ltac:(lia))) as [b Hb].
exists b. rewrite Hby by exact Hi. unfold mbyte. replace (pdata + cur + i) with (pdata + (cur + i)) by lia. rewrite Hb. reflexivity.
- exists (Z_to_bv 8 0). rewrite Hout2 by lia. rewrite <- Z.add_assoc. apply Z24. lia. }
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold callee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (HP2 3 ltac:(unfold callee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (HP2 4 ltac:(unfold callee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (HP2 8 ltac:(unfold callee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (HP2 9 ltac:(unfold callee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by exact (HP2 18 ltac:(unfold callee_saved; lia)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (HP2 22 ltac:(unfold callee_saved; lia)).
assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by exact (HP2 23 ltac:(unfold callee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (HP2 24 ltac:(unfold callee_saved; lia)).
assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (HP2 25 ltac:(unfold callee_saved; lia)).
assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (HP2 26 ltac:(unfold callee_saved; lia)).
assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by exact (HP2 27 ltac:(unfold callee_saved; lia)).
destruct (P12 0 ltac:(lia)) as [b0' Hb0]. destruct (P12 1 ltac:(lia)) as [b1' Hb1].
rewrite Z.add_0_r in Hb0. replace (dst + 12 + 1) with (dst + 13) in Hb1 by lia.
unfold rfc_cut.
exists regs2, mem2, 0, (byte_at mem2 (dst + 12)), (byte_at mem2 (dst + 13)), 0, 0, 0, 0.
split. { rewrite D1. reflexivity. }
split. { exact HJ2. }
split. { rewrite P2, D2, HFRv; f_equal; lia. }
split. { rewrite P3, D3; reflexivity. }
split. { rewrite P4, D4; reflexivity. }
split. { rewrite P8, D8; reflexivity. }
split. { rewrite P9, D9; reflexivity. }
split. { rewrite P18, D18; reflexivity. }
split. { exact R10. }
split. { intros Hk; lia. }
split. { intros Hk; lia. }
split. { intros Hk; lia. }
split. { rewrite P22, D22; reflexivity. }
split. { rewrite P23, D23; reflexivity. }
split. { rewrite P24, D24; reflexivity. }
split. { rewrite P25, D25; reflexivity. }
split. { rewrite P26, D26; reflexivity. }
split. { rewrite P27, D27; reflexivity. }
split. { replace (spZ regs - 64) with (spZ regs + -64) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S22 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 56) with (spZ regs + -56) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S21 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 48) with (spZ regs + -48) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S20 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 40) with (spZ regs + -40) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S19 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 32) with (spZ regs + -32) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S18 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 24) with (spZ regs + -24) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S9 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 16) with (spZ regs + -16) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S8 | intros i Hi; apply KEEP2; lia]. }
split. { replace (spZ regs - 8) with (spZ regs + -8) by lia. apply word_mem_frame with (m := ms_mem ms); [exact S1 | intros i Hi; apply KEEP2; lia]. }
split. { rewrite KEEP2 by lia. exact FB. }
split. { lia. }
split. { intros _; reflexivity. }
split. { apply word_mem_frame with (m := memc); [exact Wp | intros i Hi; rewrite KEEP2 by lia; apply KEEPC; lia]. }
split. { apply word_mem_frame with (m := memc); [exact Wn | intros i Hi; rewrite KEEP2 by lia; apply KEEPC; lia]. }
split. { exact WC1. }
split. { intros i Hi. rewrite KEEP2 by lia. apply Z24. lia. }
split.
{ unfold rhdr_bytes.
split; [exact (s0_mb_at _ _ _ Hb0)|]. split; [exact (s0_mb_at _ _ _ Hb1)|].
do 9 (split; [rewrite KEEP2 by lia; apply Z24; lia|]). rewrite KEEP2 by lia; apply Z24; lia. }
split.
{ unfold bytes_ok. pose proof (byte_at_range mem2 (dst + 12)). pose proof (byte_at_range mem2 (dst + 13)).
repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
intros a Ha H1 H2 H3. rewrite KEEP2 by lia. apply KEEPC; lia.
Qed.
Lemma s13_find_segment_high : forall a n, CEIL_MIN <= a -> 0 < n -> find_segment ubs2segs a n = None.
Proof.
intros a n Ha Hn. destruct (find_segment ubs2segs a n) as [sg|] eqn:Hf; [|reflexivity]. exfalso.
pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin. pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [Hlo Hhi].
assert (Hall : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? CEIL_MIN) ubs2segs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hall sg Hin) as Hb. cbn beta in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma s13_writable_present : forall (m : word -> option byte) a,
CEIL_MIN <= a < 2 ^ 64 -> writable_at ubs2segs m a -> present m a.
Proof.
intros m a Ha Hw. unfold writable_at, wview in Hw. unfold present.
destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|]. exfalso. apply Hw.
rewrite unsigned_lit_small by lia. rewrite s13_find_segment_high by lia. reflexivity.
Qed.
Lemma s13_mbyte_present : forall (m : word -> option byte) a, present m a ->
exists v, mbyte ubs2segs m a = Some (Z_to_bv 8 v) /\ 0 <= v < 256.
Proof.
intros m a [b Hb]. exists (bv_unsigned b). unfold mbyte. rewrite Hb. split.
- rewrite Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Lemma s13_pres : forall (r2 r3 : bvmap 5 word) (r : Z) (x : reg) (v : word),
regs_preserved r2 r3 -> callee_saved r -> x = Z_to_bv 5 r -> getr r2 x = v -> getr r3 x = v.
Proof. intros r2 r3 r x v HP Hc -> H. rewrite HP by exact Hc. exact H. Qed.
Lemma s13_cur_range : forall cur nb k, 0 <= cur <= nb -> 0 <= rfc_rdn k -> cur <= rfc_cur cur nb k <= nb.
Proof. intros cur nb k Hc Hk. unfold rfc_cur. destruct (Z.leb_spec (cur + rfc_rdn k) nb); cbv iota; lia. Qed.
Lemma s13_step : forall cur nb (k : nat) n, rfc_rdn (Datatypes.S k) = rfc_rdn k + n -> 0 < n ->
(rfc_cur cur nb k + n <= nb -> rfc_cur cur nb (Datatypes.S k) = rfc_cur cur nb k + n /\ rfc_res cur nb (Datatypes.S k) = 0 /\
cur + rfc_rdn (Datatypes.S k) <= nb) /\
(nb < rfc_cur cur nb k + n -> rfc_cur cur nb (Datatypes.S k) = nb /\ rfc_res cur nb (Datatypes.S k) = 2 ^ 64 - 1).
Proof.
intros cur nb k n Hk Hn. unfold rfc_cur, rfc_res. rewrite Hk.
destruct (Z.leb_spec (cur + rfc_rdn k) nb) as [Ha|Ha]; destruct (Z.leb_spec (cur + (rfc_rdn k + n)) nb) as [Hb|Hb]; cbv iota;
split; intros Hc; repeat split; first [reflexivity | lia].
Qed.
Lemma s13_bytes_ok : forall b0 b1 b2 b3 b4 b5, bytes_ok [b0; b1; b2; b3; b4; b5] <->
0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256 /\ 0 <= b3 < 256 /\ 0 <= b4 < 256 /\ 0 <= b5 < 256.
Proof.
intros b0 b1 b2 b3 b4 b5. unfold bytes_ok. rewrite !Forall_cons_iff. split.
- intros H. cbv beta in H. tauto.
- intros H. repeat split; try lia. constructor.
Qed.
Lemma rfc_seg1 : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) c,
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
rfc_cut 1 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur c ->
SR ubs2segs c (rfc_cut 2 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c Hh H1.
pose proof Hh as (HJ0 & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp0 & Wn0 & Wc0).
destruct H1 as (regs1 & mem1 & fb & b0 & b1 & b2 & b3 & b4 & b5 & -> & HJ & G2 & G3 & G4 & G8 & G9 & G18 & Q10 &
G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & W22 & W21 & W20 & W19 & W18 & W9 & W8 & W1 &
Bf & Hfb & Hfb0 & Wp & Wn & Wc & Z12 & Hhb & HB & Hfr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFRv : RRFC_FRAME = 80) by reflexivity. assert (HDPv : RRFC_STK = 8272) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HRDS : RD_STK = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hspm : (spZ regs - RRFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
pose proof (s13_cur_range cur nb 1 Hcur ltac:(unfold rfc_rdn; cbn [nth]; lia)) as Hcr.
pose proof (s13_step cur nb 1 2 eq_refl ltac:(lia)) as Hstep.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 []) n = getr regs1 rr)
by (intros; apply ew_Ereg_nat; assumption).
assert (HS : st_ok ubs2segs (Ereg regs1 []) (mkSS (rfc_pc 1) sr_atoms [] None (mkFacts [] [] []))
(mkst regs1 (Z_to_bv 64 (rfc_pc 1)) mem1 (seg_rom ubs2segs))).
{ apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (rfc_pc 1)) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_readdata. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
jreg HS (10%bv:reg) as D10. rewrite (HE 9%nat 9%bv eq_refl), G9 in D10.
jreg HS (11%bv:reg) as D11. rewrite (HE 8%nat 8%bv eq_refl), G8, unsigned_lit_small in D11 by lia.
jreg HS (12%bv:reg) as D12.
jreg HS (1%bv:reg) as D1.
jreg HS (2%bv:reg) as D2. rewrite (HE 2%nat 2%bv eq_refl), G2 in D2.
jreg HS (3%bv:reg) as D3. rewrite (HE 3%nat 3%bv eq_refl), G3 in D3.
jreg HS (4%bv:reg) as D4. rewrite (HE 4%nat 4%bv eq_refl), G4 in D4.
jreg HS (8%bv:reg) as D8. rewrite (HE 8%nat 8%bv eq_refl), G8 in D8.
jreg HS (9%bv:reg) as D9. rewrite (HE 9%nat 9%bv eq_refl), G9 in D9.
jreg HS (18%bv:reg) as D18. rewrite (HE 18%nat 18%bv eq_refl), G18 in D18.
jreg HS (19%bv:reg) as D19. rewrite (HE 10%nat 10%bv eq_refl), Q10 in D19.
jreg HS (22%bv:reg) as D22. rewrite (HE 22%nat 22%bv eq_refl), G22 in D22.
jreg HS (23%bv:reg) as D23. rewrite (HE 23%nat 23%bv eq_refl), G23 in D23.
jreg HS (24%bv:reg) as D24. rewrite (HE 24%nat 24%bv eq_refl), G24 in D24.
jreg HS (25%bv:reg) as D25. rewrite (HE 25%nat 25%bv eq_refl), G25 in D25.
jreg HS (26%bv:reg) as D26. rewrite (HE 26%nat 26%bv eq_refl), G26 in D26.
jreg HS (27%bv:reg) as D27. rewrite (HE 27%nat 27%bv eq_refl), G27 in D27.
assert (Hspz : spZ (ms_regs ms) = spZ regs - RRFC_FRAME).
{ unfold spZ at 1. rewrite D2. apply unsigned_lit_small. lia. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem1 a).
{ intros a Ha. apply (mbyte_of_frame _ [] mem1 (ms_mem ms) a HF Ha). intros r Hr. destruct Hr. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstwc) & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (ubs2_readdata API IMG STK sp0 FP L A mem md Lc Ac _ mdc _ st (dst + 16) 2 pdata nb (rfc_cur cur nb 1));
[ exact HJ | rewrite D1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hspm
| rewrite Hspz; lia | rewrite Hspz; lia | lia | exact Hst8
| exact D10 | exact D11 | exact D12 | unfold RD_NMAX; lia | lia | lia
| apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wc | intros i Hi; apply HM; lia]
| intros Hfit ].
rewrite ?Hspz.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (pdata + rfc_cur cur nb 1 + i) with (pdata + (rfc_cur cur nb 1 + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb (rfc_cur cur nb 1 + i) HHc Hpdc ltac:(lia))). }
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply s13_writable_present; [lia|]. apply Hstwc. lia. }
split; [intros a Ha; left; lia|].
split; [right; lia|]. split; [lia|]. right; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hcase & Hout3).
rewrite Hspz, HRDS in Hout3.
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_FRAME - 32 <= a < spZ regs - RRFC_FRAME) ->
~ (st + 16 <= a < st + 24) -> ~ (dst + 16 <= a < dst + 18) -> mbyte ubs2segs mem3 a = mbyte ubs2segs mem1 a).
{ intros a Ha Ha1 Ha2 Ha3. rewrite (Hout3 a Ha Ha1 Ha2 ltac:(intros [_ Hx]; lia)). apply HM; exact Ha. }
assert (HX : word_mem ubs2segs mem3 (st + 16) (rfc_cur cur nb 2) /\ getr regs3 10 = Z_to_bv 64 (rfc_res cur nb 2) /\
exists c2 c3, 0 <= c2 < 256 /\ 0 <= c3 < 256 /\
mbyte ubs2segs mem3 (dst + 16) = Some (Z_to_bv 8 c2) /\ mbyte ubs2segs mem3 (dst + 17) = Some (Z_to_bv 8 c3)).
{ destruct Hcase as [(Hfit & R10 & Wc3 & Hcp) | (Hnofit & R10 & Wc3)].
- destruct (proj1 Hstep Hfit) as (Ec2 & Er2 & _).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
destruct (s13_mbyte_present mem1 (pdata + rfc_cur cur nb 1 + 0)) as (v0 & Hv0 & Rv0).
{ replace (pdata + rfc_cur cur nb 1 + 0) with (pdata + (rfc_cur cur nb 1 + 0)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac mem1 mdc pdata nb (rfc_cur cur nb 1 + 0) HH Hpdc ltac:(lia))). }
destruct (s13_mbyte_present mem1 (pdata + rfc_cur cur nb 1 + 1)) as (v1 & Hv1 & Rv1).
{ replace (pdata + rfc_cur cur nb 1 + 1) with (pdata + (rfc_cur cur nb 1 + 1)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac mem1 mdc pdata nb (rfc_cur cur nb 1 + 1) HH Hpdc ltac:(lia))). }
exists v0, v1. split; [exact Rv0|]. split; [exact Rv1|]. split.
+ replace (dst + 16) with (dst + 16 + 0) by lia. rewrite Hcp by lia. rewrite HM by lia. exact Hv0.
+ replace (dst + 17) with (dst + 16 + 1) by lia. rewrite Hcp by lia. rewrite HM by lia. exact Hv1.
- destruct (proj2 Hstep Hnofit) as (Ec2 & Er2).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
pose proof Hhb as (_ & _ & _ & _ & H16 & H17 & _).
apply s13_bytes_ok in HB.
exists b2, b3. split; [lia|]. split; [lia|]. split.
+ rewrite (Hout3 (dst + 16) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)), HM by lia. exact H16.
+ rewrite (Hout3 (dst + 17) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)), HM by lia. exact H17. }
destruct HX as (Wc' & R' & c2 & c3 & Rc2 & Rc3 & N16 & N17).
apply SR_ret. unfold rfc_cut.
exists regs3, mem3, fb, b0, b1, c2, c3, b4, b5.
split; [rewrite D1; reflexivity|].
split; [exact HJ3|].
split; [apply (s13_pres _ _ 2 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D2|].
split; [apply (s13_pres _ _ 3 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D3|].
split; [apply (s13_pres _ _ 4 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D4|].
split; [apply (s13_pres _ _ 8 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D8|].
split; [apply (s13_pres _ _ 9 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D9|].
split; [apply (s13_pres _ _ 18 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D18|].
split; [exact R'|].
split; [intros _; apply (s13_pres _ _ 19 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D19|].
split; [intros Hx; lia|].
split; [intros Hx; lia|].
split; [apply (s13_pres _ _ 22 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D22|].
split; [apply (s13_pres _ _ 23 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D23|].
split; [apply (s13_pres _ _ 24 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D24|].
split; [apply (s13_pres _ _ 25 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D25|].
split; [apply (s13_pres _ _ 26 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D26|].
split; [apply (s13_pres _ _ 27 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D27|].
split; [apply word_mem_frame with (m := mem1); [exact W22 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W21 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W20 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W19 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W18 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W9 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W8 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W1 | intros i Hi; apply Hk; lia]|].
split; [rewrite Hk by lia; exact Bf|].
split; [exact Hfb|].
split; [intros _; apply Hfb0; left; lia|].
split; [apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply Hk; lia]|].
split; [exact Wc'|].
split; [intros i Hi; rewrite Hk by lia; apply Z12; exact Hi|].
split.
{ unfold rhdr_bytes in Hhb |- *.
destruct Hhb as (H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23).
repeat match goal with |- _ /\ _ => split end; first [exact N16 | exact N17 | rewrite Hk by lia; assumption]. }
split.
{ apply s13_bytes_ok. apply s13_bytes_ok in HB. lia. }
intros a Ha Na1 Na2 Na3. rewrite Hk by lia. apply Hfr; assumption.
Qed.
Lemma rfc_seg2 : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) c,
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
rfc_cut 2 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur c ->
SR ubs2segs c (rfc_cut 3 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c Hh H1.
pose proof Hh as (HJ0 & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp0 & Wn0 & Wc0).
destruct H1 as (regs1 & mem1 & fb & b0 & b1 & b2 & b3 & b4 & b5 & -> & HJ & G2 & G3 & G4 & G8 & G9 & G18 & Q10 &
G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & W22 & W21 & W20 & W19 & W18 & W9 & W8 & W1 &
Bf & Hfb & Hfb0 & Wp & Wn & Wc & Z12 & Hhb & HB & Hfr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFRv : RRFC_FRAME = 80) by reflexivity. assert (HDPv : RRFC_STK = 8272) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HRDS : RD_STK = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hspm : (spZ regs - RRFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
pose proof (s13_cur_range cur nb 2 Hcur ltac:(unfold rfc_rdn; cbn [nth]; lia)) as Hcr.
pose proof (s13_step cur nb 2 2 eq_refl ltac:(lia)) as Hstep.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 []) n = getr regs1 rr)
by (intros; apply ew_Ereg_nat; assumption).
assert (HS : st_ok ubs2segs (Ereg regs1 []) (mkSS (rfc_pc 2) sr_atoms [] None (mkFacts [] [] []))
(mkst regs1 (Z_to_bv 64 (rfc_pc 2)) mem1 (seg_rom ubs2segs))).
{ apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (rfc_pc 2)) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_readdata. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
jreg HS (10%bv:reg) as D10. rewrite (HE 9%nat 9%bv eq_refl), G9 in D10.
jreg HS (11%bv:reg) as D11. rewrite (HE 8%nat 8%bv eq_refl), G8, unsigned_lit_small in D11 by lia.
jreg HS (12%bv:reg) as D12.
jreg HS (1%bv:reg) as D1.
jreg HS (2%bv:reg) as D2. rewrite (HE 2%nat 2%bv eq_refl), G2 in D2.
jreg HS (3%bv:reg) as D3. rewrite (HE 3%nat 3%bv eq_refl), G3 in D3.
jreg HS (4%bv:reg) as D4. rewrite (HE 4%nat 4%bv eq_refl), G4 in D4.
jreg HS (8%bv:reg) as D8. rewrite (HE 8%nat 8%bv eq_refl), G8 in D8.
jreg HS (9%bv:reg) as D9. rewrite (HE 9%nat 9%bv eq_refl), G9 in D9.
jreg HS (18%bv:reg) as D18. rewrite (HE 18%nat 18%bv eq_refl), G18 in D18.
jreg HS (19%bv:reg) as D19. rewrite (HE 19%nat 19%bv eq_refl), (G19 ltac:(lia)) in D19.
jreg HS (20%bv:reg) as D20. rewrite (HE 10%nat 10%bv eq_refl), Q10 in D20.
jreg HS (22%bv:reg) as D22. rewrite (HE 22%nat 22%bv eq_refl), G22 in D22.
jreg HS (23%bv:reg) as D23. rewrite (HE 23%nat 23%bv eq_refl), G23 in D23.
jreg HS (24%bv:reg) as D24. rewrite (HE 24%nat 24%bv eq_refl), G24 in D24.
jreg HS (25%bv:reg) as D25. rewrite (HE 25%nat 25%bv eq_refl), G25 in D25.
jreg HS (26%bv:reg) as D26. rewrite (HE 26%nat 26%bv eq_refl), G26 in D26.
jreg HS (27%bv:reg) as D27. rewrite (HE 27%nat 27%bv eq_refl), G27 in D27.
assert (Hspz : spZ (ms_regs ms) = spZ regs - RRFC_FRAME).
{ unfold spZ at 1. rewrite D2. apply unsigned_lit_small. lia. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem1 a).
{ intros a Ha. apply (mbyte_of_frame _ [] mem1 (ms_mem ms) a HF Ha). intros r Hr. destruct Hr. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstwc) & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (ubs2_readdata API IMG STK sp0 FP L A mem md Lc Ac _ mdc _ st (dst + 20) 2 pdata nb (rfc_cur cur nb 2));
[ exact HJ | rewrite D1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hspm
| rewrite Hspz; lia | rewrite Hspz; lia | lia | exact Hst8
| exact D10 | exact D11 | exact D12 | unfold RD_NMAX; lia | lia | lia
| apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wc | intros i Hi; apply HM; lia]
| intros Hfit ].
rewrite ?Hspz.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (pdata + rfc_cur cur nb 2 + i) with (pdata + (rfc_cur cur nb 2 + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb (rfc_cur cur nb 2 + i) HHc Hpdc ltac:(lia))). }
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply s13_writable_present; [lia|]. apply Hstwc. lia. }
split; [intros a Ha; left; lia|].
split; [right; lia|]. split; [lia|]. right; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hcase & Hout3).
rewrite Hspz, HRDS in Hout3.
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_FRAME - 32 <= a < spZ regs - RRFC_FRAME) ->
~ (st + 16 <= a < st + 24) -> ~ (dst + 20 <= a < dst + 22) -> mbyte ubs2segs mem3 a = mbyte ubs2segs mem1 a).
{ intros a Ha Ha1 Ha2 Ha3. rewrite (Hout3 a Ha Ha1 Ha2 ltac:(intros [_ Hx]; lia)). apply HM; exact Ha. }
assert (HX : word_mem ubs2segs mem3 (st + 16) (rfc_cur cur nb 3) /\ getr regs3 10 = Z_to_bv 64 (rfc_res cur nb 3) /\
exists c4 c5, 0 <= c4 < 256 /\ 0 <= c5 < 256 /\
mbyte ubs2segs mem3 (dst + 20) = Some (Z_to_bv 8 c4) /\ mbyte ubs2segs mem3 (dst + 21) = Some (Z_to_bv 8 c5)).
{ destruct Hcase as [(Hfit & R10 & Wc3 & Hcp) | (Hnofit & R10 & Wc3)].
- destruct (proj1 Hstep Hfit) as (Ec2 & Er2 & _).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
destruct (s13_mbyte_present mem1 (pdata + rfc_cur cur nb 2 + 0)) as (v0 & Hv0 & Rv0).
{ replace (pdata + rfc_cur cur nb 2 + 0) with (pdata + (rfc_cur cur nb 2 + 0)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac mem1 mdc pdata nb (rfc_cur cur nb 2 + 0) HH Hpdc ltac:(lia))). }
destruct (s13_mbyte_present mem1 (pdata + rfc_cur cur nb 2 + 1)) as (v1 & Hv1 & Rv1).
{ replace (pdata + rfc_cur cur nb 2 + 1) with (pdata + (rfc_cur cur nb 2 + 1)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac mem1 mdc pdata nb (rfc_cur cur nb 2 + 1) HH Hpdc ltac:(lia))). }
exists v0, v1. split; [exact Rv0|]. split; [exact Rv1|]. split.
+ replace (dst + 20) with (dst + 20 + 0) by lia. rewrite Hcp by lia. rewrite HM by lia. exact Hv0.
+ replace (dst + 21) with (dst + 20 + 1) by lia. rewrite Hcp by lia. rewrite HM by lia. exact Hv1.
- destruct (proj2 Hstep Hnofit) as (Ec2 & Er2).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
pose proof Hhb as (_ & _ & _ & _ & _ & _ & _ & _ & H20 & H21 & _).
apply s13_bytes_ok in HB.
exists b4, b5. split; [lia|]. split; [lia|]. split.
+ rewrite (Hout3 (dst + 20) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)), HM by lia. exact H20.
+ rewrite (Hout3 (dst + 21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)), HM by lia. exact H21. }
destruct HX as (Wc' & R' & c4 & c5 & Rc4 & Rc5 & N20 & N21).
apply SR_ret. unfold rfc_cut.
exists regs3, mem3, fb, b0, b1, b2, b3, c4, c5.
split; [rewrite D1; reflexivity|].
split; [exact HJ3|].
split; [apply (s13_pres _ _ 2 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D2|].
split; [apply (s13_pres _ _ 3 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D3|].
split; [apply (s13_pres _ _ 4 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D4|].
split; [apply (s13_pres _ _ 8 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D8|].
split; [apply (s13_pres _ _ 9 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D9|].
split; [apply (s13_pres _ _ 18 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D18|].
split; [exact R'|].
split; [intros _; apply (s13_pres _ _ 19 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D19|].
split; [intros _; apply (s13_pres _ _ 20 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D20|].
split; [intros Hx; lia|].
split; [apply (s13_pres _ _ 22 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D22|].
split; [apply (s13_pres _ _ 23 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D23|].
split; [apply (s13_pres _ _ 24 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D24|].
split; [apply (s13_pres _ _ 25 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D25|].
split; [apply (s13_pres _ _ 26 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D26|].
split; [apply (s13_pres _ _ 27 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D27|].
split; [apply word_mem_frame with (m := mem1); [exact W22 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W21 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W20 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W19 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W18 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W9 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W8 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W1 | intros i Hi; apply Hk; lia]|].
split; [rewrite Hk by lia; exact Bf|].
split; [exact Hfb|].
split; [intros _; apply Hfb0; left; lia|].
split; [apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply Hk; lia]|].
split; [exact Wc'|].
split; [intros i Hi; rewrite Hk by lia; apply Z12; exact Hi|].
split.
{ unfold rhdr_bytes in Hhb |- *.
destruct Hhb as (H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23).
repeat match goal with |- _ /\ _ => split end; first [exact N20 | exact N21 | rewrite Hk by lia; assumption]. }
split.
{ apply s13_bytes_ok. apply s13_bytes_ok in HB. lia. }
intros a Ha Na1 Na2 Na3. rewrite Hk by lia. apply Hfr; assumption.
Qed.
Lemma rfc_seg3 : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) c,
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
rfc_cut 3 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur c ->
SR ubs2segs c (rfc_cut 4 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c Hh H1.
pose proof Hh as (HJ0 & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp0 & Wn0 & Wc0).
destruct H1 as (regs1 & mem1 & fb & b0 & b1 & b2 & b3 & b4 & b5 & -> & HJ & G2 & G3 & G4 & G8 & G9 & G18 & Q10 &
G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & W22 & W21 & W20 & W19 & W18 & W9 & W8 & W1 &
Bf & Hfb & Hfb0 & Wp & Wn & Wc & Z12 & Hhb & HB & Hfr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HFRv : RRFC_FRAME = 80) by reflexivity. assert (HDPv : RRFC_STK = 8272) by reflexivity.
assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HRDS : RD_STK = 32) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hpd]).
destruct (heap_blocks_range _ _ LAWS Lc Ac mem1 mdc pdata nb HH Hpdc ltac:(lia)) as (Hp0 & Hp1 & _).
assert (Hspm : (spZ regs - RRFC_FRAME) mod 16 = 0).
{ rewrite HFRv. replace (spZ regs - 80) with (spZ regs + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16. }
pose proof (s13_cur_range cur nb 3 Hcur ltac:(unfold rfc_rdn; cbn [nth]; lia)) as Hcr.
pose proof (s13_step cur nb 3 1 eq_refl ltac:(lia)) as Hstep.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew (Ereg regs1 []) n = getr regs1 rr)
by (intros; apply ew_Ereg_nat; assumption).
assert (HS : st_ok ubs2segs (Ereg regs1 []) (mkSS (rfc_pc 3) sr_atoms [] None (mkFacts [] [] []))
(mkst regs1 (Z_to_bv 64 (rfc_pc 3)) mem1 (seg_rom ubs2segs))).
{ apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 (rfc_pc 3)) mem1 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_readdata. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HJ.
jreg HS (10%bv:reg) as D10. rewrite (HE 9%nat 9%bv eq_refl), G9 in D10.
jreg HS (11%bv:reg) as D11. rewrite (HE 2%nat 2%bv eq_refl), G2, unsigned_lit_small in D11 by lia.
jreg HS (12%bv:reg) as D12.
jreg HS (1%bv:reg) as D1.
jreg HS (2%bv:reg) as D2. rewrite (HE 2%nat 2%bv eq_refl), G2 in D2.
jreg HS (3%bv:reg) as D3. rewrite (HE 3%nat 3%bv eq_refl), G3 in D3.
jreg HS (4%bv:reg) as D4. rewrite (HE 4%nat 4%bv eq_refl), G4 in D4.
jreg HS (8%bv:reg) as D8. rewrite (HE 8%nat 8%bv eq_refl), G8 in D8.
jreg HS (9%bv:reg) as D9. rewrite (HE 9%nat 9%bv eq_refl), G9 in D9.
jreg HS (18%bv:reg) as D18. rewrite (HE 18%nat 18%bv eq_refl), G18 in D18.
jreg HS (19%bv:reg) as D19. rewrite (HE 19%nat 19%bv eq_refl), (G19 ltac:(lia)) in D19.
jreg HS (20%bv:reg) as D20. rewrite (HE 20%nat 20%bv eq_refl), (G20 ltac:(lia)) in D20.
jreg HS (21%bv:reg) as D21. rewrite (HE 10%nat 10%bv eq_refl), Q10 in D21.
jreg HS (22%bv:reg) as D22. rewrite (HE 22%nat 22%bv eq_refl), G22 in D22.
jreg HS (23%bv:reg) as D23. rewrite (HE 23%nat 23%bv eq_refl), G23 in D23.
jreg HS (24%bv:reg) as D24. rewrite (HE 24%nat 24%bv eq_refl), G24 in D24.
jreg HS (25%bv:reg) as D25. rewrite (HE 25%nat 25%bv eq_refl), G25 in D25.
jreg HS (26%bv:reg) as D26. rewrite (HE 26%nat 26%bv eq_refl), G26 in D26.
jreg HS (27%bv:reg) as D27. rewrite (HE 27%nat 27%bv eq_refl), G27 in D27.
assert (D11' : getr (ms_regs ms) 11 = Z_to_bv 64 (spZ regs - 65)) by (rewrite D11; f_equal; lia).
assert (Hspz : spZ (ms_regs ms) = spZ regs - RRFC_FRAME).
{ unfold spZ at 1. rewrite D2. apply unsigned_lit_small. lia. }
assert (HM : forall a, 0 <= a < 2 ^ 64 -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem1 a).
{ intros a Ha. apply (mbyte_of_frame _ [] mem1 (ms_mem ms) a HF Ha). intros r Hr. destruct Hr. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & Hstwc) & _).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (ubs2_readdata API IMG STK sp0 FP L A mem md Lc Ac _ mdc _ st (spZ regs - 65) 1 pdata nb (rfc_cur cur nb 3));
[ exact HJ | rewrite D1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspz; exact Hspm
| rewrite Hspz; lia | rewrite Hspz; lia | lia | exact Hst8
| exact D10 | exact D11' | exact D12 | unfold RD_NMAX; lia | lia | lia
| apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply HM; lia]
| apply word_mem_frame with (m := mem1); [exact Wc | intros i Hi; apply HM; lia]
| intros Hfit ].
rewrite ?Hspz.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (pdata + rfc_cur cur nb 3 + i) with (pdata + (rfc_cur cur nb 3 + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac _ mdc pdata nb (rfc_cur cur nb 3 + i) HHc Hpdc ltac:(lia))). }
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply s13_writable_present; [lia|]. apply Hstwc. lia. }
split; [intros a Ha; left; lia|].
split; [right; lia|]. split; [lia|]. right; lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & HP3 & Hcase & Hout3).
rewrite Hspz, HRDS in Hout3.
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_FRAME - 32 <= a < spZ regs - RRFC_FRAME) ->
~ (st + 16 <= a < st + 24) -> ~ (spZ regs - 65 <= a < spZ regs - 64) -> mbyte ubs2segs mem3 a = mbyte ubs2segs mem1 a).
{ intros a Ha Ha1 Ha2 Ha3. rewrite (Hout3 a Ha Ha1 Ha2 ltac:(intros [_ Hx]; lia)). apply HM; exact Ha. }
assert (HX : word_mem ubs2segs mem3 (st + 16) (rfc_cur cur nb 4) /\ getr regs3 10 = Z_to_bv 64 (rfc_res cur nb 4) /\
exists f, 0 <= f < 256 /\ mbyte ubs2segs mem3 (spZ regs - 65) = Some (Z_to_bv 8 f) /\ (nb < cur + 7 -> f = 0)).
{ destruct Hcase as [(Hfit & R10 & Wc3 & Hcp) | (Hnofit & R10 & Wc3)].
- destruct (proj1 Hstep Hfit) as (Ec2 & Er2 & H7).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
destruct (s13_mbyte_present mem1 (pdata + rfc_cur cur nb 3 + 0)) as (v0 & Hv0 & Rv0).
{ replace (pdata + rfc_cur cur nb 3 + 0) with (pdata + (rfc_cur cur nb 3 + 0)) by lia.
exact (proj1 (heap_blocks _ _ LAWS Lc Ac mem1 mdc pdata nb (rfc_cur cur nb 3 + 0) HH Hpdc ltac:(lia))). }
exists v0. split; [exact Rv0|]. split.
+ replace (spZ regs - 65) with (spZ regs - 65 + 0) by lia. rewrite Hcp by lia. rewrite HM by lia. exact Hv0.
+ unfold rfc_rdn in H7. cbn [nth] in H7. intros Hx. lia.
- destruct (proj2 Hstep Hnofit) as (Ec2 & Er2).
split; [rewrite Ec2; exact Wc3|]. split; [rewrite Er2; exact R10|].
exists fb. split; [exact Hfb|]. split.
+ rewrite (Hout3 (spZ regs - 65) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros [Hx _]; lia)), HM by lia. exact Bf.
+ intros _. apply Hfb0. left. lia. }
destruct HX as (Wc' & R' & f & Rf & N65 & Hf0).
apply SR_ret. unfold rfc_cut.
exists regs3, mem3, f, b0, b1, b2, b3, b4, b5.
split; [rewrite D1; reflexivity|].
split; [exact HJ3|].
split; [apply (s13_pres _ _ 2 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D2|].
split; [apply (s13_pres _ _ 3 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D3|].
split; [apply (s13_pres _ _ 4 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D4|].
split; [apply (s13_pres _ _ 8 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D8|].
split; [apply (s13_pres _ _ 9 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D9|].
split; [apply (s13_pres _ _ 18 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D18|].
split; [exact R'|].
split; [intros _; apply (s13_pres _ _ 19 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D19|].
split; [intros _; apply (s13_pres _ _ 20 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D20|].
split; [intros _; apply (s13_pres _ _ 21 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D21|].
split; [apply (s13_pres _ _ 22 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D22|].
split; [apply (s13_pres _ _ 23 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D23|].
split; [apply (s13_pres _ _ 24 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D24|].
split; [apply (s13_pres _ _ 25 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D25|].
split; [apply (s13_pres _ _ 26 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D26|].
split; [apply (s13_pres _ _ 27 _ _ HP3 ltac:(unfold callee_saved; lia) eq_refl); exact D27|].
split; [apply word_mem_frame with (m := mem1); [exact W22 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W21 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W20 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W19 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W18 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W9 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W8 | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact W1 | intros i Hi; apply Hk; lia]|].
split; [exact N65|].
split; [exact Rf|].
split; [intros [Hx|Hx]; [lia | apply Hf0; exact Hx]|].
split; [apply word_mem_frame with (m := mem1); [exact Wp | intros i Hi; apply Hk; lia]|].
split; [apply word_mem_frame with (m := mem1); [exact Wn | intros i Hi; apply Hk; lia]|].
split; [exact Wc'|].
split; [intros i Hi; rewrite Hk by lia; apply Z12; exact Hi|].
split.
{ unfold rhdr_bytes in Hhb |- *.
destruct Hhb as (H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23).
repeat match goal with |- _ /\ _ => split end; rewrite Hk by lia; assumption. }
split; [exact HB|].
intros a Ha Na1 Na2 Na3. rewrite Hk by lia. apply Hfr; assumption.
Qed.
Lemma sp_le0 : forall w k, le_byte 0 w k = 0.
Proof. intros w k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma sp_rhdr_frame : forall m m' dst b0 b1 b2 b3 b4 b5,
rhdr_bytes m dst b0 b1 b2 b3 b4 b5 ->
(forall i, 12 <= i < 24 -> mbyte ubs2segs m' (dst + i) = mbyte ubs2segs m (dst + i)) ->
rhdr_bytes m' dst b0 b1 b2 b3 b4 b5.
Proof.
intros m m' dst b0 b1 b2 b3 b4 b5 H Hf. unfold rhdr_bytes in *. rewrite !Hf by lia. exact H.
Qed.
Lemma rrfc_post_of_rimg : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur cur1 fb : Z) (mem1 : word -> option byte) (b0 b1 b2 b3 b4 b5 : Z) c',
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
rimg_post API regs STK sp0 FP L A mem md Bb st dst N nb cur1 fb mem1 c' ->
cur <= cur1 ->
word_mem ubs2segs mem1 st pdata -> word_mem ubs2segs mem1 (st + 8) nb ->
(forall i, 0 <= i < 12 -> mbyte ubs2segs mem1 (dst + i) = Some (Z_to_bv 8 0)) ->
rhdr_bytes mem1 dst b0 b1 b2 b3 b4 b5 -> bytes_ok [b0; b1; b2; b3; b4; b5] ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + RGBFC_SIZE) ->
~ (st + 16 <= a < st + 24) -> mbyte ubs2segs mem1 a = mbyte ubs2segs memc a) ->
rrfc_post API regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc c'.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur cur1 fb mem1 b0 b1 b2 b3 b4 b5 c'
Hh HP Hcc Wp Wn Z12 Hhb HB Hfr.
pose proof Hh as (HJ0 & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp0 & Wn0 & Wc0).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HDPv : RRFC_STK = 8272) by reflexivity. assert (HFCv : RGBFC_SIZE = 24) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HH.
pose proof HJ0 as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
unfold bytes_ok in HB.
repeat match type of HB with Forall _ (_ :: _) => apply Forall_cons_iff in HB as [?R HB] end.
destruct HP as (L2 & A2 & regs2 & mem2 & md2 & res & cur2 & img & Hc & HJ2 & Hid2 & HP2 & Ha0 & Hfr2 & Hbb2 & Wc2 & Hcur2 & ALT).
assert (Hres : 0 <= res < 2 ^ 64) by (destruct ALT as [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]; lia).
assert (Hhb2 : rhdr_bytes mem2 dst b0 b1 b2 b3 b4 b5).
{ eapply sp_rhdr_frame; [exact Hhb|]. intros i Hi. apply Hfr2; lia. }
exists L2, A2, regs2, mem2, md2, res, cur2.
split; [exact Hc|]. split; [exact HJ2|]. split; [exact Hid2|]. split; [exact HP2|]. split; [exact Ha0|]. split; [exact Hres|].
split.
{ intros a Ha Hn1 Hn2 Hn3. rewrite (Hfr2 a Ha Hn1) by lia. apply Hfr; lia. }
split.
{ intros b m i Hb Hi. rewrite (Hbb2 b m i Hb Hi).
assert (Hbc : In (b, m) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBc | exact Hb]).
destruct (heap_blocks _ _ LAWS Lc Ac memc mdc b m i HH Hbc Hi) as (_ & Hb0 & Hb1 & _).
apply Hfr; lia. }
split.
{ intros k Hk. rewrite (Hfr2 (st + Z.of_nat k)) by lia. apply Wp. exact Hk. }
split.
{ intros k Hk. rewrite (Hfr2 (st + 8 + Z.of_nat k)) by lia. apply Wn. exact Hk. }
split; [exact Wc2|]. split; [lia|].
destruct Hhb2 as (M12 & M13 & M14 & M15 & M16 & M17 & M18 & M19 & M20 & M21 & M22 & M23).
destruct ALT as [(Hok & -> & HB0 & Hd) | [(Hok & -> & HB0) | (Hok & -> & Wi & Ri & Vf & HB2)]].
- right. split; [lia|].
exists 0, 0, (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5).
split.
{ apply rgbfc_obj; try assumption; try lia.
- intros k Hk. rewrite (Hd (dst + Z.of_nat k)) by lia. rewrite sp_le0. apply Z12. lia.
- intros k Hk. rewrite (Hd (dst + 8 + Z.of_nat k)) by lia. rewrite sp_le0. rewrite <- Z.add_assoc. apply Z12. lia. }
split; [intros _; reflexivity|]. split; [lia|]. exact HB0.
- left. split; [reflexivity|exact HB0].
- right. split; [lia|].
pose proof (fmt_okb_true fb Hok) as Hfb.
exists img, fb, (b0 + 256 * b1), (b2 + 256 * b3), (b4 + 256 * b5).
split.
{ apply rgbfc_obj; try assumption; lia. }
split. { intros Hf. rewrite Hok in Hf. discriminate Hf. }
split; [exact Ri|].
unfold img_block. rewrite Hok. exact HB2.
Qed.
Lemma rfc_tail : forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) c,
rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur ->
rfc_cut 4 STK sp0 FP L A mem md Lc Ac memc mdc regs st dst N pdata nb cur c ->
SR ubs2segs c (rrfc_post API regs STK sp0 FP L A mem md Bb st dst N pdata nb cur memc).
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c Hh H4.
pose proof Hh as (HJ0 & Hid & Hbase & HBc & Hpd & Hra0 & Htp0 & G10 & G11 & G12 & Hal16 & Hwlo & Hst1 & Hst2 &
Hdst1 & Hdst2 & Hsd & Hst8 & Hdst8 & H63 & HN & Hcur & Hnb & Wp0 & Wn0 & Wc0).
destruct H4 as (regs1 & mem1 & fb & b0 & b1 & b2 & b3 & b4 & b5 & -> & HJ & G2 & G3 & G4 & G8 & G9 & G18 & Q10 &
G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & W22 & W21 & W20 & W19 & W18 & W9 & W8 & W1 &
Bf & Hfb & Hfb0 & Wp & Wn & Wc & Z12 & Hhb & HB & Hfr).
assert (Hc4 : cur <= rfc_cur cur nb 4 <= nb).
{ unfold rfc_cur, rfc_rdn. cbn [nth]. destruct (Z.leb_spec (cur + 7) nb); lia. }
change (Z_to_bv 64 (rfc_pc 4)) with (Z_to_bv 64 RR_MAL).
eapply SR_mono.
{ eapply (rfc_img API IMG STK sp0 FP L A mem md Lc Ac mdc regs regs1 mem1 Bb st dst N pdata nb (rfc_cur cur nb 4) fb);
try eassumption; try lia.
intros Hok. apply fmt_okb_true in Hok.
assert (H7 : cur + 7 <= nb).
{ destruct (Z_lt_le_dec nb (cur + 7)) as [Hl|Hl]; [|exact Hl]. specialize (Hfb0 (or_intror Hl)). lia. }
specialize (G19 ltac:(lia)). specialize (G20 ltac:(lia)). specialize (G21 ltac:(lia)).
unfold rfc_res, rfc_rdn in Q10, G19, G20, G21. cbn [nth] in Q10, G19, G20, G21.
rewrite (proj2 (Z.leb_le (cur + 2) nb) ltac:(lia)) in G19.
rewrite (proj2 (Z.leb_le (cur + 4) nb) ltac:(lia)) in G20.
rewrite (proj2 (Z.leb_le (cur + 6) nb) ltac:(lia)) in G21.
rewrite (proj2 (Z.leb_le (cur + 7) nb) ltac:(lia)) in Q10.
exact (conj G19 (conj G20 (conj G21 Q10))). }
intros c' Hp.
exact (rrfc_post_of_rimg STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur (rfc_cur cur nb 4) fb mem1
b0 b1 b2 b3 b4 b5 c' Hh Hp (proj1 Hc4) Wp Wn Z12 Hhb HB Hfr).
Qed.
Theorem ubs2_read_frameconfig : rrfc_spec API.
Proof.
unfold rrfc_spec.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur
HJ Hid Hbase HBc Hpd Hra0 Htp0 G10 G11 G12 Hal16 Hwlo Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 H63 HN Hcur Hnb Wp Wn Wc.
assert (Hh : rrfc_hyps STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur).
{ unfold rrfc_hyps. repeat (split; [assumption|]). assumption. }
eapply SR_bind; [exact (rfc_seg0 STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur Hh)|].
intros c1 H1.
eapply SR_bind; [exact (rfc_seg1 STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c1 Hh H1)|].
intros c2 H2.
eapply SR_bind; [exact (rfc_seg2 STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c2 Hh H2)|].
intros c3 H3.
eapply SR_bind; [exact (rfc_seg3 STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c3 Hh H3)|].
intros c4 H4.
exact (rfc_tail STK sp0 FP L A mem md Lc Ac memc mdc regs Bb st dst N pdata nb cur c4 Hh H4).
Qed.
End S.
End f.
