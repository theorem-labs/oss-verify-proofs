(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI26 UO3n UI4v UI46 UI4g UI59.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma val_mem4 : forall (mem : word -> option byte) a,
present mem a -> present mem (a + 1) -> present mem (a + 2) -> present mem (a + 3) ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem ubs2segs mem a 4 v.
Proof.
intros mem a [b0 Hb0] [b1 Hb1] [b2 Hb2] [b3 Hb3].
pose proof (bv_unsigned_in_range _ b0) as Hr0. pose proof (bv_unsigned_in_range _ b1) as Hr1.
pose proof (bv_unsigned_in_range _ b2) as Hr2. pose proof (bv_unsigned_in_range _ b3) as Hr3.
change (bv_modulus 8) with 256 in Hr0, Hr1, Hr2, Hr3.
set (v := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
exists v. split; [subst v; lia|].
assert (Hm : v mod 2 ^ (8 * Z.of_nat 4) = v) by (apply Z.mod_small; change (2 ^ (8 * Z.of_nat 4)) with 4294967296; subst v; lia).
assert (BY : forall (k : nat) (b : byte) q, (k < 4)%nat -> mem (Z_to_bv 64 (a + Z.of_nat k)) = Some b -> 0 <= q ->
Z.shiftr v (8 * Z.of_nat k) = bv_unsigned b + 256 * q ->
mbyte ubs2segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 4 k))).
{ intros k b q Hk Hb Hq Hs. unfold mbyte. rewrite Hb. f_equal. unfold le_byte. rewrite Hm, Hs.
replace (bv_unsigned b + 256 * q) with (bv_unsigned b + q * 256) by lia. rewrite Z_mod_plus_full, Z.mod_small by (pose proof (bv_unsigned_in_range _ b) as Hb'; change (bv_modulus 8) with 256 in Hb'; lia).
symmetry. apply Z_to_bv_bv_unsigned. }
intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
- apply (BY 0%nat b0 (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))); [lia | rewrite Z.add_0_r; exact Hb0 | lia |].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. subst v. lia.
- apply (BY 1%nat b1 (bv_unsigned b2 + 256 * bv_unsigned b3)); [lia | exact Hb1 | lia |].
change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. subst v.
rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
- apply (BY 2%nat b2 (bv_unsigned b3)); [lia | exact Hb2 | lia |].
change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with (256 * 256). subst v.
replace (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))) with ((bv_unsigned b2 + 256 * bv_unsigned b3) * (256 * 256) + (bv_unsigned b0 + 256 * bv_unsigned b1)) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
- apply (BY 3%nat b3 0); [lia | exact Hb3 | lia |].
change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with (256 * 256 * 256). subst v.
replace (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))) with (bv_unsigned b3 * (256 * 256 * 256) + (bv_unsigned b0 + 256 * bv_unsigned b1 + 256 * 256 * bv_unsigned b2)) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma arr8_of_present : forall (mem : word -> option byte) base (n : nat),
(forall a, base <= a < base + Z.of_nat n -> present mem a) -> exists l, length l = n /\ arr8 ubs2segs mem base l.
Proof.
intros mem base n. revert base. induction n as [|n IH]; intros base Hp.
- exists []. split; [reflexivity|]. intros j Hj. cbn in Hj. lia.
- destruct (val_mem1 ubs2segs mem base) as (v & Hv & HV); [apply Hp; lia|].
destruct (IH (base + 1)) as (l & Hlen & Hl); [intros a Ha; apply Hp; lia|].
exists (v :: l). split; [cbn; lia|]. intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [| change (2 ^ 8) with 256 in Hv; lia].
specialize (HV 0%nat ltac:(lia)). cbn [Z.of_nat] in HV. rewrite Z.add_0_r in HV. rewrite HV. rewrite le_byte_small; [| exact Hv | lia].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
+ cbn [nth]. destruct (Hl j ltac:(cbn in Hj; lia)) as [Hb Hr]. split; [|exact Hr].
replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia. exact Hb.
Qed.
Lemma arr32_of_present : forall (mem : word -> option byte) base (n : nat),
(forall a, base <= a < base + 4 * Z.of_nat n -> present mem a) -> exists l, length l = n /\ arr32 ubs2segs mem base l.
Proof.
intros mem base n. revert base. induction n as [|n IH]; intros base Hp.
- exists []. split; [reflexivity|]. intros j Hj. cbn in Hj. lia.
- destruct (val_mem4 mem base) as (v & Hv & HV); [apply Hp; lia | apply Hp; lia | apply Hp; lia | apply Hp; lia |].
destruct (IH (base + 4)) as (l & Hlen & Hl); [intros a Ha; apply Hp; lia|].
exists (v :: l). split; [cbn; lia|]. intros [|j] Hj.
+ cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. split; [exact HV | exact Hv].
+ cbn [nth]. destruct (Hl j ltac:(cbn in Hj; lia)) as [Hb Hr]. split; [|exact Hr].
replace (base + 4 * Z.of_nat (S j)) with (base + 4 + 4 * Z.of_nat j) by lia. exact Hb.
Qed.
Lemma arr8_zeros : forall (mem : word -> option byte) base (n : nat),
(forall i, 0 <= i < Z.of_nat n -> mbyte ubs2segs mem (base + i) = Some (Z_to_bv 8 0)) -> arr8 ubs2segs mem base (repeat 0 n).
Proof.
intros mem base n Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia]. apply Hz. lia.
Qed.
Lemma obj_at_cht_set_px : forall (m m' : word -> option byte) c v0 v1 v2 v3 v4 v5 v6 v3' v4',
obj_at ubs2segs m c LAY_Cht [v0; v1; v2; v3; v4; v5; v6] ->
(forall a, c <= a < c + 48 -> ~ (c + 24 <= a < c + 40) -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
val_mem ubs2segs m' (c + 24) 8 v3' -> 0 <= v3' < 2 ^ 64 -> val_mem ubs2segs m' (c + 32) 8 v4' -> 0 <= v4' < 2 ^ 64 ->
obj_at ubs2segs m' c LAY_Cht [v0; v1; v2; v3'; v4'; v5; v6].
Proof.
intros m m' c v0 v1 v2 v3 v4 v5 v6 v3' v4' Hobj KEEP Hv3 Hr3 Hv4 Hr4.
cbn [obj_at LAY_Cht] in Hobj |- *. unfold field_ok in *. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobj |- *.
destruct Hobj as ([A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & _).
assert (K : forall off n v, val_mem ubs2segs m (c + off) n v -> 0 <= off -> (off + Z.of_nat n <= 24 \/ 40 <= off) -> off + Z.of_nat n <= 48 -> val_mem ubs2segs m' (c + off) n v).
{ intros off n v Hvm H0 H1 H2. apply (val_mem_kept m); [exact Hvm|]. intros k Hk. apply KEEP; lia. }
split; [split; [apply K; [exact A0 | lia | cbn; lia | cbn; lia] | exact B0]|].
split; [split; [apply K; [exact A1 | lia | cbn; lia | cbn; lia] | exact B1]|].
split; [split; [apply K; [exact A2 | lia | cbn; lia | cbn; lia] | exact B2]|].
split; [split; [exact Hv3 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr3]|].
split; [split; [exact Hv4 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr4]|].
split; [split; [apply K; [exact A5 | lia | cbn; lia | cbn; lia] | exact B5]|].
split; [split; [apply K; [exact A6 | lia | cbn; lia | cbn; lia] | exact B6]|]. exact I.
Qed.


Lemma arr8_bytes : forall (mem : word -> option byte) base l, arr8 ubs2segs mem base l -> Forall (fun v => 0 <= v < 256) l.
Proof.
intros mem base l Ha. apply Forall_nth. intros j d Hj. rewrite (nth_indep _ d 0 Hj). exact (proj2 (Ha j Hj)).
Qed.
Lemma lxor_ones_cmpl : forall u, 0 <= u < 2 ^ 64 -> (Z.lxor u (Z.ones 64)) mod 2 ^ 64 = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. transitivity (Z.lnot u mod 2 ^ 64).
- apply Z.bits_inj'. intros k Hk. destruct (Z.ltb_spec k 64) as [Hl|Hl].
+ rewrite !Z.mod_pow2_bits_low by exact Hl. rewrite Z.lxor_spec, Z.lnot_spec, Z.ones_spec_low by lia. destruct (Z.testbit u k); reflexivity.
+ rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
- unfold Z.lnot. replace (Z.pred (- u)) with ((2 ^ 64 - 1 - u) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_cmpl_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - x.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn Hx), U_SLit.
change (zcanon (-1)) with (Z.ones 64). unfold zcanon, M64. apply lxor_ones_cmpl. exact Hx.
Qed.
Lemma denot_cmpl_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof. intros E n x Hn Hx. rewrite denot_lit_U. f_equal. exact (U_cmpl_atom E n x Hn Hx). Qed.
Definition PC_RB : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x798).
Definition PC_P1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x910).   Definition PC_P2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x918).   Definition PC_P3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x920).
Section f.
Variable API : AllocAPI ubs2_msyms.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation RZ_MEM := (rz_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_BLOCKS := (rz_blocks r g bef beffmt s N img fmt rest).
Local Notation RZ_FACTS := (rz_facts N fmt).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Definition newb (T' p1 x1 h1 u1 f1 : Z) : list (Z * Z) := [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T'); (u1, T'); (f1, 4 * T')].
Definition s_regs (regs1 : bvmap 5 word) (i : Z) (C : cht) (T' h1 u1 f1 : Z) : Prop :=
rgba_regs regs0 regs1 /\ getr regs1 24 = Z_to_bv 64 h1 /\ getr regs1 25 = Z_to_bv 64 u1 /\ getr regs1 18 = Z_to_bv 64 T' /\
getr regs1 26 = Z_to_bv 64 f1 /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 9 = Z_to_bv 64 i /\ getr regs1 8 = Z_to_bv 64 r /\
getr regs1 21 = Z_to_bv 64 2.
Definition cmpl_slots (memc : word -> option byte) (h1 u1 f1 : Z) : Prop :=
slot regs0 memc 104 (2 ^ 64 - 1 - h1) /\ slot regs0 memc 96 (2 ^ 64 - 1 - u1) /\ slot regs0 memc 88 (2 ^ 64 - 1 - f1).
Definition at_MS (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
RZ_MEM memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\
obj_at ubs2segs memc (ch_c C) LAY_Cht [ch_f C; ch_hS C; ch_uS C; p1; x1; ht_cnt (ch_H C); ch_TS C] /\
(forall k, 0 <= k < T' -> mbyte ubs2segs memc (u1 + k) = Some (Z_to_bv 8 0)) /\
RZ_BLOCKS Lc Ac pnew fimg C (newb T' p1 x1 h1 u1 f1).
Definition loop_mem (memc : word -> option byte) (i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
RZ_MEM memc i ha pnew fimg imgl C /\ slot regs0 memc SL_72 ha /\ cmpl_slots memc h1 u1 f1 /\
cht_arrays ubs2segs memc f1 h1 u1 p1 x1 K /\ ht_T K = T' /\
obj_at ubs2segs memc (ch_c C) LAY_Cht [ch_f C; ch_hS C; ch_uS C; p1; x1; ht_cnt K; ch_TS C].
Definition reh_regs (regs1 : bvmap 5 word) (C : cht) (K : htab) (j : Z) : Prop :=
getr regs1 19 = Z_to_bv 64 j /\ getr regs1 27 = Z_to_bv 64 (4 * j) /\ getr regs1 22 = Z_to_bv 64 (3 * j) /\
getr regs1 10 = Z_to_bv 64 (ch_T C).
Definition at_REH (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\ reh_regs regs1 C K j /\
0 <= j < ch_T C /\ ht_inv K (ents_below (ch_H C) j) /\
loop_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\
RZ_BLOCKS Lc Ac pnew fimg C (newb T' p1 x1 h1 u1 f1).
Definition at_RB (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
getr regs1 19 = Z_to_bv 64 j /\ getr regs1 27 = Z_to_bv 64 (4 * j) /\ getr regs1 22 = Z_to_bv 64 (3 * j) /\
getr regs1 23 = Z_to_bv 64 (3 * j) /\
(exists hh, getr regs1 10 = Z_to_bv 64 hh /\ find_slot K (key (ch_H C) j) = Some hh /\ usedz K hh = 0) /\
0 <= j < ch_T C /\ usedz (ch_H C) j <> 0 /\ ht_inv K (ents_below (ch_H C) j) /\ ht_cnt K + 1 <= ht_cnt (ch_H C) /\
loop_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\
RZ_BLOCKS Lc Ac pnew fimg C (newb T' p1 x1 h1 u1 f1).
Definition at_POST (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
ht_inv K (ents_below (ch_H C) (ch_T C)) /\
loop_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\
RZ_BLOCKS Lc Ac pnew fimg C (newb T' p1 x1 h1 u1 f1).
Definition post_mem (memc : word -> option byte) (i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
slots_mid regs0 cfp N memc pnew fimg /\ slot regs0 memc SL_32 65280 /\ slot regs0 memc SL_40 fmt /\ slot regs0 memc SL_56 N /\
slot regs0 memc SL_64 1 /\ slot regs0 memc SL_80 (2 ^ 32 - 1) /\ slot regs0 memc SL_112 fmt /\ slot regs0 memc SL_120 img /\
slot regs0 memc SL_72 ha /\
fcfg_at regs0 fattr delay memc fimg 0 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\ cgif_at memc g s /\
img_at N img fmt memc imgl /\ pnew <> 0 /\ fimg <> 0 /\
cht_arrays ubs2segs memc f1 h1 u1 p1 x1 K /\ ht_T K = T' /\ In T' ts_chain /\ ht_inv K (ents_below (ch_H C) (ch_T C)) /\ ht_inv (ch_H C) (ch_ent C) /\
ht_T (ch_H C) = ch_T C /\ In (ch_T C) ts_chain /\
0 <= ch_hS C < 2 ^ 64 /\ 0 <= ch_uS C < 2 ^ 64 /\ 0 <= ch_TS C < 2 ^ 32 /\
ch_hS C = ch_h C /\ ch_uS C = ch_u C /\ zsum (map snd (ch_ent C)) <= i + 1.
Definition p_struct (memc : word -> option byte) (C : cht) (T' p1 x1 : Z) (K : htab) : Prop :=
obj_at ubs2segs memc (ch_c C) LAY_Cht [ch_f C; ch_hS C; ch_uS C; p1; x1; ht_cnt K; T'].
Definition at_P1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
post_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\ p_struct memc C T' p1 x1 K /\
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_u C, ch_T C)] ++ newb T' p1 x1 h1 u1 f1).
Definition at_P2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
post_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\ p_struct memc C T' p1 x1 K /\
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C)] ++ newb T' p1 x1 h1 u1 f1).
Definition at_P3 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ s_regs regs1 i C T' h1 u1 f1 /\
post_mem memc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K /\ p_struct memc C T' p1 x1 K /\
Permutation (blocks Lc Ac) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)] ++ newb T' p1 x1 h1 u1 f1).
End f.
Definition ss_C0 : sstate := mkSS PC_C0 sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 24 40 [] ] None
(mkFacts [] [] []).
Section h.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_C0 := (at_C0 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_MS := (at_MS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_REH := (at_REH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_LIVE := (rz_mem_live regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_ARRS := (rz_mem_arrs regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Section C0.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KMS : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_MS regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_MS) memc (seg_rom ubs2segs)) mdc) POST.
Theorem C0_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_C0 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_C0) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G9 & G20 & G8 & G21) & (G27 & G22 & G24 & G25 & G26 & G19) & Zp & Zx & Zh & Zu & Zf & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
unfold rz_blocks in RZB. fold (newb T' p1 x1 h1 u1 f1) in RZB.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
destruct (RNG p1 (3 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rp0 Rp1].
destruct (RNG x1 (4 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rx0 Rx1].
destruct (RNG u1 T' ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Ru0 Ru1].
assert (SEPc : forall y, In y (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> ch_c C + 48 <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X.
- unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; apply in_app_iff; left; exact Hy | right; exact Hy]. }
assert (SEPu : forall y, In y (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)]) -> u1 + T' <= fst y \/ fst y + snd y <= u1).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (u1, T') y (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T')]) [(f1, 4 * T')] HHc) as X.
cbn [fst snd] in X. apply X.
- unfold keepb, newb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. left. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; exact Hy | right; apply in_app_iff; right; apply in_app_iff; left; right; exact Hy]. }
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE27 : ew E 27 = Z_to_bv 64 p1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE22 : ew E 22 = Z_to_bv 64 x1) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_C0 (mkst regs1 (Z_to_bv 64 PC_C0) memc (seg_rom ubs2segs))).
{ unfold ss_C0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU20. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE o HHc ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia))).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- exact I. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_C0) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha |]; [| apply wr_ok_nil].
apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) (ch_c C) CHT_SIZE a HHc);
[| exact HB0 | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | unfold CHT_SIZE; lia | unfold CHT_SIZE; lia].
unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- ?app_assoc. exact RZB. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_c C + 24 <= a < ch_c C + 40) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hn2. mb_frame_g HF; [reflexivity | rewrite HU20; exact Hn2]. }
assert (V24 : val_mem ubs2segs (ms_mem ms) (ch_c C + 24) 8 p1).
{ apply (st_chunk_val_g E _ _ 0%nat _ 20%nat 24 8%N (SOff 27 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE27, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
assert (V32 : val_mem ubs2segs (ms_mem ms) (ch_c C + 32) 8 x1).
{ apply (st_chunk_val_g E _ _ 0%nat _ 20%nat 32 8%N (SOff 22 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | cbn [sv_denot]; rewrite Z.add_0_r, HE22, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
jreg HS (10%bv:reg) as Ma0. rewrite (HE 25%nat 25%bv eq_refl), G25 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. rewrite (HE 19%nat 19%bv eq_refl), G19 in Ma2. jreg HS (1%bv:reg) as Mra.
jreg HS (18%bv:reg) as M18. rewrite (HE 19%nat 19%bv eq_refl), G19 in M18.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 9; 20; 8; 21; 24; 25; 26]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
pose proof (proj1 HJ) as HHm.
eapply SR_bind.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E _ _ RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac _ u1 0 T');
[ exact HS | reflexivity | reflexivity | exact HJ | exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros k Hk. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac (ms_mem ms) mdc u1 T' k HHm ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) Hk)).
- intros a Ha. apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) u1 T' a HHc);
[| exact HB0 | apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10 | lia | lia].
unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- ?app_assoc. exact RZB. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
cbn [ms_regs ms_mem mkst] in HJ2, Hd10, Hfr2, Hout2, Hgr2, Hzero2.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (u1 <= a < u1 + T') -> mbyte ubs2segs mem2 a = mbyte ubs2segs (ms_mem ms) a).
{ intros a Ha Hna. unfold mbyte. rewrite (Hout2 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (RP : forall rr : reg, reg_in rr MEMSET_CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (Hfr2 rr Hrr)).
change (Z_to_bv 64 80228) with (Z_to_bv 64 PC_MS). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KMS regs2 Lc Ac mem2 mdc p1 x1 h1 u1 f1). unfold at_MS.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ2).
intros a Ha Hna. rewrite K2 by lia. apply K1; unfold sp, sp0 in *; lia. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity). rewrite M18.
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [first [assumption | reflexivity]|]). exact G21. }
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact Hz].
- intros a Ha Hs Hn1 Hn2. rewrite K2 by lia. apply K1; unfold sp, sp0 in *; lia.
- intros b n k Hb Hk. pose proof (SEPc (b, n) ltac:(apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; left; exact Hb])) as X1.
pose proof (SEPu (b, n) Hb) as X2. cbn [fst snd] in X1, X2.
assert (Hbn : In (b, n) (blocks Lc Ac)) by (apply INB; apply in_app_iff; left; apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hb).
destruct (RNG b n Hbn ltac:(lia)) as [Rb0 Rb1]. rewrite K2 by lia. apply K1; unfold sp, sp0 in *; lia. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. rewrite K2 by (unfold sp, sp0 in *; lia). apply K1; unfold sp, sp0 in *; lia. }
split. { unfold rz_struct in RZS. apply (obj_at_cht_set_px memc mem2 (ch_c C) _ _ _ _ _ _ _ p1 x1 RZS); [| | lia | | lia].
- intros a Ha Hna. pose proof (SEPu (ch_c C, CHT_SIZE)) as X.
clear X. pose proof (perm_sep API Lc Ac memc mdc (u1, T') (ch_c C, CHT_SIZE) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T')]) [(f1, 4 * T')] HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X.
rewrite K2; [apply K1; unfold sp, sp0 in *; lia | lia |].
assert (Hd : u1 + T' <= ch_c C \/ ch_c C + 48 <= u1); [apply X | lia].
+ unfold keepb, newb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
+ apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- apply (val_mem_kept (ms_mem ms)); [exact V24|]. intros k Hk. apply K2; [lia|].
pose proof (perm_sep API Lc Ac memc mdc (u1, T') (ch_c C, CHT_SIZE) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T')]) [(f1, 4 * T')] HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X.
assert (Hd : u1 + T' <= ch_c C \/ ch_c C + 48 <= u1); [apply X | lia].
+ unfold keepb, newb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
+ apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
- apply (val_mem_kept (ms_mem ms)); [exact V32|]. intros k Hk. apply K2; [lia|].
pose proof (perm_sep API Lc Ac memc mdc (u1, T') (ch_c C, CHT_SIZE) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T')]) [(f1, 4 * T')] HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X.
assert (Hd : u1 + T' <= ch_c C \/ ch_c C + 48 <= u1); [apply X | lia].
+ unfold keepb, newb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
+ apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
split; [intros k Hk; exact (Hzero2 k Hk)|].
exact RZB.
Qed.
End C0.
Section Ms.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KREH : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 K j, AT_REH regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K j ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom ubs2segs)) mdc) POST.
Definition ss_MS : sstate := mkSS PC_MS sr_atoms
[ YQ0b.mkRegion (Some 20%nat) 0 48 40 44 [mkChunk 44 (CVal 4 (SOff 32%nat 0))] ;
YQ0b.mkRegion (Some 2%nat) 88 112 88 112 [] ] None
(mkFacts [(32%nat, mkAF 521 (2^24) 0)] [] []).
Theorem MS_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_MS regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_MS) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & RZM & S72 & RZS & Hzero & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (RZ_MEM_LIVE _ _ _ _ _ _ _ RZM) as (EhS & EuS & ETS).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
set (T := ch_T C) in *.
unfold rz_blocks in RZB.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
destruct (RNG (ch_u C) T ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Ru0 Ru1].
destruct (RNG (ch_f C) (4 * T) ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rf0 Rf1].
destruct (RNG h1 (3 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rh10 Rh11].
destruct (RNG u1 T' ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Ru10 Ru11].
destruct (RNG f1 (4 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rf10 Rf11].
assert (SEPc : forall y, In y (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> ch_c C + 48 <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X.
- unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; apply in_app_iff; left; exact Hy | right; exact Hy]. }
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 6 _ _ RZS eq_refl eq_refl) as [B6 R6]. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B6, R6.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_TS C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_TS C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_MS (mkst regs1 (Z_to_bv 64 PC_MS) memc (seg_rom ubs2segs))).
{ unfold ss_MS. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
2:{ rewrite HU2. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|].
split; [intros o Ho; apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold sp, sp0, RGBA_FRAME in *; lia | constructor]. }
rewrite HU20. split; [lia|]. split; [lia|].
split. { intros o Ho. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE o HHc ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia))). }
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_TS C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by (rewrite ETS; lia); reflexivity | cbn; rewrite ETS; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B6.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU20, HU2. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE32, unsigned_lit_small by (rewrite ETS; lia). change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
rewrite ETS. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_MS) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ PC_REH.
{ eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha |];
[| eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; unfold sp, sp0, RGBA_FRAME in *; lia | apply wr_ok_nil]].
apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) (ch_c C) CHT_SIZE a HHc);
[| exact HB0 | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | unfold CHT_SIZE; lia | unfold CHT_SIZE; lia].
unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- ?app_assoc. exact RZB. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_c C + 40 <= a < ch_c C + 44) -> ~ (SP + 88 <= a < SP + 112) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hn2 Hn3. mb_frame_g HF; [reflexivity | rewrite HU20; exact Hn2 | rewrite HU2; exact Hn3]. }
pose proof (proj1 HJ) as HHm.
assert (KBL : forall b n k, In (b, n) (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> 0 <= k < n -> mbyte ubs2segs (ms_mem ms) (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b n k Hb Hk. pose proof (SEPc (b, n) Hb) as X1. cbn [fst snd] in X1.
assert (Hbn : In (b, n) (blocks Lc Ac)).
{ apply INB. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply (keepb_sub r g bef beffmt s N img fmt rest); apply in_app_iff; left; exact Hb |].
apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left; apply (keepb_sub r g bef beffmt s N img fmt rest); apply in_app_iff; right; exact Hb | right; exact Hb]. }
destruct (RNG b n Hbn ltac:(lia)) as [Rb0 Rb1]. apply K1; unfold sp, sp0 in *; lia. }
assert (PRES : forall b n a, In (b, n) (newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> present (ms_mem ms) a).
{ intros b n a Hb Ha. replace a with (b + (a - b)) by lia. apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac (ms_mem ms) mdc b n (a - b) HHm ltac:(apply INB; apply in_app_iff; right; exact Hb) ltac:(lia))). }
destruct (arr32_of_present (ms_mem ms) f1 (Z.to_nat T')) as (frN & LfrN & AfrN); [intros a Ha; apply (PRES f1 (4 * T')); [cbn; auto 10 | lia]|].
destruct (arr8_of_present (ms_mem ms) h1 (Z.to_nat (3 * T'))) as (keysN & LkN & AkN); [intros a Ha; apply (PRES h1 (3 * T')); [cbn; auto 10 | lia]|].
destruct (arr8_of_present (ms_mem ms) p1 (Z.to_nat (3 * T'))) as (palN & LpN & ApN); [intros a Ha; apply (PRES p1 (3 * T')); [cbn; auto 10 | lia]|].
destruct (arr32_of_present (ms_mem ms) x1 (Z.to_nat T')) as (cixN & LcN & AcN); [intros a Ha; apply (PRES x1 (4 * T')); [cbn; auto 10 | lia]|].
assert (AuN : arr8 ubs2segs (ms_mem ms) u1 (repeat 0 (Z.to_nat T'))).
{ apply arr8_zeros. intros k Hk. rewrite (KBL u1 T' k); [apply Hzero; lia | apply in_app_iff; right; cbn; auto 10 | lia]. }
set (K0 := mkHT frN keysN (repeat 0 (Z.to_nat T')) palN cixN 0 T').
assert (INV0 : ht_inv K0 (ents_below (ch_H C) 0)).
{ rewrite ents_below_0. subst K0. apply ht_empty_inv; [lia | unfold zlen; lia | unfold zlen; lia | unfold zlen; lia | unfold zlen; lia | exact (arr8_bytes _ _ _ AkN) | exact (arr8_bytes _ _ _ ApN)]. }
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80252) with (Z_to_bv 64 PC_REH).
apply (KREH (ms_regs ms) Lc Ac (ms_mem ms) mdc p1 x1 h1 u1 f1 K0 0). unfold at_REH.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ). intros a Ha Hna. apply K1; unfold sp, sp0 in *; lia. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { unfold reh_regs. rewrite !Z.mul_0_r.
split; [jreg HS (19%bv:reg) as Hq; exact Hq|].
split; [jreg HS (27%bv:reg) as Hq; exact Hq|].
split; [jreg HS (22%bv:reg) as Hq; exact Hq|].
jreg HS (10%bv:reg) as Hq; rewrite Hq, HE32, ETS; reflexivity. }
split; [lia|]. split; [exact INV0|].
split. { unfold loop_mem. split. { apply (RZ_MEM_KEPT Lc Ac memc (ms_mem ms) mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact Hz].
- intros a Ha Hs Hn1 Hn2. apply K1; unfold sp, sp0 in *; lia.
- intros b n k Hb Hk. apply (KBL b n k); [| exact Hk]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; left; exact Hb]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply K1; unfold sp, sp0 in *; lia. }
split. { unfold cmpl_slots, slot.
assert (HU2' : bv_unsigned (ew E 2) = SP) by exact HU2.
assert (W24 : ew E 24 = Z_to_bv 64 h1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (W25 : ew E 25 = Z_to_bv 64 u1) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (W26 : ew E 26 = Z_to_bv 64 f1) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
split; [|split].
- eapply (st_chunk_word _ _ _ 1%nat _ 2%nat 104 (SAlu ALU_XOR (SOff 24 0) (SLit (-1))) SP _ HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2'
| rewrite (denot_cmpl_atom E 24 h1 W24) by lia; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 2%nat 96 (SAlu ALU_XOR (SOff 25 0) (SLit (-1))) SP _ HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2'
| rewrite (denot_cmpl_atom E 25 u1 W25) by lia; reflexivity | lia].
- eapply (st_chunk_word _ _ _ 1%nat _ 2%nat 88 (SAlu ALU_XOR (SOff 26 0) (SLit (-1))) SP _ HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2'
| rewrite (denot_cmpl_atom E 26 f1 W26) by lia; reflexivity | lia]. }
split; [subst K0; unfold cht_arrays; cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx]; split; [exact AfrN | split; [exact AkN | split; [exact AuN | split; [exact ApN | exact AcN]]]]|].
split; [reflexivity|].
subst K0. cbn [ht_cnt]. apply (obj_at_cht_set_cnt memc (ms_mem ms) (ch_c C) _ _ _ _ _ (ht_cnt (ch_H C)) _ 0 RZS); [| | lia].
- intros a Ha Hna. apply K1; unfold sp, sp0 in *; lia.
- apply (st_chunk_val_g E _ _ 0%nat _ 20%nat 40 4%N (SLit 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | reflexivity | cbn; lia | cbn; lia]. }
exact RZB.
Qed.
End Ms.
End h.
End e.
