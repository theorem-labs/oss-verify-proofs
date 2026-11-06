(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YA0j.v (donor image sha256 1c29845fe605), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK18 YK00 YK04 YK05 YK0g YK08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0c YK0e YK0f YA0i YA0n YP09. From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YK09 YA0c YA0e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Definition kn_mem (K : kentry) (cs : acs) : bool := existsb (kentry_eqb K) (kn cs).
Lemma kn_mem_In : forall K cs, kn_mem K cs = true -> In K (kn cs).
Proof.
intros K cs H. unfold kn_mem in H. apply existsb_exists in H as [K' [Hin Heq]].
apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.
Definition kn_read (segs : list Segment) (cs : acs) (rb : expr) (rk : Z) (n : nat) : option expr :=
if ((1 <=? n)%nat && (n <=? 8)%nat && flat_x (kn cs) rb rk (ELit (Z.of_nat n)))%bool then
match know_lookup segs (kn cs) rb rk n false [] [] with
| LHit v [] _ => Some v
| _ => None
end
else None.
Definition kn_zero (cs : acs) (rb : expr) (rk : Z) (len : Z) : bool := kzero_x (kn cs) (kn cs) rb rk (ELit len).
Definition kn_vis (A : atable) (cs : acs) (rb : expr) (rk : Z) (len : Z) : bool := kunk_covered A (kn cs) (KUnk (SA rb rk) (ELit len)).
Lemma kunk_covered_len : forall A k rb rk len, kunk_covered A k (KUnk (SA rb rk) (ELit len)) = true -> 0 < len <= 2 ^ 40.
Proof.
intros A k rb rk len H. unfold kunk_covered in H.
apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. lia.
Qed.
Fixpoint zcover1 (bss : Z * Z) (k : list kentry) (b : expr) (i : Z) : option Z :=
match k with
| [] => None
| K :: rest =>
let hit := match K with
| KWord (SA kb kk) w (ELit 0) =>
if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
| KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) 0 =>
if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
| KImg lo hi =>
if (expr_eqb b (ELit 0) && Z.leb lo i && Z.ltb i hi && Z.leb (fst bss) i && Z.ltb i (snd bss))%bool
then Some (Z.min hi (snd bss)) else None
| _ => None
end in
match hit with Some e => Some e | None => zcover1 bss rest b i end
end.
Fixpoint zcover (bss : Z * Z) (fuel : nat) (k : list kentry) (b : expr) (i stop : Z) : bool :=
match fuel with
| O => false
| Datatypes.S f => if Z.leb stop i then true else
match zcover1 bss k b i with
| Some e => if Z.ltb i e then zcover bss f k b e stop else false
| None => false
end
end.
Definition kn_zcover (bss : Z * Z) (cs : acs) (rb : expr) (rk : Z) (len : Z) : bool :=
(flat_x (kn cs) rb rk (ELit len) && zcover bss (Datatypes.S (length (kn cs))) (kn cs) rb rk (rk + len))%bool.
Definition kn_img (cs : acs) (a len : Z) : bool :=
existsb (fun K => match K with KImg lo hi => ((lo <=? a) && (a + len <=? hi))%bool | _ => false end) (kn cs).
Definition hreader (segs : list Segment) (M : word -> option byte) (a : Z) : option Z :=
option_map (fun b : byte => bv_unsigned b) (mbyte segs M a).
Lemma hreader_rom : forall segs M a, seg_rom segs (Z_to_bv 64 a) <> None -> hreader segs M a <> None.
Proof.
intros segs M a H. unfold hreader, mbyte. destruct (M (Z_to_bv 64 a)); [discriminate|].
destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | exfalso; exact (H eq_refl)].
Qed.
Lemma hreader_rom_val : forall segs M a b, M (Z_to_bv 64 a) = None -> seg_rom segs (Z_to_bv 64 a) = Some b ->
hreader segs M a = Some (bv_unsigned b).
Proof. intros segs M a b HM Hb. unfold hreader, mbyte. rewrite HM, Hb. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma nth_error_le_byte : forall bs k (b : byte),
nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite bytes_le_to_Z_cons. pose proof (u8_range b0) as Hb0. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
rewrite <- Z.div_div by lia. f_equal. f_equal.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma Z_to_le_bytes_0 : forall n, Z_to_le_bytes n 0 = repeat (Z_to_bv 8 0) n.
Proof. induction n as [|n IHn]; [reflexivity|]. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l, IHn. reflexivity. Qed.
Lemma word_to_le_bytes_zero : forall w k (b : byte),
nth_error (word_to_le_bytes w (Z_to_bv 64 0)) k = Some b -> bv_unsigned b = 0.
Proof.
intros w k b H. unfold word_to_le_bytes in H. rewrite u64_lit in H by lia. rewrite Z_to_le_bytes_0 in H.
apply nth_error_In in H. apply repeat_spec in H. subst b. reflexivity.
Qed.
Lemma word_to_le_bytes_length : forall w v, length (word_to_le_bytes w v) = w.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.
Section g. Context {fx : YK11.FPState}.
Section h.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable TOP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis TOP_ok : top_ok TOP.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> TOP <= bv_unsigned a.
Variable E : env.
Variable ch : acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable model : Model.
Hypothesis HC : cs_ok SEGS A LIMIT TOP SINV argH FS0 E ch R FULL model.
#[local] Notation MR := (Mr A TOP argH E ch model FULL).
#[local] Notation HID := (hid A TOP argH E ch model).
Lemma ho_halted : m_halted model = None.
Proof. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_fs : m_fs model = FS0.
Proof. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_fds_std : a_fd ch = FdStd -> m_fds model = fds_std.
Proof. intros H. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ _ HC) as X. rewrite H in X. exact X. Qed.
Lemma ho_tid : a_tidset ch = false -> m_tid model = None.
Proof. exact (co_tid _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_res : vm_reserved (m_vmmaps model) = segments_reserved SEGS.
Proof. exact (co_res _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_limit : vm_limit (m_vmmaps model) = LIMIT.
Proof. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_brk : vm_brk (m_vmmaps model) = edenot E (a_brk ch).
Proof. exact (co_brk _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_sbrk : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model)).
Proof. exact (co_sbrk _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_minv : MInv (allowA A E ch) model.
Proof. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_abytes : A_bytes (allowA A E ch) <= a_abytes ch.
Proof. exact (co_abytes _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_eager : eager_used model <= a_eager ch.
Proof. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_maps : maps_match E (a_maps ch) (vm_maps (m_vmmaps model)).
Proof. exact (co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_seps : seps (vm_maps (m_vmmaps model)).
Proof. exact (co_seps _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_wf : model_ivs_wf model.
Proof. exact (co_wf _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
/\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
/\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TOP) (vm_maps (m_vmmaps model)).
Proof. exact (co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_lazyb : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TOP) (m_vm_lazy model).
Proof. exact (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_top : alloc_top (m_vmmaps model) = TOP.
Proof. exact (co_top _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true.
Proof. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_napos : Forall (fun iv => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps model)).
Proof. exact (co_napos _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_none : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps ch).
Proof. exact (co_none _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_kinds : Forall (fun m => am_kind m = KRWLAZY ->
forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps ch).
Proof. exact (co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz ch.
Proof. exact (co_totsz _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_zero : forall a : word, HID a = true ->
in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
page_in_ranges (page_base a) (m_vm_lazy model) = true ->
in_ghost E ch (bv_unsigned a) = false ->
FULL a = Some (Z_to_bv 8 0).
Proof. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_sinv : SINV E FULL.
Proof. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_lazy_cover : lazy_cover HID (m_vm_lazy model) (allowA A E ch).
Proof.
exact (lazy_cover_cs SEGS A LIMIT TOP (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
TOP_ok HULL_ok SINV argH FS0 0%nat E ch R FULL model HC).
Qed.
Lemma ho_A_wf : A_wf (allowA A E ch).
Proof. exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E ch). Qed.
Lemma ho_reg : forall r : Prelude.reg, getr R r = edenot E (sr_get (s_regs (a_ss ch)) r).
Proof. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_reg_lit : forall (r : Prelude.reg) z, sr_get (s_regs (a_ss ch)) r = ELit z -> getr R r = Z_to_bv 64 z.
Proof. intros r z H. rewrite ho_reg, H. reflexivity. Qed.
Lemma ho_reg_idx : forall r : Prelude.reg, bv_eqb r 0 = false -> getr R r = edenot E (reg ch (ridx r)).
Proof. intros r Hr. rewrite ho_reg. unfold sr_get, reg. rewrite Hr. reflexivity. Qed.
Lemma ho_know : know_ok SEGS E MR (kn ch).
Proof. exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.
Lemma ho_kn : forall K, kn_mem K ch = true -> kentry_ok SEGS E MR K.
Proof. intros K H. exact (proj1 (Forall_forall _ _) ho_know K (kn_mem_In K ch H)). Qed.
Lemma ho_word : forall a w v, kn_mem (KWord a w v) ch = true ->
(w <= 8)%nat /\ rdn SEGS MR (adenot E a) w = Some (word_to_le_bytes w (edenot E v)).
Proof. intros a w v H. destruct (ho_kn _ H) as (H1 & _ & H3). exact (conj H1 H3). Qed.
Lemma ho_zero_at : forall a n, kn_mem (KZero a n) ch = true ->
forall i, 0 <= i < elenZ E n -> MR (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0).
Proof. intros a n H. destruct (ho_kn _ H) as [_ H2]. exact H2. Qed.
Lemma ho_fill_at : forall a n c, kn_mem (KFill a n c) ch = true ->
forall i, 0 <= i < elenZ E n -> MR (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 c).
Proof. intros a n c H. destruct (ho_kn _ H) as [_ H2]. exact H2. Qed.
Lemma ho_unk_at : forall a n, kn_mem (KUnk a n) ch = true ->
forall i, 0 <= i < elenZ E n -> MR (Z_to_bv 64 (estart E a + i)) <> None.
Proof. intros a n H. destruct (ho_kn _ H) as [_ H2]. exact H2. Qed.
Lemma ho_img_at : forall lo hi, kn_mem (KImg lo hi) ch = true ->
forall i, lo <= i < hi -> MR (Z_to_bv 64 i) = None.
Proof. intros lo hi H. destruct (ho_kn _ H) as (_ & _ & H3). exact H3. Qed.
Lemma ho_range : forall e lo hi, kn_mem (KRange e lo hi) ch = true -> lo <= uE E e <= hi.
Proof. intros e lo hi H. destruct (ho_kn _ H) as [H1 H2]. unfold uE. split; assumption. Qed.
Lemma ho_align : forall e m, kn_mem (KAlign e m) ch = true -> 0 < m /\ uE E e mod m = 0.
Proof. intros e m H. destruct (ho_kn _ H) as [H1 H2]. unfold uE. split; assumption. Qed.
Lemma ho_wr : forall a n, kn_mem (KWr a n) ch = true ->
forall d m, 0 <= d -> d + Z.of_nat m <= elenZ E n -> RiscvSemantics.store_ok SEGS MR (Z_to_bv 64 (estart E a + d)) m = true.
Proof. intros a n H. destruct (ho_kn _ H) as [_ H2]. exact H2. Qed.
Lemma ho_disj : forall a1 n1 a2 n2, kn_mem (KDisj a1 n1 a2 n2) ch = true ->
estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1.
Proof. intros a1 n1 a2 n2 H. exact (ho_kn _ H). Qed.
Lemma ho_read : forall rb rk n v, kn_read SEGS ch rb rk n = Some v ->
exists bs, rdn SEGS MR (adenot E (SA rb rk)) n = Some bs /\ length bs = n
/\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
intros rb rk n v H. unfold kn_read in H.
destruct (((1 <=? n)%nat && (n <=? 8)%nat && flat_x (kn ch) rb rk (ELit (Z.of_nat n)))%bool) eqn:Hg; [|discriminate H].
apply andb_prop in Hg as [Hg Hfl]. apply andb_prop in Hg as [Hn1 Hn8].
apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
pose proof (know_lookup_sound SEGS E MR (kn ch) rb rk n false [] [] ho_know Hn1 Hn8) as X.
destruct (know_lookup SEGS (kn ch) rb rk n false [] []) as [v' scs hints | | ]; try discriminate H.
destruct scs; [|discriminate H]. injection H as ->.
destruct X as (bs & Hr & Hl & Hv).
- constructor.
- destruct (flat_x_sound SEGS E MR (kn ch) rb rk (ELit (Z.of_nat n)) ho_know Hfl) as (F1 & F2 & F3).
cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia. unfold flat. lia.
- exists bs. cbn [extz] in Hv. exact (conj Hr (conj Hl Hv)).
Qed.
Lemma ho_read_lit : forall a n z, kn_read SEGS ch (ELit 0) a n = Some (ELit z) ->
exists bs, rdn SEGS MR (Z_to_bv 64 a) n = Some bs /\ length bs = n /\ Z_to_bv 64 (bytes_le_to_Z bs) = Z_to_bv 64 z.
Proof.
intros a n z H. destruct (ho_read (ELit 0) a n (ELit z) H) as (bs & Hr & Hl & Hv).
exists bs. split; [|exact (conj Hl Hv)].
replace (adenot E (SA (ELit 0) a)) with (Z_to_bv 64 a : word) in Hr; [exact Hr|].
unfold adenot, v_addi. cbn [a_base a_off edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned. cbn. rewrite ?bv_wrap64_mod.
rewrite Zplus_mod_idemp_l || reflexivity. reflexivity.
Qed.
Lemma kn_read_le8 : forall rb rk n v, kn_read SEGS ch rb rk n = Some v -> (1 <= n <= 8)%nat.
Proof.
intros rb rk n v H. unfold kn_read in H.
destruct (((1 <=? n)%nat && (n <=? 8)%nat && flat_x (kn ch) rb rk (ELit (Z.of_nat n)))%bool) eqn:Hg; [|discriminate H].
apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [H1 H2]. apply Nat.leb_le in H1. apply Nat.leb_le in H2. lia.
Qed.
Lemma ho_read_byte : forall rb rk n v, kn_read SEGS ch rb rk n = Some v ->
forall k, (k < n)%nat -> hreader SEGS MR (uE E rb + rk + Z.of_nat k) = Some ((uE E v / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof.
intros rb rk n v H k Hk. pose proof (kn_read_le8 _ _ _ _ H) as Hn.
destruct (ho_read rb rk n v H) as (bs & Hr & Hl & Hv).
assert (Ea : adenot E (SA rb rk) = Z_to_bv 64 (uE E rb + rk)) by reflexivity. rewrite Ea in Hr.
apply (proj1 (rdn_mbytes SEGS MR n (uE E rb + rk) bs)) in Hr as [_ Hb].
unfold hreader. rewrite (Hb k Hk).
destruct (nth_error bs k) as [b|] eqn:En; [|exfalso; apply nth_error_None in En; lia].
cbn [option_map]. f_equal. rewrite (nth_error_le_byte bs k b En). f_equal. f_equal.
pose proof (bytes_le_to_Z_bound bs) as Hbd. pose proof (bytes_le_to_Z_nonneg bs) as Hnn. rewrite Hl in Hbd.
assert (Hbd' : bytes_le_to_Z bs < 2 ^ 64).
{ eapply Z.lt_le_trans; [apply (proj2 Hbd) | apply Z.pow_le_mono_r; lia]. }
apply (f_equal bv_unsigned) in Hv. rewrite u64_lit in Hv by lia. exact Hv.
Qed.
Lemma ho_read_bound : forall rb rk n v, kn_read SEGS ch rb rk n = Some v -> 0 <= uE E v < 2 ^ (8 * Z.of_nat n).
Proof.
intros rb rk n v H. pose proof (kn_read_le8 _ _ _ _ H) as Hn.
destruct (ho_read rb rk n v H) as (bs & _ & Hl & Hv).
pose proof (bytes_le_to_Z_bound bs) as Hbd. pose proof (bytes_le_to_Z_nonneg bs) as Hnn. rewrite Hl in Hbd.
assert (Hbd' : bytes_le_to_Z bs < 2 ^ 64).
{ eapply Z.lt_le_trans; [apply (proj2 Hbd) | apply Z.pow_le_mono_r; lia]. }
apply (f_equal bv_unsigned) in Hv. rewrite u64_lit in Hv by lia. unfold uE. rewrite <- Hv. lia.
Qed.
Lemma ho_zero_range : forall rb rk len, 0 <= len < 2 ^ 64 -> kn_zero ch rb rk len = true ->
forall i, 0 <= i < len -> hreader SEGS MR (uE E rb + rk + i) = Some 0.
Proof.
intros rb rk len Hlen H i Hi. unfold kn_zero in H.
destruct (kzero_x_sound0 SEGS E MR (kn ch) (kn ch) rb rk (ELit len) ho_know ho_know H) as (Hz & _ & _).
unfold hreader, mbyte. unfold elenZ in Hz. cbn [edenot] in Hz. rewrite u64_lit in Hz by lia.
unfold estart in Hz. cbn [a_base a_off] in Hz. fold (uE E rb) in Hz. rewrite (Hz i Hi). reflexivity.
Qed.
Lemma ho_vis_range : forall rb rk len, kn_vis A ch rb rk len = true ->
forall i, 0 <= i < len -> hreader SEGS MR (uE E rb + rk + i) <> None.
Proof.
intros rb rk len H i Hi. unfold kn_vis in H.
pose proof (kunk_covered_sound SEGS A SEGS_in_hull HULL_ok E MR (kn ch) _ ho_know H) as [_ Hu].
unfold elenZ in Hu. cbn [edenot] in Hu. rewrite u64_lit in Hu by (pose proof (kunk_covered_len _ _ _ _ _ H); lia).
unfold hreader, mbyte. unfold estart in Hu. cbn [a_base a_off] in Hu. fold (uE E rb) in Hu.
specialize (Hu i Hi). destruct (MR (Z_to_bv 64 (uE E rb + rk + i))); [discriminate | exfalso; apply Hu; reflexivity].
Qed.
Variable BSS : Z * Z.
Hypothesis IMG0 : forall x, fst BSS <= x < snd BSS -> seg_rom SEGS (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Lemma zcover1_sound : forall k b i e, Forall (kentry_ok SEGS E MR) k -> zcover1 BSS k b i = Some e ->
i < e /\ forall j, i <= j < e -> hreader SEGS MR (uE E b + j) = Some 0.
Proof.
induction k as [|K rest IHk]; intros b i e Hk H; [discriminate H|].
inversion Hk as [|K' rest' HK Hrest]; subst.
assert (REST : zcover1 BSS rest b i = Some e -> i < e /\ forall j, i <= j < e -> hreader SEGS MR (uE E b + j) = Some 0)
by (intros H'; exact (IHk b i e Hrest H')).
cbn [zcover1] in H.
destruct K as [[kb kk] w v|[kb kk] n| |lo hi| | | | |[kb kk] n c|]; try (apply REST; exact H).
-
destruct v as [z| | | | | | |]; try (apply REST; exact H).
destruct z as [|pz|nz]; try (apply REST; exact H).
destruct (expr_eqb b kb && (kk <=? i) && (i <? kk + Z.of_nat w))%bool eqn:Eb; [|apply REST; exact H]. injection H as <-.
apply andb_prop in Eb as [Eb E3]. apply andb_prop in Eb as [E1 E2]. apply expr_eqb_eq in E1. subst kb.
apply Z.leb_le in E2. apply Z.ltb_lt in E3. split; [lia|]. intros j Hj.
destruct HK as (Hw & Hfl & Hrd). cbn [edenot] in Hrd.
assert (Ea : adenot E (SA b kk) = Z_to_bv 64 (uE E b + kk)) by reflexivity. rewrite Ea in Hrd.
apply (proj1 (rdn_mbytes SEGS MR w (uE E b + kk) _)) in Hrd as [Hl Hb].
specialize (Hb (Z.to_nat (j - kk)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia.
replace (uE E b + kk + (j - kk)) with (uE E b + j) in Hb by lia.
unfold hreader. rewrite Hb.
destruct (nth_error (word_to_le_bytes w (Z_to_bv 64 0)) (Z.to_nat (j - kk))) as [bb|] eqn:En.
+ cbn [option_map]. f_equal. exact (word_to_le_bytes_zero _ _ _ En).
+ exfalso. apply nth_error_None in En. rewrite word_to_le_bytes_length in En. lia.
-
destruct n as [l| | | | | | |]; try (apply REST; exact H).
destruct (expr_eqb b kb && (0 <=? l) && (l <? two64) && (kk <=? i) && (i <? kk + l))%bool eqn:Eb; [|apply REST; exact H]. injection H as <-.
apply andb_prop in Eb as [Eb E5]. apply andb_prop in Eb as [Eb E4]. apply andb_prop in Eb as [Eb E3]. apply andb_prop in Eb as [E1 E2].
apply expr_eqb_eq in E1. subst kb. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply Z.leb_le in E4. apply Z.ltb_lt in E5.
split; [lia|]. intros j Hj. destruct HK as [Hfl Hz]. unfold elenZ in Hz. cbn [edenot] in Hz. unfold two64 in E3. rewrite u64_lit in Hz by lia.
unfold estart in Hz. cbn [a_base a_off] in Hz. fold (uE E b) in Hz.
unfold hreader, mbyte. replace (uE E b + j) with (uE E b + kk + (j - kk)) by lia. rewrite (Hz (j - kk)) by lia. reflexivity.
-
destruct (expr_eqb b (ELit 0) && (lo <=? i) && (i <? hi) && (fst BSS <=? i) && (i <? snd BSS))%bool eqn:Eb; [|apply REST; exact H].
injection H as <-.
apply andb_prop in Eb as [Eb E5]. apply andb_prop in Eb as [Eb E4]. apply andb_prop in Eb as [Eb E3]. apply andb_prop in Eb as [E1 E2].
apply expr_eqb_eq in E1. subst b. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply Z.leb_le in E4. apply Z.ltb_lt in E5.
split; [lia|]. intros j Hj. destruct HK as (_ & _ & Hnone).
unfold hreader, mbyte. unfold uE. rewrite edenot_lit, u64_lit by lia. rewrite Z.add_0_l.
rewrite (Hnone j) by lia. rewrite (IMG0 j) by lia. reflexivity.
-
destruct n as [l| | | | | | |]; try (apply REST; exact H). destruct c as [|pc|nc]; try (apply REST; exact H).
destruct (expr_eqb b kb && (0 <=? l) && (l <? two64) && (kk <=? i) && (i <? kk + l))%bool eqn:Eb; [|apply REST; exact H]. injection H as <-.
apply andb_prop in Eb as [Eb E5]. apply andb_prop in Eb as [Eb E4]. apply andb_prop in Eb as [Eb E3]. apply andb_prop in Eb as [E1 E2].
apply expr_eqb_eq in E1. subst kb. apply Z.leb_le in E2. apply Z.ltb_lt in E3. apply Z.leb_le in E4. apply Z.ltb_lt in E5.
split; [lia|]. intros j Hj. destruct HK as [Hfl Hz]. unfold elenZ in Hz. cbn [edenot] in Hz. unfold two64 in E3. rewrite u64_lit in Hz by lia.
unfold estart in Hz. cbn [a_base a_off] in Hz. fold (uE E b) in Hz.
unfold hreader, mbyte. replace (uE E b + j) with (uE E b + kk + (j - kk)) by lia. rewrite (Hz (j - kk)) by lia. reflexivity.
Qed.
Lemma zcover_sound : forall fuel k b i stop, Forall (kentry_ok SEGS E MR) k -> zcover BSS fuel k b i stop = true ->
forall j, i <= j < stop -> hreader SEGS MR (uE E b + j) = Some 0.
Proof.
induction fuel as [|f IHf]; intros k b i stop Hk H j Hj; [discriminate H|].
cbn [zcover] in H. destruct (stop <=? i) eqn:Es; [apply Z.leb_le in Es; lia|].
destruct (zcover1 BSS k b i) as [e|] eqn:E1; [|discriminate H]. destruct (i <? e) eqn:Ei; [|discriminate H].
destruct (zcover1_sound k b i e Hk E1) as [_ Hz].
destruct (Z.lt_ge_cases j e) as [Hlt|Hge]; [apply Hz; lia | eapply IHf; [exact Hk | exact H | lia]].
Qed.
Lemma ho_zcover_range : forall rb rk len, kn_zcover BSS ch rb rk len = true ->
forall i, 0 <= i < len -> hreader SEGS MR (uE E rb + rk + i) = Some 0.
Proof.
intros rb rk len H i Hi. unfold kn_zcover in H. apply andb_prop in H as [_ H].
rewrite <- Z.add_assoc. eapply zcover_sound; [exact ho_know | exact H | lia].
Qed.
Lemma ho_img_byte : forall a len, kn_img ch a len = true ->
forall x, a <= x < a + len -> hreader SEGS MR x = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x)).
Proof.
intros a len H x Hx. unfold kn_img in H. apply existsb_exists in H as (K & Hin & HK).
destruct K as [| | |lo hi| | | | | |]; try discriminate HK. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (proj1 (Forall_forall _ _) ho_know _ Hin) as (_ & _ & Hnone).
unfold hreader, mbyte. rewrite (Hnone x) by lia. reflexivity.
Qed.
Lemma Mr_is_mrestrict : MR = mrestrict HID FULL.
Proof. reflexivity. Qed.
Lemma ho_Mr_full : forall a b, MR a = Some b -> FULL a = Some b.
Proof. intros a b. unfold Mr, mrestrict. destruct (HID a); [discriminate | exact (fun H => H)]. Qed.
Lemma ho_Mr_visible : forall a, HID a = false -> MR a = FULL a.
Proof. intros a Ha. unfold Mr, mrestrict. rewrite Ha. reflexivity. Qed.
Lemma ho_hid_hull : forall a : word, in_hull A (bv_unsigned a) = true -> HID a = false.
Proof.
intros a Ha. unfold hid. destruct (argH E a) eqn:HaH.
- exfalso. pose proof (argH_high E a HaH) as Hc. unfold in_hull in Ha. apply andb_prop in Ha as [_ Ha].
apply Z.ltb_lt in Ha. destruct HULL_ok as (_ & _ & _ & Hk). pose proof TOP_ok as HT; unfold top_ok in HT. unfold KHI, CEIL in *. lia.
- cbn [orb]. unfold vis. rewrite Ha. reflexivity.
Qed.
Lemma ho_hid_high : forall a : word, TOP <= bv_unsigned a -> argH E a = false -> HID a = false.
Proof.
intros a Ha HaH. unfold hid. rewrite HaH. cbn [orb]. unfold vis.
rewrite (proj2 (Z.leb_le _ _) Ha). rewrite orb_true_r. reflexivity.
Qed.
Lemma ho_hid_off : forall a : word, HID a = true -> find_segment SEGS (bv_unsigned a) 1 = None.
Proof.
intros a H. apply SEGS_in_hull. destruct (in_hull A (bv_unsigned a)) eqn:Hh; [|reflexivity].
rewrite (ho_hid_hull a Hh) in H. discriminate H.
Qed.
Lemma ho_H_off : H_off_segments SEGS HID.
Proof. exact ho_hid_off. Qed.
Lemma ho_AI : AI SEGS HID (allowA A E ch) model.
Proof.
split; [exact ho_H_off|]. split; [exact ho_A_wf|]. split; [exact ho_lazy_cover|]. split; [exact ho_minv | exact ho_halted].
Qed.
Lemma seg_rom_none_of_find : forall a : word, find_segment SEGS (bv_unsigned a) 1 = None -> seg_rom SEGS a = None.
Proof. intros a H. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.
Lemma rdn_mrestrict_full : forall (H0 : word -> bool) (m : word -> option byte),
(forall a : word, H0 a = true -> seg_rom SEGS a = None) ->
forall n (a : word) bs, rdn SEGS (mrestrict H0 m) a n = Some bs -> rdn SEGS m a n = Some bs.
Proof.
intros H0 m Hoff. induction n as [|n IH]; intros a bs Hr; [exact Hr|].
cbn [rdn] in Hr |- *.
assert (E1 : mrestrict H0 m a = if H0 a then None else m a) by reflexivity.
rewrite E1 in Hr. destruct (H0 a) eqn:Ha.
- rewrite (Hoff a Ha) in Hr. discriminate Hr.
- destruct (m a) as [b|].
+ destruct (rdn SEGS (mrestrict H0 m) (a + 1) n) as [rest|] eqn:Hn; [|discriminate Hr].
rewrite (IH _ _ Hn). exact Hr.
+ destruct (seg_rom SEGS a) as [b|]; [|discriminate Hr].
destruct (rdn SEGS (mrestrict H0 m) (a + 1) n) as [rest|] eqn:Hn; [|discriminate Hr].
rewrite (IH _ _ Hn). exact Hr.
Qed.
Lemma ho_rdn_full : forall n (a : word) bs, rdn SEGS MR a n = Some bs -> rdn SEGS FULL a n = Some bs.
Proof.
intros n a bs H. apply (rdn_mrestrict_full HID FULL); [|exact H].
intros x Hx. apply seg_rom_none_of_find. apply ho_hid_off. exact Hx.
Qed.
Lemma ho_word_full : forall a w v, kn_mem (KWord a w v) ch = true ->
rdn SEGS FULL (adenot E a) w = Some (word_to_le_bytes w (edenot E v)).
Proof. intros a w v H. apply ho_rdn_full. exact (proj2 (ho_word a w v H)). Qed.
Definition ho_W : world SEGS := mkW SEGS HID (allowA A E ch) ho_H_off ho_A_wf.
Lemma ho_W_H : w_H ho_W = HID.  Proof. reflexivity. Qed.
Lemma ho_W_A : w_A ho_W = allowA A E ch.  Proof. reflexivity. Qed.
Lemma ho_start : forall (pc : word) (Q : world SEGS -> config -> Prop) (T : TSet),
SRr SEGS ho_W (mkCfg (mkst R pc FULL (seg_rom SEGS)) model) Q ->
(forall W' c', wle ho_W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') -> Q W' c' ->
srealizes SEGS c' T) ->
srealizes SEGS (mkCfg (mkst R pc FULL (seg_rom SEGS)) model) T.
Proof. intros pc Q T HS HK. exact (SRr_srealizes SEGS ho_W _ Q T HS ho_AI HK). Qed.
End h.
End g.
