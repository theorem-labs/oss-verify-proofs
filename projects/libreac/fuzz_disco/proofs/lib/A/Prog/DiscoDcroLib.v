From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg DiscoRoClose.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition dz_in_b (p : Z * Z) (l : list (Z * Z)) : bool :=
  existsb (fun r => ((fst r =? fst p) && (snd r =? snd p))%bool) l.

Lemma dz_in : forall p l, dz_in_b p l = true -> In p l.
Proof.
intros [a n] l H. apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst q m. exact Hin.
Qed.

Definition drbn_ro_b (q sz : Z) : bool :=
  (dz_in_b (q, sz) disco_globs && ((sz mod 8 =? 0) || dz_in_b (q + sz, 8 - sz mod 8) disco_glob_tails))%bool.

Lemma d_rbn_ro : forall q sz, drbn_ro_b q sz = true -> rbn_ro q sz.
Proof.
intros q sz H. unfold drbn_ro_b in H. apply andb_prop in H as [H1 H2].
split; [exact (dz_in _ _ H1)|]. apply orb_true_iff in H2 as [H2|H2].
- left. apply Z.eqb_eq. exact H2.
- right. exact (dz_in _ _ H2).
Qed.

Definition dz_cov_b (a n : Z) (l : list (Z * Z)) : bool :=
  existsb (fun r => ((fst r <=? a) && (a + n <=? fst r + snd r))%bool) l.

Lemma dz_cov : forall a n l, dz_cov_b a n l = true -> exists q sz, In (q, sz) l /\ q <= a /\ a + n <= q + sz.
Proof.
intros a n l H. apply existsb_exists in H as ([q sz] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists q, sz. split; [exact Hin|]. split; [exact H1 | exact H2].
Qed.

Lemma d_in_globs : forall p, In p disco_globs -> In p disco_ro_ranges.
Proof. intros p H. unfold disco_ro_ranges. apply in_or_app. left. exact H. Qed.

Lemma d_in_extra : forall p, In p disco_ro_extra -> In p disco_ro_ranges.
Proof. intros p H. unfold disco_ro_ranges. apply in_or_app. right. exact H. Qed.

Lemma d_in_all : forall p, In p disco_ro_ranges -> In p disco_ro_all.
Proof. intros p H. unfold disco_ro_all. apply in_or_app. left. exact H. Qed.

Definition drom_b (a : Z) (l : list Z) : bool :=
  forallb (fun j => match seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat j)) with
                    | Some b => Z.eqb (bv_unsigned b) (nth j l 0)
                    | None => false
                    end) (seq 0 (length l)).

Lemma drom_at : forall a l j, drom_b a l = true -> (j < length l)%nat ->
  option_map (fun b : byte => bv_unsigned b) (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat j))) = Some (nth j l 0).
Proof.
intros a l j H Hj. pose proof (proj1 (forallb_forall _ _) H j ltac:(apply in_seq; lia)) as Hb. cbv beta in Hb.
destruct (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat j))) as [b|]; [|discriminate].
cbn [option_map]. f_equal. apply Z.eqb_eq. exact Hb.
Qed.

Definition dword_b (a v : Z) (n : nat) : bool :=
  forallb (fun k => match seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k)) with
                    | Some b => Z.eqb (bv_unsigned b) (YO0f.le_byte v n k)
                    | None => false
                    end) (seq 0 n).

Definition dgarr_b (a : Z) (l : list Z) : bool :=
  (drom_b a l && dz_cov_b a (Z.of_nat (length l)) disco_ro_ranges)%bool.

Definition dw8_b (a v : Z) : bool := (dword_b a v 8 && dz_cov_b a 8 disco_ro_ranges)%bool.

Definition dtail_b (e : Z) : bool :=
  ((e - e mod 8 + 8 <=? e + 1) || dz_cov_b (e + 1) (e - e mod 8 + 8 - (e + 1)) disco_ro_all)%bool.

Definition dbytes_ok_b (l : list Z) : bool := forallb (fun c => ((0 <? c) && (c <? 256))%bool) l.

Lemma dbytes_ok : forall l, dbytes_ok_b l = true -> Forall (fun c => 0 < c < 256) l.
Proof.
intros l H. apply Forall_forall. intros x Hx.
pose proof (proj1 (forallb_forall _ _) H x Hx) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

Definition drdok_b (a n : Z) : bool :=
  ((0 <? n) && (IMG_LO + 64 <=? a) && (a + n + 64 <=? IMG_TOP) && dz_cov_b a n disco_globs)%bool.

Definition dstr_b (a n : Z) : bool :=
  ((0 <? a) && (a + n <=? 2 ^ 63) && (n <? 2 ^ 32) && (a + n <=? kLowMemEnd - 1) &&
   drdok_b a n && dz_cov_b a n disco_ro_ranges && DiscoImg.rom_range_b a n && dtail_b (a + n - 1))%bool.

Lemma drom_in : forall a n x, DiscoImg.rom_range_b a n = true -> a <= x < a + n -> in_rom disco_segs x.
Proof.
intros a n x H Hx. unfold DiscoImg.rom_range_b in H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs|]. split; [exact H0 | lia].
Qed.

Lemma d_le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma d_val1_of_view : forall (H : word -> bool) (mm : word -> option byte) a v,
  aview disco_segs H mm a = Some v -> val_mem disco_segs (mrestrict H mm) a 1 v /\ 0 <= v < 256.
Proof.
intros H mm a v Hv. unfold aview in Hv.
destruct (mbyte disco_segs (mrestrict H mm) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate]. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
rewrite (d_le1 _ Hr). symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
apply bv_unsigned_in_range.
Qed.

Section dv. Context {rc : YM05.RunCeil}.

Lemma d_pa_segs : pa_segs (PAImg := PB_disco) = disco_segs.
Proof. reflexivity. Qed.

Lemma d_pa_val : pa_val (PAImg := PB_disco) = disco_val.
Proof. reflexivity. Qed.

Lemma d_val_obj : forall i z, (i < 68)%nat -> disco_obj i = z -> pa_val (PAImg := PB_disco) (A_OBJ i) = z.
Proof. intros i z Hi <-. exact (pa_obj_val i ltac:(unfold disco_nobj; lia)). Qed.

Lemma d_val_hi : forall j z, disco_hi j = z -> pa_val (PAImg := PB_disco) (A_HI j) = z.
Proof.
intros j z <-. rewrite d_pa_val. unfold disco_val.
replace ((A_HI j =? A_TEXT)%nat) with false by (symmetry; apply Nat.eqb_neq; unfold A_HI, A_TEXT; lia).
replace ((A_HI j <? A_HI 0)%nat) with false by (symmetry; apply Nat.ltb_ge; unfold A_HI; lia).
f_equal. unfold A_HI. lia.
Qed.

End dv.

Section dl. Context {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.

Definition dro_ctx (B : asyms) (ly : alayout) (S : astate) (W : world disco_segs)
  (mem : word -> option byte) (md : Model) : Prop :=
  AR disco_segs B ly S W mem md /\
  arodata_okP disco_segs disco_relro_lo disco_relro_hi B (aview disco_segs (w_H W) mem) /\
  disco_ro_unowned B /\ globs_marked disco_segs B disco_globs /\ img_shadow_vis disco_segs B.

Section dc.
Variable B : asyms.
Variable ly : alayout.
Variable S : astate.
Variable W : world disco_segs.
Variable mem : word -> option byte.
Variable md : Model.
Hypothesis CTX : dro_ctx B ly S W mem md.

Lemma d_view_rom : forall q sz x, In (q, sz) disco_ro_ranges -> q <= x < q + sz ->
  aview disco_segs (w_H W) mem x = option_map (fun b : byte => bv_unsigned b) (seg_rom disco_segs (Z_to_bv 64 x)).
Proof.
intros q sz x Hin Hx. destruct CTX as (HAR & HOK & DRO & GM & HV).
exact (ro_bytes disco_segs disco_relro_lo disco_relro_hi B (aview disco_segs (w_H W) mem) q sz x HOK
  (disco_ro_in_ro (PI := PB_disco) q sz x (d_in_all (q, sz) Hin) Hx)
  (disco_ro_unowned_at B q sz DRO Hin) Hx).
Qed.

Lemma d_garr8_b : forall a l, dgarr_b a l = true -> garr8 disco_segs (mrestrict (w_H W) mem) a l.
Proof.
intros a l Hb. apply andb_prop in Hb as [Hr Hc].
destruct (dz_cov a (Z.of_nat (length l)) disco_ro_ranges Hc) as (q & sz & Hin & Hlo & Hhi).
intros j Hj.
assert (Hv : aview disco_segs (w_H W) mem (a + Z.of_nat j) = Some (nth j l 0)).
{ rewrite (d_view_rom q sz (a + Z.of_nat j) Hin ltac:(lia)). exact (drom_at a l j Hr Hj). }
destruct (d_val1_of_view (w_H W) mem (a + Z.of_nat j) (nth j l 0) Hv) as [Hm Hrg].
split; [exact Hm | exact Hrg].
Qed.

Lemma d_val_rom : forall q sz a v n, In (q, sz) disco_ro_ranges -> q <= a -> a + Z.of_nat n <= q + sz ->
  dword_b a v n = true -> val_mem disco_segs (mrestrict (w_H W) mem) a n v.
Proof.
intros q sz a v n Hin Hlo Hhi Hb k Hk.
assert (Hv : aview disco_segs (w_H W) mem (a + Z.of_nat k) = Some (YO0f.le_byte v n k)).
{ rewrite (d_view_rom q sz (a + Z.of_nat k) Hin ltac:(lia)).
  pose proof (proj1 (forallb_forall _ _) Hb k ltac:(apply in_seq; lia)) as Hc. cbv beta in Hc.
  destruct (seg_rom disco_segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate].
  cbn [option_map]. f_equal. apply Z.eqb_eq. exact Hc. }
destruct (d_val1_of_view (w_H W) mem (a + Z.of_nat k) (YO0f.le_byte v n k) Hv) as [Hm Hr].
specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm.
rewrite (d_le1 _ Hr) in Hm. exact Hm.
Qed.

Lemma d_word_b : forall a v, dw8_b a v = true -> val_mem disco_segs (mrestrict (w_H W) mem) a 8 v.
Proof.
intros a v Hb. apply andb_prop in Hb as [Hw Hc].
destruct (dz_cov a 8 disco_ro_ranges Hc) as (q & sz & Hin & Hlo & Hhi).
exact (d_val_rom q sz a v 8%nat Hin Hlo ltac:(cbn [Z.of_nat]; lia) Hw).
Qed.

Lemma d_in_img_rom : forall q sz x, In (q, sz) disco_ro_all -> q <= x < q + sz -> in_img disco_segs x.
Proof.
intros q sz x Hin Hx. destruct (disco_ro_in_ro (PI := PB_disco) q sz x Hin Hx) as [(s & Hs & _ & Hr) | Hrel].
- exists s. split; [exact Hs | exact Hr].
- exact (disco_relro_img x Hrel).
Qed.

Lemma d_in_img_b : forall a n, dz_cov_b a n disco_ro_all = true ->
  forall x, a <= x < a + n -> in_img disco_segs x.
Proof.
intros a n Hb x Hx. destruct (dz_cov a n disco_ro_all Hb) as (q & sz & Hin & Hlo & Hhi).
exact (d_in_img_rom q sz x Hin ltac:(lia)).
Qed.

Lemma d_tail_vis : forall e, dtail_b e = true ->
  forall x, e < x < e - e mod 8 + 8 -> aview disco_segs (w_H W) mem x <> None.
Proof.
intros e H x Hx. unfold dtail_b in H. apply orb_true_iff in H as [H|H].
- apply Z.leb_le in H. lia.
- destruct (dz_cov (e + 1) (e - e mod 8 + 8 - (e + 1)) disco_ro_all H) as (q & m & Hin & H1 & H2).
  exact (disco_ro_view (PI := PB_disco) (w_H W) mem q m x Hin ltac:(lia)).
Qed.

Lemma d_rdok_b : forall a n, drdok_b a n = true ->
  range_addressable (aview disco_segs (w_H W) mem) SHADOW_OFF a n /\
  shadow_hull_vis (aview disco_segs (w_H W) mem) a n.
Proof.
intros a n Hb. unfold drdok_b in Hb.
apply andb_prop in Hb as [Hb Hc]. apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hn Hlo].
apply Z.ltb_lt in Hn. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
destruct (dz_cov a n disco_globs Hc) as (q & sz & Hin & H1 & H2).
destruct CTX as (HAR & HOK & DRO & GM & HV).
exact (ro_read_ok_glob disco_segs B disco_globs ly S W mem md q sz a n GM Hin HV HAR H1 H2 Hn Hlo Hhi).
Qed.

Lemma d_rom_b : forall a n, DiscoImg.rom_range_b a n = true -> d_rom a n.
Proof. intros a n H x Hx. exact (drom_in a n x H Hx). Qed.

Lemma d_str_parts : forall a (s : list Z),
  dstr_b a (Z.of_nat (length s) + 1) = true -> drom_b a (s ++ [0]) = true ->
  garr8 disco_segs (mrestrict (w_H W) mem) a (s ++ [0]) /\
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  amem_range a (Z.of_nat (length s) + 1) /\
  range_addressable (aview disco_segs (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview disco_segs (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview disco_segs (w_H W) mem x <> None) /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img disco_segs x) /\
  d_rom a (Z.of_nat (length s) + 1).
Proof.
intros a s Hb Hr. unfold dstr_b in Hb.
apply andb_prop in Hb as [Hb Htl]. apply andb_prop in Hb as [Hb Hrom]. apply andb_prop in Hb as [Hb Hcov].
apply andb_prop in Hb as [Hb Hrd]. apply andb_prop in Hb as [Hb Hlow]. apply andb_prop in Hb as [Hb H32].
apply andb_prop in Hb as [Hpos H63].
apply Z.ltb_lt in Hpos. apply Z.leb_le in H63. apply Z.ltb_lt in H32. apply Z.leb_le in Hlow.
assert (Hlen : Z.of_nat (length (s ++ [0])) = Z.of_nat (length s) + 1) by (rewrite length_app; cbn [length]; lia).
split.
{ apply d_garr8_b. unfold dgarr_b. apply andb_true_intro. split; [exact Hr|]. rewrite Hlen. exact Hcov. }
split; [exact Hpos|]. split; [lia|]. split; [lia|].
split; [left; unfold kLowMemEnd in Hlow; unfold kLowMemEnd; lia|].
destruct (d_rdok_b a (Z.of_nat (length s) + 1) Hrd) as [Hra Hhv].
split; [exact Hra|]. split; [exact Hhv|].
split.
{ intros x Hx. apply (d_tail_vis (a + (Z.of_nat (length s) + 1) - 1) Htl).
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) by lia. exact Hx. }
split.
{ intros x Hx. destruct (dz_cov a (Z.of_nat (length s) + 1) disco_ro_ranges Hcov) as (q & sz & Hin & H1 & H2).
  exact (d_in_img_rom q sz x (d_in_all (q, sz) Hin) ltac:(lia)). }
intros x Hx. exact (drom_in a (Z.of_nat (length s) + 1) x Hrom Hx).
Qed.

Lemma d_rostr_of : forall a (s : list Z),
  dstr_b a (Z.of_nat (length s) + 1) = true -> drom_b a (s ++ [0]) = true -> dbytes_ok_b s = true ->
  d_rostr W mem a s.
Proof.
intros a s H1 H2 H3.
destruct (d_str_parts a s H1 H2) as (G & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
split; [|exact P9]. unfold tjson_scalar_str.
split; [exact (dbytes_ok s H3)|]. split; [exact G|]. split; [exact P1|]. split; [lia|]. split; [exact P3|].
split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P7 | exact P8].
Qed.

Lemma d_tjstr_of : forall a (s : list Z),
  dstr_b a (Z.of_nat (length s) + 1) = true -> drom_b a (s ++ [0]) = true -> dbytes_ok_b s = true ->
  tjson_scalar_str W mem a s.
Proof. intros a s H1 H2 H3. exact (proj1 (d_rostr_of a s H1 H2 H3)). Qed.

Lemma d_rbn_stem_of : forall a (s : list Z),
  dstr_b a (Z.of_nat (length s) + 1) = true -> drom_b a (s ++ [0]) = true -> dbytes_ok_b s = true ->
  rbn_stem W mem a s.
Proof.
intros a s H1 H2 H3.
destruct (d_str_parts a s H1 H2) as (G & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
split; [|exact P8]. unfold rbn_str.
split; [exact (dbytes_ok s H3)|]. split; [exact G|]. split; [exact P1|]. split; [lia|]. split; [exact P3|].
split; [exact P4|]. split; [exact P5|]. split; [exact P6 | exact P7].
Qed.

Lemma d_rbn_lit_of : forall a (s : list Z),
  dstr_b a (Z.of_nat (length s) + 1) = true -> drom_b a (s ++ [0]) = true -> rbn_lit W mem a s.
Proof.
intros a s H1 H2.
destruct (d_str_parts a s H1 H2) as (G & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
split; [exact G|]. split; [exact P5 | exact P8].
Qed.

End dc.
End dl.
