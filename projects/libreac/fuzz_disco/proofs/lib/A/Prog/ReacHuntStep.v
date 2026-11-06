(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 4602 of its 4661 lines of code are new or changed and 310 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC81 YC1g YC1h YC45 YC4b YC88 YC85 YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableAge ReacArbitrate ReacSenderKind.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_hunt_step disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c hunt_c reac_rate_snap_c reac_master_only_cadence_ns_c reac_hunt_step_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_age_c reac_arbitrate_c reac_sender_kind_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma l1_ble_cons : forall (b : byte) (bs : list byte), bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. apply Bytes.lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
- pose proof (disco_table.ble_range bs). lia.
Qed.
Lemma l1_ble_byte : forall bs k, (k < length bs)%nat ->
Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
rewrite l1_ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (disco_table.ble_range bs) as Hr.
destruct k as [|k].
- cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. exact Hb.
- cbn [nth length] in *. rewrite Nat2Z.inj_succ.
replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
rewrite <- Z.shiftr_shiftr by lia. rewrite (Z.shiftr_div_pow2 _ 8) by lia. change (2 ^ 8) with 256.
rewrite Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by exact Hb. rewrite Z.add_0_l.
apply IH. lia.
Qed.
Lemma l2_ble_cons : forall (b : byte) (bs : list byte),
bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. apply Bytes.lor_shiftl8_add.
- pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia.
- apply PropExec.bytes_le_to_Z_nonneg.
Qed.
Lemma l2_ble_nth : forall (bs : list byte) j, (j < length bs)%nat ->
Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j) mod 256 = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
rewrite l2_ble_cons. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
  assert (Hd : Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) (8 + 8 * Z.of_nat j)
               = Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)).
  { rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by lia.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs)
      by (symmetry; Z.div_mod_to_equations; lia).
    reflexivity. }
  rewrite Hd. apply IH. lia.
Qed.
Lemma l2_nth_sub : forall (A : list byte) (k : Z) (n j : nat), 0 <= k -> (j < n)%nat ->
nth j (sub A k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) A (Z_to_bv 8 0).
Proof.
intros A k n j Hk Hj. unfold sub.
destruct (Nat.lt_ge_cases j (length (skipn (Z.to_nat k) A))) as [Hl|Hl].
- rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn; f_equal; lia.
- rewrite nth_overflow by (rewrite length_firstn; lia).
  rewrite length_skipn in Hl. rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma l2_u_at_byte : forall (A : list byte) (k : Z) (n j : nat), 0 <= k -> (Z.to_nat k + n <= length A)%nat -> (j < n)%nat ->
Z_to_bv 8 (YO0f.le_byte (u_at A k n) n j) = nth (Z.to_nat k + j) A (Z_to_bv 8 0).
Proof.
intros A k n j Hk Hn Hj.
assert (LS : length (sub A k n) = n).
{ unfold sub. rewrite length_firstn, length_skipn. lia. }
pose proof (PropExec.bytes_le_to_Z_bound (sub A k n)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k n)) as Hb0.
rewrite (YI04.le_byte_small (u_at A k n) n j) by (unfold u_at; lia).
rewrite <- (l2_nth_sub A k n j Hk Hj). apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite <- (l2_ble_nth (sub A k n) j ltac:(lia)). unfold u_at. reflexivity.
Qed.
Lemma l2_u32_small : forall (A : list byte) (k : Z), 0 <= k -> (Z.to_nat k + 4 <= length A)%nat ->
0 <= bv_swrap 32 (u_at A k 4) -> u_at A k 4 = bv_swrap 32 (u_at A k 4).
Proof.
intros A k Hk Hn H0.
assert (LS : length (sub A k 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (PropExec.bytes_le_to_Z_bound (sub A k 4)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k 4)) as Hb0.
unfold u_at in *. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma l2_u_range : forall (A : list byte) (k : Z) (n : nat), 0 <= u_at A k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros A k n. unfold u_at.
pose proof (PropExec.bytes_le_to_Z_bound (sub A k n)) as Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k n)) as Hb0.
assert (Hl : (length (sub A k n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb|]. apply Z.pow_le_mono_r; lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma l2_val : forall (m : word -> option byte) (A : list byte) (p k : Z) (n : nat),
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) A) -> 0 <= k -> (Z.to_nat k + n <= length A)%nat ->
val_mem SEGS m (p + k) n (u_at A k n).
Proof.
intros m A p k n HG Hk Hn j Hj.
rewrite (l2_u_at_byte A k n j Hk Hn Hj).
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (garr8_mbyte SEGS m p _ (Z.to_nat k + j) HG ltac:(rewrite length_map; lia)).
assert (NM : forall j0, nth j0 (map (fun b : byte => bv_unsigned b) A) 0 = bv_unsigned (nth j0 A (Z_to_bv 8 0)))
  by (intros j0; rewrite <- (map_nth (fun b : byte => bv_unsigned b) A (Z_to_bv 8 0) j0); reflexivity).
f_equal. rewrite NM. apply Z_to_bv_bv_unsigned.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis TAGE : treac_disco_table_age_spec B.
Hypothesis TARB : treac_arbitrate_spec B.
Hypothesis TSENDER : treac_sender_kind_spec B.
Definition REAC_HUNT_STEP_STK : Z := 112 + REAC_ARBITRATE_STK.
(* The csr a run may leave, relative to the hunt's entry state: as it was, or with a zero rounding-mode field
   (apost_base's csr clause, which the callees' posts now give in place of an equality). *)
Definition hs_csr (fq0 fq : YK11.FPState) : Prop :=
  @YK11.fp_csr fq = @YK11.fp_csr fq0 \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq)) 5) 7 = 0.
Lemma hs_csr_refl : forall fq, hs_csr fq fq.
Proof. intros fq. left. reflexivity. Qed.
Lemma hs_csr_trans : forall a b c, hs_csr a b -> hs_csr b c -> hs_csr a c.
Proof.
unfold hs_csr. intros a b c [Hb|Hb] [Hc|Hc];
  [left; rewrite Hc; exact Hb | right; exact Hc | right; rewrite Hc; exact Hb | right; exact Hc].
Qed.
(* A callee's apost_base f-register clause (all but f10, by Sem.reg_get) keeps freg_kept. *)
Lemma hs_freg_apost : forall F G H, freg_kept F G ->
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get H k = Sem.reg_get G k) -> freg_kept F H.
Proof. intros F G H HA HB k H10 H14 H15. rewrite (HB k H10). apply HA; assumption. Qed.
Definition treac_hunt_step_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (h now : Z) (H : list byte) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_HUNT_STEP_STK [(h, h + 400); (h + 440, h + 476)] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (if hs_verdict h H now =? s32_at H 440 then 0 else 1) /\
         garr8 SEGS (mrestrict (w_H W') mem') h (map (fun b : byte => bv_unsigned b) (hs_hunt h H now)) /\
         hunt_ok (hs_hunt h H now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_step_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (H : list byte),
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 h -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  hunt_ok H ->
  garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) H) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
  (forall x, 0 <= x < 8 -> in_img SEGS (VAL (A_HI 97) + -1832 + x) /\ in_img SEGS (VAL (A_HI 96) + -1628 + x)) ->
  (forall x, 0 <= x < 12 -> in_img SEGS (VAL (A_OBJ 65) + x)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_hunt_step) regs mem md)
    (treac_hunt_step_post fq regs ly S W mem md h now H).
Definition HSBx : sv := SOff 32 0.
Definition hs_regions : smem := [ stack_region 112; got_regionP; bcell_regionP 32 ].
Definition hs_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 3); (11%nat, mkAF 0 (2 ^ 64 - 1) 0);
(32%nat, mkAF SB SB 0) ] [] [].
Definition ss_hs : sstate := mkSS AF_reac_hunt_step sr_atoms hs_regions None hs_facts.
Definition hs_SH : list shent := [ mkSHE 10 0 480 ].
Definition EH (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SB]).
Definition HSFP (h : Z) : list (Z * Z) := [(h, h + 400); (h + 440, h + 476)].
Definition hs_saved : list (Z * bv 5) :=
[(104, 1%bv); (96, 8%bv); (88, 9%bv); (80, 18%bv); (72, 19%bv); (64, 20%bv); (56, 21%bv); (48, 22%bv);
(40, 23%bv); (32, 24%bv); (24, 25%bv); (16, 26%bv); (8, 27%bv)].
Definition hs_frame (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop :=
Forall (fun p => val_mem SEGS m (sp0 - 112 + fst p) 8 (bv_unsigned (getr regs (snd p)))) hs_saved.
Definition ep_chunks : list YP09.chunk :=
[YP09.mkChunk 8 (CVal 8 (SOff 45 0)); YP09.mkChunk 16 (CVal 8 (SOff 44 0)); YP09.mkChunk 24 (CVal 8 (SOff 43 0));
YP09.mkChunk 32 (CVal 8 (SOff 42 0)); YP09.mkChunk 40 (CVal 8 (SOff 41 0)); YP09.mkChunk 48 (CVal 8 (SOff 40 0));
YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 38 0)); YP09.mkChunk 72 (CVal 8 (SOff 37 0));
YP09.mkChunk 80 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SOff 35 0)); YP09.mkChunk 96 (CVal 8 (SOff 34 0));
YP09.mkChunk 104 (CVal 8 (SOff 33 0))].
Definition ep_regions : smem :=
[YP09.mkRegion (Some 2%nat) 0 112 0 0 ep_chunks; YP09.mkRegion (Some 8%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))]].
Definition ep_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, PTR 3); (23%nat, mkAF SB SB 0)] [] [].
Definition ss_ep (pc : Z) : sstate := mkSS pc sr_atoms ep_regions None ep_facts.
Definition ep_SH : list shent := [mkSHE 8 0 4].
Definition ep_Bx : sv := SOff 23 0.
Definition ep_extra (regs : bvmap 5 word) (w : Z) : list word :=
Z_to_bv 64 w :: map (getr regs) [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition EP (regsd regs : bvmap 5 word) (w : Z) : env := Eimg (Ereg regsd (ep_extra regs w)).
Lemma hs_frame_kept : forall (regs : bvmap 5 word) H H' (m m' : word -> option byte) sp0,
(forall a, sp0 - 104 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
hs_frame regs (mrestrict H m) sp0 -> hs_frame regs (mrestrict H' m') sp0.
Proof.
intros regs H H' m m' sp0 Hk HF. unfold hs_frame in *.
assert (R : forall p, In p hs_saved -> 8 <= fst p <= 104).
{ intros p Hp. unfold hs_saved in Hp. repeat (destruct Hp as [<- | Hp]; [cbn; lia|]). destruct Hp. }
apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) HF p Hp) as Hv. cbn beta in Hv |- *.
pose proof (R p Hp) as Rp.
apply (val_mem_kept SEGS H H' m m'); [|exact Hv].
intros k Hk'. change (Z.of_nat 8) with 8 in Hk'. apply Hk. lia.
Qed.
Lemma hs_map_firstn : forall (f : byte -> Z) (n : nat) (L : list byte), map f (firstn n L) = firstn n (map f L).
Proof. induction n as [|n IH]; intros [|x L]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma hs_map_skipn : forall (f : byte -> Z) (k : nat) (L : list byte), map f (skipn k L) = skipn k (map f L).
Proof. induction k as [|k IH]; intros [|x L]; cbn; try reflexivity. apply IH. Qed.
Lemma hs_map_sub : forall (f : byte -> Z) (L : list byte) (k : Z) (n : nat),
map f (sub L k n) = firstn n (skipn (Z.to_nat k) (map f L)).
Proof. intros f L k n. unfold sub. rewrite hs_map_firstn, hs_map_skipn. reflexivity. Qed.
Lemma hs_nth_le_bytes : forall (n : nat) (z : Z) (j : nat), (j < n)%nat ->
nth j (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
induction n as [|n IH]; intros z [|j] Hj; cbn [Z_to_le_bytes nth]; try lia.
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite (IH (Z.shiftr z 8) j ltac:(lia)). rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma hs_nth_sub : forall (k : nat) (L : list byte) (n j : nat), (j < n)%nat ->
nth j (firstn n (skipn k L)) (Z_to_bv 8 0) = nth (k + j) L (Z_to_bv 8 0).
Proof.
induction k as [|k IH]; intros L n j Hj.
- cbn [skipn Nat.add]. revert L j Hj. induction n as [|n IHn]; intros L j Hj; [lia|].
destruct L as [|x L];
[rewrite firstn_nil; rewrite !nth_overflow by (cbn [length]; lia); reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IHn. lia.
- destruct L as [|x L].
+ rewrite skipn_nil, firstn_nil. rewrite !nth_overflow by (cbn [length]; lia). reflexivity.
+ cbn [skipn Nat.add]. apply IH. exact Hj.
Qed.
Lemma hs_bs_head : forall (b : byte) (bs : list byte), Z_to_bv 8 (bytes_le_to_Z (b :: bs)) = b.
Proof.
intros b bs. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (Z.of_N 8) with 8. cbn [bytes_le_to_Z].
rewrite <- (Z.land_ones _ 8) by lia.
rewrite Z.land_lor_distr_l.
rewrite (Z.land_ones (bv_unsigned b) 8) by lia.
rewrite (Z.land_ones (Z.shiftl (bytes_le_to_Z bs) 8) 8) by lia.
rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8))
by (pose proof (bv_unsigned_in_range 8 b); change (bv_modulus 8) with (2 ^ 8) in *; lia).
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_mod_mult.
rewrite Z.lor_0_r. reflexivity.
Qed.
Lemma hs_bs_shift : forall (b : byte) (bs : list byte), Z.shiftr (bytes_le_to_Z (b :: bs)) 8 = bytes_le_to_Z bs.
Proof.
intros b bs. cbn [bytes_le_to_Z]. rewrite Z.shiftr_lor.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.div_small (bv_unsigned b) 256)
by (pose proof (bv_unsigned_in_range 8 b); change (bv_modulus 8) with 256 in *; lia).
rewrite Z.shiftr_shiftl_r by lia. replace (8 - 8) with 0 by lia. rewrite Z.shiftr_0_r.
rewrite Z.lor_0_l. reflexivity.
Qed.
Lemma hs_nth_bs : forall (bs : list byte) (j : nat), (j < length bs)%nat ->
Z_to_bv 8 (Z.shiftr (bytes_le_to_Z bs) (8 * Z.of_nat j)) = nth j bs (Z_to_bv 8 0).
Proof.
induction bs as [|b bs IH]; intros [|j] Hj; cbn [length] in Hj; try lia.
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. apply hs_bs_head.
- cbn [nth]. replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia.
rewrite <- Z.shiftr_shiftr by lia. rewrite hs_bs_shift. apply IH. lia.
Qed.
Lemma hs_map_nth : forall (L : list byte) (j : nat), (j < length L)%nat ->
nth j (map (fun b : byte => bv_unsigned b) L) 0 = bv_unsigned (nth j L (Z_to_bv 8 0)).
Proof.
induction L as [|x L IH]; intros [|j] Hj; cbn [length] in Hj; try lia; cbn [map nth]; [reflexivity|].
apply IH. lia.
Qed.
Lemma hs_val_mem_of_garr8 : forall m a (L : list byte) (k : Z) (n : nat),
garr8 SEGS m a (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
val_mem SEGS m (a + k) n (u_at L k n).
Proof.
intros m a L k n HG Hk Hkn j Hj.
pose proof (garr8_mbyte SEGS m a (map (fun b : byte => bv_unsigned b) L) (Z.to_nat k + j) HG
ltac:(rewrite length_map; lia)) as HM.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in HM by lia.
rewrite HM. f_equal.
assert (LS : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
assert (HR : 0 <= bytes_le_to_Z (sub L k n) < 2 ^ (8 * Z.of_nat n)).
{ pose proof (YK11.bytes_le_to_Z_bound (sub L k n)) as HB.
pose proof (YK11.bytes_le_to_Z_nonneg (sub L k n)) as HN. rewrite LS in HB. lia. }
rewrite (le_byte_small (u_at L k n) n j HR Hj).
unfold u_at. rewrite (hs_nth_bs (sub L k n) j ltac:(rewrite LS; exact Hj)).
unfold sub. rewrite hs_nth_sub by exact Hj.
rewrite (hs_map_nth L (Z.to_nat k + j) ltac:(lia)).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma hs_garr8_of_val4 : forall m a v, 0 <= v < 2 ^ 32 -> val_mem SEGS m a 4 v ->
garr8 SEGS m a (map (fun b : byte => bv_unsigned b) (Z_to_le_bytes 4 v)).
Proof.
intros m a v Hv HV j Hj. rewrite length_map in Hj. cbn [length Z_to_le_bytes] in Hj.
rewrite (hs_map_nth (Z_to_le_bytes 4 v) j) by (cbn [length Z_to_le_bytes]; lia).
rewrite (hs_nth_le_bytes 4 v j) by lia. rewrite Z_to_bv_unsigned.
assert (RX : 0 <= bv_wrap 8 (Z.shiftr v (8 * Z.of_nat j)) < 256).
{ unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_pos_bound. lia. }
split; [|exact RX].
intros k Hk. assert (k = 0%nat) by (cbn in Hk; lia). subst k.
replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia.
rewrite (HV j ltac:(lia)).
rewrite (le_byte_small v 4 j) by (cbn; lia).
rewrite (le_byte_small _ 1 0) by (cbn; lia).
f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap. rewrite Zmod_mod. reflexivity.
Qed.
Definition hs_img (h now : Z) (Hb : list byte) : list byte :=
hs_table Hb now ++ sub Hb 400 44 ++ hs_arb h Hb now ++ sub Hb 476 4.
Lemma hs_img_len : forall h now Hb, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
length (hs_arb h Hb now) = 32%nat -> length (hs_img h now Hb) = 480%nat.
Proof. intros h now Hb LH LT LA. unfold hs_img, sub. rewrite !length_app, !length_firstn, !length_skipn, LH, LT, LA. reflexivity. Qed.
Lemma hs_img_first : forall h now Hb, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
firstn 440 (hs_img h now Hb) = hs_table Hb now ++ sub Hb 400 40.
Proof.
intros h now Hb LH LT. unfold hs_img. rewrite firstn_app, LT, firstn_all2 by lia. f_equal.
replace (440 - 400)%nat with 40%nat by lia. rewrite firstn_app.
assert (LX : length (sub Hb 400 44) = 44%nat) by (unfold sub; rewrite length_firstn, length_skipn, LH; reflexivity).
rewrite LX. replace (40 - 44)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
unfold sub. rewrite firstn_firstn. reflexivity.
Qed.
Lemma hs_img_last : forall h now Hb, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
skipn 444 (hs_img h now Hb) = hs_arb h Hb now ++ skipn 476 Hb.
Proof.
intros h now Hb LH LT. unfold hs_img. rewrite skipn_app, LT, skipn_all2 by lia. cbn [app].
replace (444 - 400)%nat with 44%nat by lia. rewrite skipn_app.
assert (LX : length (sub Hb 400 44) = 44%nat) by (unfold sub; rewrite length_firstn, length_skipn, LH; reflexivity).
rewrite LX, skipn_all2 by lia. rewrite Nat.sub_diag. cbn [app]. rewrite skipn_O. f_equal.
unfold sub. change (Z.to_nat 476) with 476%nat. apply firstn_all2. rewrite length_skipn, LH. lia.
Qed.
Lemma hs_img_mid : forall h now Hb, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
sub (hs_img h now Hb) 440 4 = sub Hb 440 4.
Proof.
intros h now Hb LH LT. unfold sub at 1. change (Z.to_nat 440) with 440%nat. unfold hs_img.
rewrite skipn_app, LT, skipn_all2 by lia. cbn [app]. replace (440 - 400)%nat with 40%nat by lia.
rewrite skipn_app, firstn_app.
assert (LX : length (skipn 40 (sub Hb 400 44)) = 4%nat)
by (rewrite length_skipn; unfold sub; rewrite length_firstn, length_skipn, LH; reflexivity).
rewrite LX. replace (4 - 4)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
unfold sub. change (Z.to_nat 400) with 400%nat. change (Z.to_nat 440) with 440%nat.
rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn. reflexivity.
Qed.
Section w. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Lemma hs_epi_entry : forall ly S W mem md lyd Sd Wd (regsd regs : bvmap 5 word) memd mdd (h hb hn : Z) (H3 : list byte) pc,
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyd Sd Wd memd mdd 0 ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF ->
hs_frame regs (mrestrict (w_H Wd) memd) (spZ regs) ->
0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyd Sd) -> hb <= h -> h + 480 <= hb + req_size hn ->
length H3 = 480%nat -> garr8 SEGS (mrestrict (w_H Wd) memd) h (map (fun b : byte => bv_unsigned b) H3) ->
st_ok_pi SEGS VAL (EP regsd regs (u_at H3 440 4)) (ss_ep pc)
(restrict (w_H Wd) (mkst regsd (Z_to_bv 64 (BASE + pc)) memd (seg_rom SEGS)))
/\ sh_ok SEGS ep_Bx ep_SH (EP regsd regs (u_at H3 440 4)) (mrestrict (w_H Wd) memd).
Proof.
intros ly S W mem md lyd Sd Wd regsd regs memd mdd h hb hn H3 pc HJ R2 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
set (sp0 := spZ regs) in *.
assert (Hsp0 : 0 <= sp0 < 2 ^ 64) by (subst sp0; unfold spZ; apply bv_unsigned_in_range).
rewrite restrict_mkst_fx.
set (E := EP regsd regs (u_at H3 440 4)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsd (ep_extra regs (u_at H3 440 4))) n)
by (intros n Hn; subst E; unfold EP; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsd _ 2 2%bv eq_refl); exact R2).
assert (E8 : ew E 8 = Z_to_bv 64 (h + 440)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsd _ 8 8%bv eq_refl); exact R8).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsd _ 23 23%bv eq_refl); exact R23).
assert (EX : forall i, (i < 14)%nat -> ew E (32 + i) = nth i (ep_extra regs (u_at H3 440 4)) (Z_to_bv 64 0)).
{ intros i Hi. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 8) = h + 440) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- unfold ss_ep. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ep_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ep_chunks.
      let ck off n i r :=
        apply (chunk_ok_val SEGS E _ (sp0 - 112) off 8 (SOff n 0) (bv_unsigned (getr regs r)));
        [ cbn [sv_denot]; pose proof (EX i ltac:(lia)) as X; cbn [Nat.add nth ep_extra map] in X;
          rewrite X, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR;
          cbn; lia
        | cbn; lia
        | exact (proj1 (Forall_forall _ _) HFR (off, r) ltac:(cbn; tauto)) ] in
      apply Forall_cons; [ck 8 45%nat 13%nat (27%bv : bv 5)|];
      apply Forall_cons; [ck 16 44%nat 12%nat (26%bv : bv 5)|];
      apply Forall_cons; [ck 24 43%nat 11%nat (25%bv : bv 5)|];
      apply Forall_cons; [ck 32 42%nat 10%nat (24%bv : bv 5)|];
      apply Forall_cons; [ck 40 41%nat 9%nat (23%bv : bv 5)|];
      apply Forall_cons; [ck 48 40%nat 8%nat (22%bv : bv 5)|];
      apply Forall_cons; [ck 56 39%nat 7%nat (21%bv : bv 5)|];
      apply Forall_cons; [ck 64 38%nat 6%nat (20%bv : bv 5)|];
      apply Forall_cons; [ck 72 37%nat 5%nat (19%bv : bv 5)|];
      apply Forall_cons; [ck 80 36%nat 4%nat (18%bv : bv 5)|];
      apply Forall_cons; [ck 88 35%nat 3%nat (9%bv : bv 5)|];
      apply Forall_cons; [ck 96 34%nat 2%nat (8%bv : bv 5)|];
      apply Forall_cons; [ck 104 33%nat 1%nat (1%bv : bv 5)|];
      apply Forall_nil.
    * rewrite Uh. split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbpres (h + 440 + o) ltac:(lia))).
      -- constructor; [|constructor].
         assert (HU : 0 <= u_at H3 440 4 < 2 ^ 32).
         { unfold u_at. pose proof (YK11.bytes_le_to_Z_bound (sub H3 440 4)) as HB.
           pose proof (YK11.bytes_le_to_Z_nonneg (sub H3 440 4)) as HN.
           assert (LS : length (sub H3 440 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn, LH3; reflexivity).
           rewrite LS in HB. cbn in HB. lia. }
         apply (chunk_ok_val SEGS E _ (h + 440) 0 4 (SOff 32 0) (u_at H3 440 4));
         [ cbn [sv_denot]; pose proof (EX 0%nat ltac:(lia)) as X; cbn [Nat.add nth ep_extra] in X;
           rewrite X, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. apply hs_val_mem_of_garr8; [exact HG3 | lia | rewrite LH3; cbn; lia].
  + apply pairwise_disjoint_of_extents. unfold ep_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uh.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hsh H47 Hceil Hbceil Hlo Hhi Hh0 Hrq0 Hrq1 Hstk0 C1 WS. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ep_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uh, U23. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hsh H47 Hceil Hbceil Hb4096 Hlo Hhi Hh0 Hh8 Hal C1 C3 WS Hstk0 Hrq0 Hrq1.
    clear. unfold SB, SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end;
    first [exact I | lia | rewrite Zminus_mod, Hal; reflexivity | rewrite Zplus_mod, Hh8; reflexivity].
- unfold sh_ok, ep_SH. constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H Wd) memd E ep_Bx 8 (h + 440) 4 (h + 440) 0 4).
  + eapply (range_addressable_of_block SEGS B LAWS lyd Sd Wd memd mdd hb hn (h + 440) 4 HAR Hin); lia.
  + unfold U, ep_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U23.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Uh.
  + lia.
  + lia.
  + intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
    unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma hs_epi_7664 : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb H3 : list byte)
lyd Sd Wd (regsd : bvmap 5 word) memd mdd (v : Z),
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyd Sd Wd memd mdd 0 ->
freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
getr regsd 10 = w64 v ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF ->
hs_frame regs (mrestrict (w_H Wd) memd) (spZ regs) ->
0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyd Sd) -> hb <= h -> h + 480 <= hb + req_size hn ->
length H3 = 480%nat -> garr8 SEGS (mrestrict (w_H Wd) memd) h (map (fun b : byte => bv_unsigned b) H3) ->
v = hs_verdict h Hb now -> 0 <= v <= 3 -> s32_at H3 440 = s32_at Hb 440 -> 0 <= s32_at Hb 440 <= 3 ->
firstn 440 H3 ++ Z_to_le_bytes 4 v ++ skipn 444 H3 = hs_hunt h Hb now ->
hunt_ok (hs_hunt h Hb now) ->
Permutation (ablocks B lyd Sd) (ablocks B ly S) ->
SRr SEGS Wd (cfg_at (fx := fx) SEGS (BASE + 0x7664) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb H3 lyd Sd Wd regsd memd mdd v HPRE HJ HFk HFc R10
R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3 Hv Rv Hold Rold Hsplice HOKH HPerm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct (hs_epi_entry ly S W mem md lyd Sd Wd regsd regs memd mdd h hb hn H3 0x7664 HJ R2 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3)
as [HS SHOK].
set (E := EP regsd regs (u_at H3 440 4)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EP; apply Eimg_env).
pose proof (proj1 HJ) as HARd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HARd Hin) as (Hbb16 & Hbb4096 & Hbbceil & Hbbapp & Hbbpres & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Uh8 : bv_unsigned (ew E 8) = h + 440).
{ subst E; unfold EP; rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regsd _ 8 8%bv eq_refl), R8. apply unsigned_lit_small. lia. }
unfold cfg_at.
change (w64 (BASE + 0x7664)) with (Z_to_bv 64 (BASE + 0x7664)).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := 8%nat) (b := h + 440);
    [reflexivity | exact Uh8
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
      [exists (h + 440, h + 476); split; [right; left; reflexivity | cbn; lia] | exists hb, hn; split; [exact Hin | lia]]
    | apply awr_ok_nil]. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  assert (EXv : forall i, (i < 14)%nat -> ew E (32 + i) = nth i (ep_extra regs (u_at H3 440 4)) (Z_to_bv 64 0)).
  { intros i Hi. subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (E10v : ew E 10 = Z_to_bv 64 v).
  { subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsd _ 10 10%bv eq_refl). exact R10. }
  assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs - 112)).
  { subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsd _ 2 2%bv eq_refl). exact R2. }
  assert (E3v : ew E 3 = getr regs 3).
  { subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsd _ 3 3%bv eq_refl). exact R3. }
  assert (E4v : ew E 4 = getr regs 4).
  { subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regsd _ 4 4%bv eq_refl). exact R4. }
  pose proof (EXv 0%nat ltac:(lia)) as X0. pose proof (EXv 1%nat ltac:(lia)) as X1. pose proof (EXv 2%nat ltac:(lia)) as X2.
  pose proof (EXv 3%nat ltac:(lia)) as X3. pose proof (EXv 4%nat ltac:(lia)) as X4. pose proof (EXv 5%nat ltac:(lia)) as X5.
  pose proof (EXv 6%nat ltac:(lia)) as X6. pose proof (EXv 7%nat ltac:(lia)) as X7. pose proof (EXv 8%nat ltac:(lia)) as X8.
  pose proof (EXv 9%nat ltac:(lia)) as X9. pose proof (EXv 10%nat ltac:(lia)) as X10. pose proof (EXv 11%nat ltac:(lia)) as X11.
  pose proof (EXv 12%nat ltac:(lia)) as X12. pose proof (EXv 13%nat ltac:(lia)) as X13.
  cbn [Nat.add nth ep_extra map] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13.
  assert (HU : 0 <= u_at H3 440 4 < 2 ^ 32).
  { unfold u_at. pose proof (YK11.bytes_le_to_Z_bound (sub H3 440 4)) as HB.
    pose proof (YK11.bytes_le_to_Z_nonneg (sub H3 440 4)) as HN.
    assert (LS : length (sub H3 440 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn, LH3; reflexivity).
    rewrite LS in HB. cbn in HB. lia. }
  assert (Uold : u_at H3 440 4 = s32_at Hb 440).
  { rewrite <- Hold in Rold |- *. unfold s32_at in *. destruct (Z.lt_ge_cases (u_at H3 440 4) (2 ^ 31)) as [Hl | Hg].
    - symmetry. apply swrap32_id. lia.
    - exfalso. rewrite (bv_swrap_hi 32 (u_at H3 440 4)) in Rold
      by (first [discriminate | change (bv_half_modulus 32) with (2 ^ 31); lia | change (bv_modulus 32) with (2 ^ 32); lia]).
      change (bv_modulus 32) with (2 ^ 32) in Rold. lia. }
  assert (Hret : v_jalr (getr (ms_regs ms) 1) 0 = getr regs 1) by (rewrite Q1, X1; exact Hra).
  assert (Hval : getr (ms_regs ms) 10 = w64 (if hs_verdict h Hb now =? s32_at Hb 440 then 0 else 1)).
  { rewrite Q10, E10v, X0. rewrite (sext32_small (u_at H3 440 4)) by lia. rewrite Uold, <- Hv.
    apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
    unfold w64. rewrite Z_to_bv_unsigned.
    destruct (Z.eqb_spec v (s32_at Hb 440)) as [<- | Hne].
    - rewrite Z.lxor_nilpotent. reflexivity.
    - assert (Hx : 0 < Z.lxor v (s32_at Hb 440) < 4).
      { revert Rv Rold Hne. generalize (s32_at Hb 440). generalize v. clear. intros a b Ra Rb Hab.
        assert (a = 0 \/ a = 1 \/ a = 2 \/ a = 3) as [-> | [-> | [-> | ->]]] by lia;
        assert (b = 0 \/ b = 1 \/ b = 2 \/ b = 3) as [-> | [-> | [-> | ->]]] by lia;
        first [exfalso; lia | split; vm_compute; reflexivity]. }
      rewrite (bv_wrap_small 64 (Z.lxor v (s32_at Hb 440))) by (change (bv_modulus 64) with (2 ^ 64); lia).
      replace (0 <? Z.lxor v (s32_at Hb 440)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (MK : forall a, 0 <= a < 2 ^ 64 -> ~ (h + 440 <= a < h + 444) ->
    mbyte SEGS (mrestrict (w_H Wd) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H Wd) memd) a).
  { intros a Ha Hn. apply (mbyte_of_frame_x SEGS E _ _ _ a HFr Ha). intros r Hr.
    cbn [ss_ep ss_mem ep_regions In] in Hr. destruct Hr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; [lia | rewrite Uh8; lia]. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 (YP09.mkRegion (Some 8%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 10 0))]) HS eq_refl) as RT.
  unfold region_ok in RT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ew ewset Nat.eqb restrict ms_mem] in RT.
  destruct RT as (_ & _ & _ & RC). apply Forall_inv in RC.
  pose proof (val_of_chunk_ok SEGS _ _ _ 0 4 (SOff 10 0) v RC) as VM.
  rewrite Uh8 in VM.
  specialize (VM ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E10v, unsigned_lit_small, Z.add_0_r by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)).
  rewrite Z.add_0_r in VM. change (N.to_nat 4) with 4%nat in VM.
  eapply (RET Wd _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite Hret.
  unfold treac_hunt_step_post. exists (mkFP (@YK11.fp_regs fx) (@YK11.fp_csr fq0)).
  split; [exact HFk|]. split; [reflexivity|].
  unfold apost_base. exists fx. do 5 eexists. split; [reflexivity|].
  split; [intros; reflexivity|]. split; [exact HFc|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [-> | Hc]); [..| subst r];
    (lazymatch goal with |- getr _ (Z_to_bv 5 ?n) = _ => let Rr := fresh "Rr" in prreg HS (Z_to_bv 5 n) Rr; rewrite Rr
     | |- ?g => idtac "ARG" g; fail end);
    first [ rewrite ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9, ?X10, ?X11, ?X12, ?X13; reflexivity
          | rewrite E3v; reflexivity | rewrite E4v; reflexivity
          | assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity;
            pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
            assert (Rsp : 0 <= spZ regs - 112 < 2 ^ 64) by lia;
            rewrite E2v, unsigned_lit_small by exact Rsp; replace (spZ regs - 112 + 112) with (spZ regs) by lia;
            unfold spZ; apply Z_to_bv_bv_unsigned
          | match goal with |- ?g => idtac "AR" g; fail end ]. }
  split; [exact Hval|].
  split.
  { rewrite <- Hsplice. rewrite !map_app.
    apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    - apply (garr8_frame SEGS (mrestrict (w_H Wd) memd)).
      + pose proof HG3 as G. rewrite <- (firstn_skipn 440 H3) in G. rewrite map_app in G.
        exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) G)).
      + intros a Ha. rewrite length_map, length_firstn, LH3 in Ha. change (Nat.min 440 480) with 440%nat in Ha.
        apply MK; lia.
    - rewrite length_map, length_firstn, LH3. change (Nat.min 440 480) with 440%nat.
      apply (proj2 (garr8_app SEGS _ _ _ _)). split.
      + replace (h + Z.of_nat 440) with (h + 440) by lia. apply hs_garr8_of_val4; [lia | exact VM].
      + rewrite length_map. change (length (Z_to_le_bytes 4 v)) with 4%nat.
        replace (h + Z.of_nat 440 + Z.of_nat 4) with (h + Z.of_nat 444) by lia.
        apply (garr8_frame SEGS (mrestrict (w_H Wd) memd)).
        * pose proof HG3 as G. rewrite <- (firstn_skipn 444 H3) in G. rewrite map_app in G.
          pose proof (proj2 (proj1 (garr8_app SEGS _ _ _ _) G)) as G2. rewrite length_map, length_firstn, LH3 in G2.
          change (Nat.min 444 480) with 444%nat in G2. exact G2.
        * intros a Ha. rewrite length_map, length_skipn, LH3 in Ha. apply MK; lia. }
  split; [exact HOKH | exact HPerm].
Qed.
Lemma hs_epi_core : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb H3 : list byte)
lyd Sd Wd (regsd : bvmap 5 word) memd mdd (pc v : Z),
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyd Sd Wd memd mdd 0 ->
freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
(pc = 0x7664 /\ getr regsd 10 = w64 v \/ pc = 0x795c /\ v = 0) ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF ->
hs_frame regs (mrestrict (w_H Wd) memd) (spZ regs) ->
0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyd Sd) -> hb <= h -> h + 480 <= hb + req_size hn ->
length H3 = 480%nat -> garr8 SEGS (mrestrict (w_H Wd) memd) h (map (fun b : byte => bv_unsigned b) H3) ->
v = hs_verdict h Hb now -> 0 <= v <= 3 -> s32_at H3 440 = s32_at Hb 440 -> 0 <= s32_at Hb 440 <= 3 ->
firstn 440 H3 ++ Z_to_le_bytes 4 v ++ skipn 444 H3 = hs_hunt h Hb now ->
hunt_ok (hs_hunt h Hb now) ->
Permutation (ablocks B lyd Sd) (ablocks B ly S) ->
SRr SEGS Wd (cfg_at (fx := fx) SEGS (BASE + pc) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb H3 lyd Sd Wd regsd memd mdd pc v HPRE HJ HFk HFc Hpc
R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3 Hv Rv Hold Rold Hsplice HOKH HPerm.
destruct Hpc as [[-> R10] | [-> ->]].
- exact (hs_epi_7664 fq0 ly S W regs mem md ch h now hb hn Hb H3 lyd Sd Wd regsd memd mdd v HPRE HJ HFk HFc R10
  R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3 Hv Rv Hold Rold Hsplice HOKH HPerm).
- pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  destruct (hs_epi_entry ly S W mem md lyd Sd Wd regsd regs memd mdd h hb hn H3 0x795c HJ R2 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi LH3 HG3)
  as [HS SHOK].
  set (E := EP regsd regs (u_at H3 440 4)) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EP; apply Eimg_env).
  pose proof (proj1 HJ) as HARd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HARd Hin) as (Hbb16 & Hbb4096 & Hbbceil & Hbbapp & Hbbpres & _ & Hbbn).
  pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  apply (st_ok_pi_submem E _ _ [YP09.mkRegion (Some 2%nat) 0 112 0 0 ep_chunks]) in HS;
  [| submem_tac | vm_compute; reflexivity].
  unfold cfg_at. change (w64 (BASE + 0x795c)) with (Z_to_bv 64 (BASE + 0x795c)).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7664.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (23%bv : bv 5) P23.
  assert (MKa : forall a, 0 <= a < 2 ^ 64 -> mbyte SEGS (mrestrict (w_H Wd) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H Wd) memd) a).
  { intros a Ha. apply (mbyte_of_frame_x SEGS E _ _ _ a HFr Ha). intros r Hr. cbn [In] in Hr. destruct Hr as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. lia. }
  assert (AVk : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wd) (ms_mem ms) a = aview SEGS (w_H Wd) memd a).
  { intros a Ha. rewrite !(aview_mbyte SEGS). f_equal. apply MKa. exact Ha. }
  assert (EN : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regsd r).
  { intros n r Hn Hr. subst E. unfold EP. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regsd _ n r Hr). }
  apply (hs_epi_7664 fq0 ly S W regs mem md ch h now hb hn Hb H3 lyd Sd Wd (ms_regs ms) (ms_mem ms) _ 0 HPRE HJ HFk HFc).
  + rewrite P10. reflexivity.
  + rewrite P2, (EN 2%nat 2%bv ltac:(lia) eq_refl). exact R2.
  + rewrite P3, (EN 3%nat 3%bv ltac:(lia) eq_refl). exact R3.
  + rewrite P4, (EN 4%nat 4%bv ltac:(lia) eq_refl). exact R4.
  + rewrite P8, (EN 8%nat 8%bv ltac:(lia) eq_refl). exact R8.
  + rewrite P23, (EN 23%nat 23%bv ltac:(lia) eq_refl). exact R23.
  + apply (hs_frame_kept regs (w_H Wd) (w_H Wd) memd (ms_mem ms)); [|exact HFR].
    intros a Ha. apply AVk. lia.
  + exact Hh0.
  + exact Hh8.
  + exact Hin.
  + exact Hlo.
  + exact Hhi.
  + exact LH3.
  + apply (garr8_frame SEGS (mrestrict (w_H Wd) memd)); [exact HG3|].
    intros a Ha. rewrite length_map, LH3 in Ha. apply MKa. lia.
  + exact Hv.
  + exact Rv.
  + exact Hold.
  + exact Rold.
  + exact Hsplice.
  + exact HOKH.
  + exact HPerm.
Qed.
Lemma hs_epi : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte)
lyd Sd Wd (regsd : bvmap 5 word) memd mdd (pc v : Z),
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyd Sd Wd memd mdd 0 ->
freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
(pc = 0x7664 /\ getr regsd 10 = w64 v \/ pc = 0x795c /\ v = 0) ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF ->
hs_frame regs (mrestrict (w_H Wd) memd) (spZ regs) ->
0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyd Sd) -> hb <= h -> h + 480 <= hb + req_size hn ->
hunt_ok Hb -> length (hs_table Hb now) = 400%nat -> length (hs_arb h Hb now) = 32%nat ->
garr8 SEGS (mrestrict (w_H Wd) memd) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
v = hs_verdict h Hb now -> hunt_ok (hs_hunt h Hb now) ->
Permutation (ablocks B lyd Sd) (ablocks B ly S) ->
SRr SEGS Wd (cfg_at (fx := fx) SEGS (BASE + pc) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb lyd Sd Wd regsd memd mdd pc v HPRE HJ HFk HFc Hpc
R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi HOK LT LA HG Hv HOKH HPerm.
pose proof HOK as (LHb & TOKb & LOKb & V0R).
assert (Rv : 0 <= v <= 3).
{ rewrite Hv. unfold hs_verdict. apply reac_hunt_step.hs_dec_range. exact V0R. }
assert (Hold : s32_at (hs_img h now Hb) 440 = s32_at Hb 440).
{ unfold s32_at, u_at. rewrite (hs_img_mid h now Hb LHb LT). reflexivity. }
assert (Hsplice : firstn 440 (hs_img h now Hb) ++ Z_to_le_bytes 4 v ++ skipn 444 (hs_img h now Hb) = hs_hunt h Hb now).
{ rewrite (hs_img_first h now Hb LHb LT), (hs_img_last h now Hb LHb LT). unfold hs_hunt.
  rewrite <- !app_assoc. f_equal. f_equal. rewrite <- Hv. unfold Mem.le4. rewrite unsigned_lit_small by lia. reflexivity. }
exact (hs_epi_core fq0 ly S W regs mem md ch h now hb hn Hb (hs_img h now Hb) lyd Sd Wd regsd memd mdd pc v HPRE HJ HFk HFc Hpc
R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi (hs_img_len h now Hb LHb LT LA) HG Hv Rv Hold V0R Hsplice HOKH HPerm).
Qed.
End w.
Definition hs_pro_chunks : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma hs_frame_of_chunks : forall E m (regs : bvmap 5 word) sp0,
(forall (r : bv 5), ew E (Z.to_nat (bv_unsigned r)) = getr regs r) ->
Forall (YP09.chunk_ok SEGS E m sp0) hs_pro_chunks -> hs_frame regs m sp0.
Proof.
intros E m regs sp0 HE HC. unfold hs_frame. apply Forall_forall. intros [o r] Hp.
assert (HIn : In (YP09.mkChunk (o - 112) (CVal 8 (SOff (Z.to_nat (bv_unsigned r)) 0))) hs_pro_chunks).
{ unfold hs_saved in Hp. cbn [In] in Hp.
  repeat (destruct Hp as [Hp | Hp]; [injection Hp as <- <-; vm_compute; repeat (first [left; reflexivity | right]) |]).
  destruct Hp. }
pose proof (proj1 (Forall_forall _ _) HC _ HIn) as CK.
pose proof (val_of_chunk_ok SEGS E m sp0 (o - 112) 8 (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (getr regs r)) CK) as V.
cbn beta. replace (sp0 - 112 + fst (o, r)) with (sp0 + (o - 112)) by (cbn; lia). apply V.
- cbn [sv_denot]. rewrite HE, Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR. change (bv_modulus 64) with (2 ^ 64) in BR. cbn. lia.
- cbn. lia.
Qed.
Definition L2_PC : Z := 0x78cc.
Definition L2_RET : Z := 0x7918.
Definition L2_EXIT : Z := 0x7664.
Definition l2_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    20%bv (SOff 9 40))
    23%bv (SOff 32 0))
    24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0)))
    26%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 9 40) (SLit 3))))
    22%bv (SLit 2))
    25%bv (SLit 1))
    27%bv (SLit 5000000000).
Definition l2_ent : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 48 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition l2_nreg : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition l2_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, PTR 3); (18%nat, mkAF 0 (2 ^ 64 - 1) 0); (19%nat, PTR 3);
            (21%nat, mkAF 0 7 0); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
            (34%nat, mkAF 0 2 0); (35%nat, mkAF 0 8 0) ] [] [].
Definition l2_ss (pc : Z) : sstate := mkSS pc l2_regs [l2_ent; l2_nreg] None l2_facts.
Definition l2_SH : list shent := [ mkSHE 9 0 48; mkSHE 19 0 8 ].
Definition l2_E (regs : bvmap 5 word) (T : list byte) (i : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (last_of T i); Z_to_bv 64 (role_of_e T i); Z_to_bv 64 (n_of T)]).
Definition l2_regs_at (regs : bvmap 5 word) (sp h now i : Z) : Prop :=
  spZ regs = sp /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (h + 440) /\ getr regs 9 = w64 (h + 48 * i) /\ getr regs 18 = w64 now /\
  getr regs 19 = w64 (h + 384) /\ getr regs 20 = w64 (h + 48 * i + 40) /\ getr regs 21 = w64 i /\
  getr regs 22 = w64 2 /\ getr regs 23 = w64 SB /\ getr regs 24 = w64 (SB + (h + 384) / 8) /\
  getr regs 25 = w64 1 /\ getr regs 26 = w64 (SB + (h + 48 * i + 40) / 8) /\ getr regs 27 = w64 5000000000.
Lemma l2_U_sh : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SB -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 50 ->
  U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = SB + (v + c) / 8 /\
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = (v + c) / 8 + SB.
Proof.
intros E n v c Hn H32 Hv Hc. rewrite !U_SAlu, !U_SOff, !U_SLit, Hn, H32. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SB; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite (zcanon_id (v + c)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 50) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id (SB + 0)) by (unfold M64, SB; lia).
rewrite Z.add_0_r. split; apply zcanon_id; unfold M64, SB; lia.
Qed.
Lemma l2_entry : forall (fq : YK11.FPState) (pc : Z) (W : world SEGS) lyc Sc (regs : bvmap 5 word) memc mdc
  (sp h now i hb hn : Z) (T : list byte),
  AR SEGS B lyc Sc W memc mdc ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn -> h mod 8 = 0 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 ->
  0 <= now < 2 ^ 64 -> 0 <= i < n_of T -> n_of T <= 8 -> 0 <= role_of_e T i <= 2 ->
  length T = 400%nat ->
  l2_regs_at regs sp h now i ->
  garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) T) ->
  st_ok_pi SEGS VAL (l2_E regs T i) (l2_ss pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS HSBx l2_SH (l2_E regs T i) (mrestrict (w_H W) memc).
Proof.
intros fq pc W lyc Sc regs memc mdc sp h now i hb hn T HAR Hin Hlo Hhi Hh8 Hsp Hsp16 Rnow Hi Hn8 Hrole LT HR HG.
destruct HR as (Hspr & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (_ & Hbb4096 & Hbbceil & Hbbapp & _ & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
rewrite restrict_mkst_fx.
set (E := l2_E regs T i).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (last_of T i); Z_to_bv 64 (role_of_e T i); Z_to_bv 64 (n_of T)]) n)
  by (intros n Hn; subst E; unfold l2_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 (h + 48 * i)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (h + 384)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (last_of T i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (role_of_e T i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hspr).
pose proof (l2_u_range T (48 * i + 40) 8) as Rlast'.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rlast'.
assert (Rlast : 0 <= last_of T i < 2 ^ 64) by exact Rlast'.
assert (Urole : u_at T (48 * i + 8) 4 = role_of_e T i)
  by (unfold role_of_e, s32_at in *; apply l2_u32_small; lia).
assert (Un : u_at T 384 4 = n_of T) by (unfold n_of, s32_at in *; apply l2_u32_small; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (UBx : U E HSBx = SHADOW_OFF) by (unfold HSBx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
split.
- unfold l2_ss. apply pa_entry_st_ok_full.
  + unfold l2_regs.
    apply regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; exact R27].
    apply regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; exact R25].
    apply regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; exact R22].
    apply regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite denot_lit_U, (proj1 (l2_U_sh E 9 (h + 48 * i) 40 E9 E32 ltac:(lia) ltac:(lia))). exact R26. }
    apply regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite denot_lit_U. replace (h + 384) with (h + 384 + 0) in R24 by lia.
         rewrite (proj2 (l2_U_sh E 19 (h + 384) 0 E19 E32 ltac:(lia) ltac:(lia))), Z.add_comm. exact R24. }
    apply regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact R23].
    apply regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite denot_lit_U, (U_atom_off E 9 (h + 48 * i) 40 E9) by lia. exact R20. }
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold l2_ent, l2_nreg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem].
    * rewrite (VB 9%nat (h + 48 * i) E9) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (h + 48 * i) 8 4 (SOff 34 0) (role_of_e T i));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite <- Urole. replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia.
         apply (l2_val _ T h (48 * i + 8) 4 HG); lia.
      -- apply (chunk_ok_val SEGS E _ (h + 48 * i) 40 8 (SOff 33 0) (u_at T (48 * i + 40) 8));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (h + 48 * i + 40) with (h + (48 * i + 40)) by lia.
         apply (l2_val _ T h (48 * i + 40) 8 HG); lia.
    * rewrite (VB 19%nat (h + 384) E19) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (h + 384) 0 4 (SOff 35 0) (n_of T));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, <- Un. apply (l2_val _ T h 384 4 HG); lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, l2_ent, l2_nreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat (h + 48 * i) E9) by lia. rewrite (VB 19%nat (h + 384) E19) by lia.
    split; [split; [lia | exact I] | split; [exact I | exact I]].
  + split; [|split; [exact I | exact I]].
    cbn [l2_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E9, E18, E19, E21, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hlo Hhi Hbb4096 Hbbceil Hh8 Hsp Hsp16 Rnow Hi Hn8 Hrole Rlast C1 Hrq0 Hrq1. clear. unfold SB. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    all: Z.div_mod_to_equations; lia.
- unfold sh_ok, l2_SH. constructor; [|constructor; [|constructor]].
  + eapply (shent_ok_of_range SEGS (w_H W) memc E HSBx 9 (h + 48 * i) 48 (h + 48 * i) 0 48).
    * eapply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn (h + 48 * i) 48 HAR Hin); lia.
    * exact UBx.
    * apply (U_atom E 9 (h + 48 * i) E9). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      unfold SHADOW_OFF in *. revert Hx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 C1 C3 Hi Hn8.
      clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
  + eapply (shent_ok_of_range SEGS (w_H W) memc E HSBx 19 (h + 384) 8 (h + 384) 0 8).
    * eapply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn (h + 384) 8 HAR Hin); lia.
    * exact UBx.
    * apply (U_atom E 19 (h + 384) E19). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      unfold SHADOW_OFF in *. revert Hx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 C1 C3.
      clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Definition L2_NEXT : Z := 0x791c.
Definition L2_LIVE : Z := 0x78e4.
Definition l2_win (sp0 a : Z) : Prop := sp0 - 112 - REAC_SENDER_KIND_STK <= a < sp0 - 112.
Definition l2_mem (W : world SEGS) (memr : word -> option byte) (h : Z) (T : list byte) : Prop :=
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memr) /\
  range_addressable (aview SEGS (w_H W) memr) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
  garr8 SEGS (mrestrict (w_H W) memr) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
  val_mem SEGS (mrestrict (w_H W) memr) (VAL (A_HI 97) + -1832) 8 D6000 /\
  val_mem SEGS (mrestrict (w_H W) memr) (VAL (A_HI 96) + -1628) 8 D3837 /\
  garr8 SEGS (mrestrict (w_H W) memr) h (map (fun b : byte => bv_unsigned b) T).
Lemma l2_aview_kept : forall H (m m' : word -> option byte) (P : Z -> Prop),
  (forall a : word, ~ P (bv_unsigned a) -> m' a = m a) ->
  forall x, ~ P (x mod 2 ^ 64) -> aview SEGS H m' x = aview SEGS H m x.
Proof.
intros H m m' P Hk x Hx. apply (aview_eq_of SEGS). unfold mrestrict. rewrite Hk; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hx.
Qed.
Lemma l2_ro_low : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
- apply pa_segs_low. apply pa_relro_img. exact Hr.
Qed.
Lemma l2_hi_near : forall kk (rd : bv 5) j, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  exists s, - 2 ^ 31 <= s < 2 ^ 31 /\ VAL (A_HI j) = (BASE + kk + s) mod 2 ^ 64 /\ 0 <= BASE + kk < kLowMemEnd.
Proof.
intros kk rd j Hk40 Hk. pose proof pa_B_ok as HB.
rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert kk _ Hk) as [Hc [Hk0 Hk4]].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + kk)) as [wz|] eqn:Hf; [|discriminate Hc].
assert (Himg : 0 <= BASE + kk < kLowMemEnd).
{ pose proof (pa_tbl_ok _ _ Hf) as Hfw.
  unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
  unfold code_read in Hfw.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
  destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
  assert (HI : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk)))).
  { exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
  pose proof (pa_segs_low _ HI) as HR.
  rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  rewrite Z.mod_small in HR by lia. lia. }
destruct (decode_any (Z_to_bv 32 wz)) as [[ins isz]|]; [|discriminate Hc].
apply andb_prop in Hc as [_ Hc]. destruct ins; try (cbn in Hc; discriminate Hc).
apply andb_prop in Hc as [_ Hc]. apply Z.eqb_eq in Hc. unfold auipc_val, zcanon, M64 in Hc.
exists (bv_signed (bv_concat 32 imm (Z_to_bv 12 0))).
pose proof (bv_signed_in_range 32 (bv_concat 32 imm (Z_to_bv 12 0)) ltac:(discriminate)) as Hr.
change (bv_half_modulus 32) with (2 ^ 31) in Hr.
split; [lia|]. split; [rewrite <- Hc; reflexivity | exact Himg].
Qed.
Lemma l2_hi_win : forall kk (rd : bv 5) j c x lo hi, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  -4096 <= c <= 4096 -> 0 <= x < 8 -> alloc_ceiling <= lo -> hi <= 2 ^ 47 ->
  ~ (lo <= (VAL (A_HI j) + c + x) mod 2 ^ 64 < hi).
Proof.
intros kk rd j c x lo hi Hk40 Hk Hc Hx Hlo Hhi.
destruct (l2_hi_near kk rd j Hk40 Hk) as (s & Hs & Hv & Hb).
pose proof (asan_consts) as (C1 & _ & _ & _ & C5).
rewrite Hv. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
revert Hs Hb Hc Hx Hlo Hhi C1 C5. clear. intros. Z.div_mod_to_equations. lia.
Qed.
Lemma l2_mem_kept : forall W memr memc h T sp0,
  l2_mem W memr h T -> (forall a : word, ~ l2_win sp0 (bv_unsigned a) -> memc a = memr a) ->
  alloc_ceiling <= sp0 - 112 - REAC_SENDER_KIND_STK -> sp0 <= 2 ^ 47 -> 0 <= h -> h + 400 <= alloc_ceiling ->
  length T = 400%nat -> l2_mem W memc h T.
Proof.
intros W memr memc h T sp0 (H1 & H2 & H3 & H4 & H5 & H6) Hk Hlo Hhi Hh0 Hh1 LT.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (AK : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) memc x = aview SEGS (w_H W) memr x).
{ intros x Hx. apply (l2_aview_kept (w_H W) memr memc (l2_win sp0) Hk). rewrite Z.mod_small by lia. unfold l2_win. lia. }
pose proof (pa_obj_img 65 ltac:(unfold disco_nobj; lia)) as H65.
assert (HimgL : 0 <= IMG_LO /\ IMG_TOP <= kLowMemEnd) by (unfold IMG_LO, IMG_TOP, kLowMemEnd; lia).
assert (LR : length RATES = 12%nat) by reflexivity.
split; [|split; [|split; [|split; [|split]]]].
- intros a Hro Ho He. pose proof (l2_ro_low a Hro) as Ha. rewrite AK by lia. exact (H1 a Hro Ho He).
- intros x Hx. destruct (H2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite AK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
  revert Hx H65 HimgL C1 C5. clear. intros. Z.div_mod_to_equations. lia.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) memr memc); [|exact H3].
  intros a Ha. rewrite length_map, LR in Ha. apply AK. lia.
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memr memc); [|exact H4].
  intros x Hx. apply (l2_aview_kept (w_H W) memr memc (l2_win sp0) Hk).
  replace x with (VAL (A_HI 97) + -1832 + (x - (VAL (A_HI 97) + -1832))) by lia.
  unfold l2_win. apply (l2_hi_win 31476 11%bv 97 (-1832) (x - (VAL (A_HI 97) + -1832))); [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memr memc); [|exact H5].
  intros x Hx. apply (l2_aview_kept (w_H W) memr memc (l2_win sp0) Hk).
  replace x with (VAL (A_HI 96) + -1628 + (x - (VAL (A_HI 96) + -1628))) by lia.
  unfold l2_win. apply (l2_hi_win 31472 10%bv 96 (-1628) (x - (VAL (A_HI 96) + -1628))); [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) memr memc); [|exact H6].
  intros a Ha. rewrite length_map, LT in Ha. apply AK. lia.
Qed.
Lemma l2_frame_ro : forall E rs (m m' : word -> option byte), forallb (fun r => r_whi r <=? r_wlo r) rs = true ->
  frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hr & Ha).
apply (proj1 (forallb_forall _ rs) Hro r) in Hr. apply Z.leb_le in Hr. lia.
Qed.
Lemma l2_blt : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. unfold U in Ha, Hb. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite Ha, Hb.
assert (Hs : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z).
{ intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
rewrite !Hs by lia. reflexivity.
Qed.
Definition l2_cont (fq : YK11.FPState) (Q : world SEGS -> config -> Prop) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (sp0 h now : Z) (T : list byte) (W : world SEGS)
  (memr : word -> option byte) (bl0 : list (Z * Z)) : Prop :=
  forall (fq' : YK11.FPState) (lyd : alayout) (Sd : astate) (Wd : world SEGS) (memd : word -> option byte)
    (mdd : Model) (regsd : bvmap 5 word) (v : Z),
  freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') -> hs_csr fq fq' ->
  ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd Wd memd mdd 0 ->
  v = (if box_present h T now then 1 else 0) ->
  Wd = W -> Permutation (ablocks B lyd Sd) bl0 ->
  (forall a : word, ~ l2_win sp0 (bv_unsigned a) -> memd a = memr a) ->
  spZ regsd = sp0 - 112 -> getr regsd 3 = w64 (as_gp B) -> getr regsd 4 = w64 (as_tp B) ->
  getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SB -> getr regsd 10 = w64 v ->
  SRr SEGS Wd (cfg_at (fx := fq') SEGS (BASE + L2_EXIT) regsd memd mdd) Q.
Lemma l2_cont_trans : forall fq fq2 Q ly S W0 mem0 md0 sp0 h now T W memr bl0,
  l2_cont fq Q ly S W0 mem0 md0 sp0 h now T W memr bl0 ->
  freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq2) -> hs_csr fq fq2 ->
  l2_cont fq2 Q ly S W0 mem0 md0 sp0 h now T W memr bl0.
Proof.
intros fq fq2 Q ly S W0 mem0 md0 sp0 h now T W memr bl0 HK Hf Hc fq' lyd Sd Wd memd mdd regsd v Hf' Hc'.
apply HK; [exact (reac_hunt_step.hs_freg_trans _ _ _ Hf Hf') | exact (hs_csr_trans _ _ _ Hc Hc')].
Qed.
Definition l2_it (fq : YK11.FPState) (Q : world SEGS -> config -> Prop) (ly lyc : alayout) (S Sc : astate)
  (W0 W : world SEGS) (mem0 memr memc : word -> option byte) (md0 mdc : Model) (regs : bvmap 5 word)
  (sp0 h now hb hn i : Z) (T : list byte) (bl0 : list (Z * Z)) : Prop :=
  ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyc Sc W memc mdc 0 /\
  l2_mem W memr h T /\
  (forall a : word, ~ l2_win sp0 (bv_unsigned a) -> memc a = memr a) /\
  Permutation (ablocks B lyc Sc) bl0 /\ In (hb, hn) bl0 /\ hb <= h /\ h + 480 <= hb + req_size hn /\ h mod 8 = 0 /\
  length T = 400%nat /\ table_ok T /\ 0 <= now < 2 ^ 64 /\ 0 <= i < n_of T /\
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fb h T now j = false) /\
  l2_regs_at regs (sp0 - 112) h now i /\
  l2_cont fq Q ly S W0 mem0 md0 sp0 h now T W memr bl0.
Definition l2_P (k : nat) : Prop :=
  forall (fq : YK11.FPState) (Q : world SEGS -> config -> Prop) (ly lyc : alayout) (S Sc : astate) (W0 W : world SEGS)
    (mem0 memr memc : word -> option byte) (md0 mdc : Model) (regs : bvmap 5 word) (sp0 h now hb hn i : Z)
    (T : list byte) (bl0 : list (Z * Z)),
  Z.of_nat k = n_of T - i ->
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + L2_PC) regs memc mdc) Q.
Lemma l2_start : forall (fq : YK11.FPState) (pc : Z) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0,
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  st_ok_pi SEGS VAL (l2_E regs T i) (l2_ss pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS HSBx l2_SH (l2_E regs T i) (mrestrict (w_H W) memc) /\
  img_env VAL A_LIM (l2_E regs T i) /\
  ew (l2_E regs T i) 2 = getr regs 2 /\ ew (l2_E regs T i) 3 = Z_to_bv 64 (as_gp B) /\
  ew (l2_E regs T i) 4 = Z_to_bv 64 (as_tp B) /\ ew (l2_E regs T i) 8 = Z_to_bv 64 (h + 440) /\
  ew (l2_E regs T i) 9 = Z_to_bv 64 (h + 48 * i) /\ ew (l2_E regs T i) 10 = getr regs 10 /\
  ew (l2_E regs T i) 18 = Z_to_bv 64 now /\ ew (l2_E regs T i) 19 = Z_to_bv 64 (h + 384) /\
  ew (l2_E regs T i) 21 = Z_to_bv 64 i /\ ew (l2_E regs T i) 32 = Z_to_bv 64 SB /\
  ew (l2_E regs T i) 33 = Z_to_bv 64 (last_of T i) /\ ew (l2_E regs T i) 34 = Z_to_bv 64 (role_of_e T i) /\
  ew (l2_E regs T i) 35 = Z_to_bv 64 (n_of T) /\
  In (hb, hn) (ablocks B lyc Sc) /\ 0 <= n_of T <= 8 /\ 0 <= role_of_e T i <= 2 /\ 0 <= last_of T i < 2 ^ 64 /\
  l2_mem W memc h T /\ alloc_ceiling <= sp0 - 8432 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ 4096 <= h /\
  h + 480 <= alloc_ceiling.
Proof.
intros fq pc Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 HIT.
destruct HIT as (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (WK : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (HinC : In (hb, hn) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | exact Hin0]).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR HinC) as (_ & Hbb4096 & Hbbceil & _ & _ & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
destruct HTOK as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
assert (Hrole : 0 <= role_of_e T i <= 2) by (destruct (T2 i Hi) as [R|[R|R]]; rewrite R; lia).
pose proof (l2_u_range T (48 * i + 40) 8) as Rlast'.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rlast'.
assert (Rlast : 0 <= last_of T i < 2 ^ 64) by exact Rlast'.
assert (HMEMc : l2_mem W memc h T)
  by (apply (l2_mem_kept W memr memc h T sp0 HMEM HKEPT); [rewrite WK; lia | lia | lia | lia | exact LT]).
pose proof HMEMc as (_ & _ & _ & _ & _ & HG).
pose proof HR as (Hspr & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct (l2_entry fq pc W lyc Sc regs memc mdc (sp0 - 112) h now i hb hn T HAR HinC Hlo Hhi Hh8
  ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) Rnow Hi ltac:(lia) Hrole LT HR HG) as [HS SHOK].
set (E := l2_E regs T i).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (last_of T i); Z_to_bv 64 (role_of_e T i); Z_to_bv 64 (n_of T)]) n)
  by (intros n Hn; subst E; unfold l2_E; apply Eimg_low; exact Hn).
split; [exact HS|]. split; [exact SHOK|]. split; [subst E; unfold l2_E; apply Eimg_env|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact R3|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact R4|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19|].
split; [rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)|].
split; [exact HinC|]. split; [lia|]. split; [exact Hrole|]. split; [exact Rlast|].
split; [exact HMEMc|]. repeat split; lia.
Qed.
Ltac l2_meq HS :=
  lazymatch goal with
  | HF : frame_of _ ?rs ?m0 ?m1, HMEQ : forall x : word, ?m0 x = ?M x |- _ =>
    let Hn := fresh "HMEQ" in
    assert (Hn : forall x : word, m1 x = M x)
      by (intros x; rewrite (l2_frame_ro _ rs m0 m1 ltac:(vm_compute; reflexivity) HF x); exact (HMEQ x));
    clear HMEQ; rename Hn into HMEQ
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  let m := lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?m) => m
    | st_ok _ _ _ (restrict _ ?m) => m
    end in
  repeat match goal with o : machine_state |- _ => lazymatch o with m => fail | _ => clear o end end;
  try rename m into ms.
Ltac l2_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Lemma l2_U_add_lit : forall E a c, U E (SAlu ALU_ADD a (SLit c)) = zcanon (U E a + zcanon c).
Proof. intros. rewrite U_SAlu, U_SLit. reflexivity. Qed.
Lemma l2_freg_refl : forall F, freg_kept F F.
Proof. intros F r _ _ _. reflexivity. Qed.
Lemma l2_next : forall k, l2_P k -> forall (fq : YK11.FPState) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0,
  Z.of_nat k = n_of T - i - 1 ->
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  reac_hunt_step.hs_fb h T now i = false ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + L2_NEXT) regs memc mdc) Q.
Proof.
intros k IH fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 Hk HIT HFB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (l2_start fq L2_NEXT Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 HIT)
  as (HS & SHOK & HEI & E2 & E3 & E4 & E8 & E9 & E10 & E18 & E19 & E21 & E32 & E33 & E34 & E35 & HinC & Hn8 & Hrole & Rlast &
      HMEMc & Hceil & H47 & Hal16 & Hh4096 & Hhc).
pose proof HIT as (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK).
pose proof HR as (Hspr & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
unfold l2_cont in HK.
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := l2_E regs T i) in *.
assert (HMEQ : forall x : word, memc x = memc x) by reflexivity.
unfold cfg_at. change (w64 (BASE + L2_NEXT)) with (Z_to_bv 64 (BASE + L2_NEXT)).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
l2_meq HS.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (l2_blt E _ _ (i + 1) (n_of T) (U_atom_off E 21 i 1 E21 ltac:(lia) ltac:(lia)) (U_atom E 35 (n_of T) E35 ltac:(lia)))
    in Hc by lia.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_PC. { awr_ok_tac. }
  l2_meq HS.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (25%bv : bv 5) N25.
  prreg HS (27%bv : bv 5) N27.
  l2_rreg HS (24%bv : bv 5) N24. l2_rreg HS (26%bv : bv 5) N26.
  assert (HRn : l2_regs_at (ms_regs ms) (sp0 - 112) h now (i + 1)).
  { unfold l2_regs_at, spZ, w64.
    rewrite N2, N3, N4, N8, N9, N18, N19, N20, N21, N22, N23, N25, N27, E2, E3, E4, E8, E9, E18, E19, E21, E32.
    rewrite !unsigned_lit_small by lia.
    split; [exact Hspr|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [f_equal; lia|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    { rewrite N24, denot_lit_U. replace (h + 384) with (h + 384 + 0) by lia.
      rewrite (proj2 (l2_U_sh E 19 (h + 384) 0 E19 E32 ltac:(lia) ltac:(lia))). f_equal. lia. }
    split; [reflexivity|]. split; [|reflexivity].
    rewrite N26, denot_lit_U, l2_U_add_lit, (proj1 (l2_U_sh E 9 (h + 48 * i) 40 E9 E32 ltac:(lia) ltac:(lia))).
    rewrite (zcanon_id 6) by (unfold M64; lia).
    assert (Hd : (h + 48 * (i + 1) + 40) / 8 = (h + 48 * i + 40) / 8 + 6)
      by (replace (h + 48 * (i + 1) + 40) with (h + 48 * i + 40 + 6 * 8) by lia; apply Z.div_add; lia).
    rewrite Hd. f_equal.
    assert (0 <= (h + 48 * i + 40) / 8 < 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite zcanon_id; [lia|]. unfold M64, SB. lia. }
  pmkst HS.
  eapply (IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn (i + 1) T bl0).
  + lia.
  + split; [exact HJ|]. split; [exact HMEM|]. split; [intros a Ha; rewrite HMEQ; exact (HKEPT a Ha)|].
    split; [exact HPERM|]. split; [exact Hin0|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hh8|].
    split; [exact LT|]. split; [exact HTOK|]. split; [exact Rnow|]. split; [lia|].
    split; [intros j Hj; destruct (Z.eq_dec j i) as [->|Hji]; [exact HFB | apply HNW; lia]|].
    split; [exact HRn|]. exact HK.
- rewrite (l2_blt E _ _ (i + 1) (n_of T) (U_atom_off E 21 i 1 E21 ltac:(lia) ltac:(lia)) (U_atom E 35 (n_of T) E35 ltac:(lia)))
    in Hc by lia.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_EXIT. { awr_ok_tac. }
  l2_meq HS.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (23%bv : bv 5) N23. prreg HS (10%bv : bv 5) N10.
  pmkst HS.
  apply (HK fq lyc Sc W (ms_mem ms) _ (ms_regs ms) 0).
  + apply l2_freg_refl.
  + apply hs_csr_refl.
  + exact HJ.
  + rewrite (reac_hunt_step.hs_bp_false h T now); [reflexivity|].
    intros j Hj. destruct (Z.eq_dec j i) as [->|Hji]; [exact HFB | apply HNW; lia].
  + reflexivity.
  + exact HPERM.
  + intros a Ha. rewrite HMEQ. exact (HKEPT a Ha).
  + unfold spZ. rewrite N2, E2. exact Hspr.
  + rewrite N3. exact E3.
  + rewrite N4. exact E4.
  + rewrite N8. exact E8.
  + rewrite N23. exact E32.
  + rewrite N10. reflexivity.
Qed.
Definition l2_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac l2_in := cbn [In l2_kept]; repeat (first [left; reflexivity | right]).
Lemma l2_regs_at_ext : forall (regs regs' : bvmap 5 word) sp h now i,
  (forall r, In r l2_kept -> getr regs' r = getr regs r) ->
  l2_regs_at regs sp h now i -> l2_regs_at regs' sp h now i.
Proof.
intros regs regs' sp h now i HE HR. unfold l2_regs_at, spZ in *.
rewrite !HE by l2_in. exact HR.
Qed.
Lemma l2_same_regs : forall (fq : YK11.FPState) E ss0 ss ms0 ms H,
  st_ok_pi (fx := fq) SEGS VAL E ss0 (restrict H ms0) -> st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get (ss_regs ss0) r)) l2_kept = true ->
  forall r, In r l2_kept -> getr (ms_regs ms) r = getr (ms_regs ms0) r.
Proof.
intros fq E ss0 ss ms0 ms H HS0 HS Hf r Hr.
rewrite (st_ok_pi_restrict_reg H E ss ms r HS), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0).
f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ l2_kept) Hf r Hr).
Qed.
Lemma l2_it_gen : forall (fq : YK11.FPState) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0
  lyc' Sc' memc' mdc' regs' (fq' : YK11.FPState),
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyc' Sc' W memc' mdc' 0 ->
  Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
  (forall a : word, ~ l2_win sp0 (bv_unsigned a) -> memc' a = memc a) ->
  (forall r, In r l2_kept -> getr regs' r = getr regs r) ->
  freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') -> hs_csr fq fq' ->
  l2_it fq' Q ly lyc' S Sc' W0 W mem0 memr memc' md0 mdc' regs' sp0 h now hb hn i T bl0.
Proof.
intros fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc' Sc' memc' mdc' regs' fq'
  (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK) HJ' HP HKc HRg Hf Hc.
split; [exact HJ'|]. split; [exact HMEM|].
split; [intros a Ha; rewrite (HKc a Ha); exact (HKEPT a Ha)|].
split; [eapply Permutation_trans; [exact HP | exact HPERM]|].
do 9 (split; [assumption|]).
split; [exact (l2_regs_at_ext regs regs' _ _ _ _ HRg HR)|].
exact (l2_cont_trans fq fq' Q ly S W0 mem0 md0 sp0 h now T W memr bl0 HK Hf Hc).
Qed.
Lemma l2_after : forall k, l2_P k -> forall (fq : YK11.FPState) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0,
  Z.of_nat k = n_of T - i - 1 ->
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  disco_stale T i now = false -> role_of_e T i = 0 -> getr regs 10 = w64 (hs_kind h T now i) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + L2_RET) regs memc mdc) Q.
Proof.
intros k IH fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 Hk HIT Hst Hr0 H10.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (l2_start fq L2_RET Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 HIT)
  as (HS & SHOK & HEI & E2 & E3 & E4 & E8 & E9 & E10 & E18 & E19 & E21 & E32 & E33 & E34 & E35 & HinC & Hn8 & Hrole & Rlast &
      HMEMc & Hceil & H47 & Hal16 & Hh4096 & Hhc).
pose proof HIT as (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK).
pose proof HR as (Hspr & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
unfold l2_cont in HK.
pose proof (reac_hunt_step.hs_sk_range (h + 48 * i) (role_of_e T i) (hd_of T i) (slots_of T i) (ch_of T i) (fs_of T i) now) as KR.
change (reac_sender_kind_model (h + 48 * i) (role_of_e T i) (hd_of T i) (slots_of T i) (ch_of T i) (fs_of T i) now)
  with (hs_kind h T now i) in KR.
assert (HFB : reac_hunt_step.hs_fb h T now i = (hs_kind h T now i =? 2)) by (unfold reac_hunt_step.hs_fb; rewrite Hst, Hr0; reflexivity).
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := l2_E regs T i) in *.
pose proof HS as HS0.
assert (HMEQ : forall x : word, memc x = memc x) by reflexivity.
unfold cfg_at. change (w64 (BASE + L2_RET)) with (Z_to_bv 64 (BASE + L2_RET)).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
l2_meq HS.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, (U_atom E 10 (hs_kind h T now i)), U_lit in Hc by (first [rewrite E10, H10; reflexivity | lia]).
  apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_EXIT. { awr_ok_tac. }
  l2_meq HS.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (23%bv : bv 5) N23. prreg HS (10%bv : bv 5) N10.
  pmkst HS.
  apply (HK fq lyc Sc W (ms_mem ms) _ (ms_regs ms) 1).
  + apply l2_freg_refl.
  + apply hs_csr_refl.
  + exact HJ.
  + rewrite (reac_hunt_step.hs_bp_true h T now i Hi); [reflexivity|]. rewrite HFB, Hc. reflexivity.
  + reflexivity.
  + exact HPERM.
  + intros a Ha. rewrite HMEQ. exact (HKEPT a Ha).
  + unfold spZ. rewrite N2, E2. exact Hspr.
  + rewrite N3. exact E3.
  + rewrite N4. exact E4.
  + rewrite N8. exact E8.
  + rewrite N23. exact E32.
  + rewrite N10. reflexivity.
- rewrite branch_eq_U, (U_atom E 10 (hs_kind h T now i)), U_lit in Hc by (first [rewrite E10, H10; reflexivity | lia]).
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_NEXT. { awr_ok_tac. }
  l2_meq HS.
  pose proof (l2_same_regs fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
  pmkst HS.
  eapply (l2_next k IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn i T bl0 Hk).
  + apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc Sc (ms_mem ms) _ (ms_regs ms) fq HIT HJ).
    * apply Permutation_refl.
    * intros a _. exact (HMEQ a).
    * exact HRK.
    * apply l2_freg_refl.
    * apply hs_csr_refl.
  + rewrite HFB. apply Z.eqb_neq. exact Hc.
Qed.
Lemma l2_pres_kept : forall regs regs', aregs_preserved regs regs' -> forall r, In r l2_kept -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. cbn [In l2_kept] in Hr.
repeat (destruct Hr as [<-|Hr];
  [match goal with |- getr _ ?r = _ => let z := eval vm_compute in (bv_unsigned r) in
     exact (HP z ltac:(unfold acallee_saved; lia)) end|]).
destruct Hr.
Qed.
Lemma l2_same_regs_call : forall (fq : YK11.FPState) E ss0 ss ms0 ms H,
  st_ok_pi (fx := fq) SEGS VAL E ss0 (restrict H ms0) -> st_ok (fx := fq) SEGS E ss (restrict H ms) ->
  forallb (fun r => sv_eqb (sr_get (ss_regs ss) r) (sr_get (ss_regs ss0) r)) l2_kept = true ->
  forall r, In r l2_kept -> getr (ms_regs ms) r = getr (ms_regs ms0) r.
Proof.
intros fq E ss0 ss ms0 ms H HS0 HS Hf r Hr.
rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), (st_ok_pi_restrict_reg H E ss0 ms0 r HS0).
f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ l2_kept) Hf r Hr).
Qed.
Lemma l2_live : forall k, l2_P k -> forall (fq : YK11.FPState) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0,
  Z.of_nat k = n_of T - i - 1 ->
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  disco_stale T i now = false ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + L2_LIVE) regs memc mdc) Q.
Proof.
intros k IH fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 Hk HIT Hst.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (l2_start fq L2_LIVE Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 HIT)
  as (HS & SHOK & HEI & E2 & E3 & E4 & E8 & E9 & E10 & E18 & E19 & E21 & E32 & E33 & E34 & E35 & HinC & Hn8 & Hrole & Rlast &
      HMEMc & Hceil & H47 & Hal16 & Hh4096 & Hhc).
pose proof HIT as (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK).
pose proof HR as (Hspr & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
unfold l2_cont in HK.
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (WK : REAC_SENDER_KIND_STK = 4224) by reflexivity.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := l2_E regs T i) in *.
pose proof HS as HS0.
assert (HMEQ : forall x : word, memc x = memc x) by reflexivity.
unfold cfg_at. change (w64 (BASE + L2_LIVE)) with (Z_to_bv 64 (BASE + L2_LIVE)).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
l2_meq HS.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, (U_atom E 34 (role_of_e T i) E34), U_lit in Hc by lia.
  apply Z.eqb_eq in Hc. rename Hc into Hr0.
  paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
  l2_meq HS.
  pose proof (l2_same_regs_call fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
  cbn [ms_regs mkst] in HRK.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  pose proof (proj1 HJ) as HARc.
  assert (HMEMs : l2_mem W (ms_mem ms) h T)
    by (apply (l2_mem_kept W memc (ms_mem ms) h T sp0 HMEMc); [intros a _; exact (HMEQ a) | rewrite WK; lia | lia | lia | lia | exact LT]).
  pmkst HS.
  rewrite pa_sigma_reac_sender_kind.
  destruct HMEMs as (HROs & HRAs & HRTs & HD6s & HD3s & HGs).
  destruct (al_blocks _ _ LAWS lyc Sc W (ms_mem ms) _ hb hn HARc HinC) as (_ & Hbb4096 & Hbbceil & Hbbapp & Hbbpres & _ & Hbbn).
  pose proof (blk_off_imgP B lyc Sc W (ms_mem ms) _ hb hn HARc HinC) as Hbimg.
  pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
  assert (Hsp1 : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ; rewrite Q2, E2; exact Hspr).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (Urole : u_at T (48 * i + 8) 4 = role_of_e T i)
    by (unfold role_of_e, s32_at in *; apply l2_u32_small; lia).
  pose proof (l2_u_range T (48 * i + 12) 1) as Rd. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in Rd.
  pose proof (l2_u_range T (48 * i + 16) 1) as Rs. change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in Rs.
  pose proof (l2_u_range T (48 * i + 20) 4) as Rc. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rc.
  pose proof (l2_u_range T (48 * i + 32) 8) as Rf. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rf.
  eapply SRr_bind.
  { eapply (TSENDER fq lyc Sc W (ms_regs ms) (ms_mem ms) _ [] (h + 48 * i) now 0 (role_of_e T i) (hd_of T i)
      (slots_of T i) (ch_of T i) (fs_of T i)).
    - eapply (afn_pre_at SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyc Sc W (ms_mem ms) _ 0 (ms_regs ms)
        REAC_SENDER_KIND_STK (-112) [] HJ).
      + rewrite Hsp1. lia.
      + reflexivity.
      + lia.
      + rewrite WK. lia.
      + rewrite WK, WS. lia.
      + rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      + unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold IMG_LO in HBLO. lia.
      + rewrite Q3. exact E3.
      + rewrite Q4. exact E4.
      + apply achain_low. unfold s0Z. rewrite Q8, E8, unsigned_lit_small by lia. lia.
    - exact HROs.
    - rewrite Q10, E9. reflexivity.
    - lia.
    - revert Hh8. clear. intros. Z.div_mod_to_equations. lia.
    - rewrite Q11, E18. reflexivity.
    - exact Rnow.
    - rewrite Q12. reflexivity.
    - lia.
    - intros _.
      split; [lia|]. split; [revert Hbbapp; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia|].
      split; [revert Hbimg; unfold off_img; intros; lia|].
      split; [eapply (range_addressable_of_block SEGS B LAWS lyc Sc W (ms_mem ms) _ hb hn (h + 48 * i + 8) 32 HARc HinC); lia|].
      split; [intros a Ha; exact (proj1 (Hbbpres a ltac:(lia)))|].
      split; [lia|]. split; [exact Rd|]. split; [exact Rs|]. split; [exact Rc|]. split; [exact Rf|].
      split; [rewrite <- Urole; replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia; apply (l2_val _ T h (48 * i + 8) 4 HGs); lia|].
      split; [replace (h + 48 * i + 12) with (h + (48 * i + 12)) by lia; apply (l2_val _ T h (48 * i + 12) 1 HGs); lia|].
      split; [replace (h + 48 * i + 16) with (h + (48 * i + 16)) by lia; apply (l2_val _ T h (48 * i + 16) 1 HGs); lia|].
      split; [replace (h + 48 * i + 20) with (h + (48 * i + 20)) by lia; apply (l2_val _ T h (48 * i + 20) 4 HGs); lia|].
      replace (h + 48 * i + 32) with (h + (48 * i + 32)) by lia; apply (l2_val _ T h (48 * i + 32) 8 HGs); lia.
    - exact HRAs.
    - exact HRTs.
    - exact HD6s.
    - exact HD3s. }
  cbv beta. intros W2 c2 Hwle2 (fq2 & Hfk & Hcsr & fq3 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr3 & Hcs3 & HJ2 & HP2 & Ha0 & HPerm2 & HW2 & Hkept2).
  pose proof (hs_freg_apost _ _ _ Hfk Hfr3) as Hfk3. rewrite Hcsr in Hcs3. clear Hfk Hcsr Hfr3. clear fq2.
  rename fq3 into fq2. rename Hfk3 into Hfk. rename Hcs3 into Hcsr.
  subst W2. rewrite Q1.
  assert (HJc : ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 ([] ++ []) ly2 S2 W mem2 md2 (0 + 0)).
  { eapply (ajournal_sub SEGS B LAWS pa_segs_low);
      [exact HJ | exact HJ2 | rewrite Hsp1, WK, WS; lia | rewrite Hsp1; lia | intros a (r & Hr & _); destruct Hr]. }
  eapply (l2_after k IH fq2 Q ly ly2 S S2 W0 W mem0 memr mem2 md0 md2 regs2 sp0 h now hb hn i T bl0 Hk).
  + apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ly2 S2 mem2 md2 regs2 fq2 HIT HJc HPerm2).
    * intros a Ha. rewrite (Hkept2 a); [exact (HMEQ a)|]. rewrite Hsp1. exact Ha.
    * intros r Hr. rewrite (l2_pres_kept _ _ HP2 r Hr). exact (HRK r Hr).
    * exact Hfk.
    * exact Hcsr.
  + exact Hst.
  + exact Hr0.
  + exact Ha0.
- rewrite branch_eq_U, (U_atom E 34 (role_of_e T i) E34), U_lit in Hc by lia.
  apply Z.eqb_neq in Hc. rename Hc into Hr0.
  paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
  l2_meq HS.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_eq_U, (U_atom E 34 (role_of_e T i) E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_EXIT. { awr_ok_tac. }
    l2_meq HS.
    prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
    prreg HS (23%bv : bv 5) N23. prreg HS (10%bv : bv 5) N10.
    pmkst HS.
    apply (HK fq lyc Sc W (ms_mem ms) _ (ms_regs ms) 1).
    * apply l2_freg_refl.
    * apply hs_csr_refl.
    * exact HJ.
    * rewrite (reac_hunt_step.hs_bp_true h T now i Hi); [reflexivity|]. unfold reac_hunt_step.hs_fb. rewrite Hst, Hc. reflexivity.
    * reflexivity.
    * exact HPERM.
    * intros a Ha. rewrite HMEQ. exact (HKEPT a Ha).
    * unfold spZ. rewrite N2, E2. exact Hspr.
    * rewrite N3. exact E3.
    * rewrite N4. exact E4.
    * rewrite N8. exact E8.
    * rewrite N23. exact E32.
    * rewrite N10, E34, Hc. reflexivity.
  + rewrite branch_eq_U, (U_atom E 34 (role_of_e T i) E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_NEXT. { awr_ok_tac. }
    l2_meq HS.
    pose proof (l2_same_regs fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
    pmkst HS.
    eapply (l2_next k IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn i T bl0 Hk).
    * apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc Sc (ms_mem ms) _ (ms_regs ms) fq HIT HJ).
      -- apply Permutation_refl.
      -- intros a _. exact (HMEQ a).
      -- exact HRK.
      -- apply l2_freg_refl.
      -- apply hs_csr_refl.
    * unfold reac_hunt_step.hs_fb. rewrite Hst.
      replace (role_of_e T i =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hc).
      replace (role_of_e T i =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). reflexivity.
Qed.
Lemma l2_U_sub : forall E a b x y, U E a = x -> U E b = y -> 0 <= y <= x -> x < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = x - y.
Proof.
intros E a b x y Ha Hb Hr Hx. rewrite U_SAlu, U_SMd, U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Z.mul_mod_idemp_r by lia. rewrite Z.add_mod_idemp_r by lia.
replace (x + y * -1) with (x - y) by lia. apply Z.mod_small. lia.
Qed.
Lemma l2_head : forall k, l2_P k -> forall (fq : YK11.FPState) Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0,
  Z.of_nat k = n_of T - i - 1 ->
  l2_it fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + L2_PC) regs memc mdc) Q.
Proof.
intros k IH fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 Hk HIT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct (l2_start fq L2_PC Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 HIT)
  as (HS & SHOK & HEI & E2 & E3 & E4 & E8 & E9 & E10 & E18 & E19 & E21 & E32 & E33 & E34 & E35 & HinC & Hn8 & Hrole & Rlast &
      HMEMc & Hceil & H47 & Hal16 & Hh4096 & Hhc).
pose proof HIT as (HJ & HMEM & HKEPT & HPERM & Hin0 & Hlo & Hhi & Hh8 & LT & HTOK & Rnow & Hi & HNW & HR & HK).
pose proof (paj_run (fx := fq) B LAWS) as RUN. pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
set (E := l2_E regs T i) in *.
pose proof HS as HS0.
assert (HMEQ : forall x : word, memc x = memc x) by reflexivity.
unfold cfg_at. change (w64 (BASE + L2_PC)) with (Z_to_bv 64 (BASE + L2_PC)).
paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
l2_meq HS.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_geu_U, (U_atom E 33 (last_of T i) E33), (U_atom E 18 now E18) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_LIVE. { awr_ok_tac. }
  l2_meq HS.
  pose proof (l2_same_regs fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
  pmkst HS.
  eapply (l2_live k IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn i T bl0 Hk).
  + apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc Sc (ms_mem ms) _ (ms_regs ms) fq HIT HJ).
    * apply Permutation_refl.
    * intros a _. exact (HMEQ a).
    * exact HRK.
    * apply l2_freg_refl.
    * apply hs_csr_refl.
  + apply reac_hunt_step.hs_st1. lia.
- rewrite branch_geu_U, (U_atom E 33 (last_of T i) E33), (U_atom E 18 now E18) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt.
  paj_run_tok RUN HS HJ SHOK Bspan. { awr_ok_tac. }
  l2_meq HS.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ltu_U in Hc. rewrite U_lit in Hc by lia.
    rewrite (l2_U_sub E (SOff 18 0) (SOff 33 0) now (last_of T i) (U_atom E 18 now E18 ltac:(lia))
      (U_atom E 33 (last_of T i) E33 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_NEXT. { awr_ok_tac. }
    l2_meq HS.
    pose proof (l2_same_regs fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
    pmkst HS.
    eapply (l2_next k IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn i T bl0 Hk).
    * apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc Sc (ms_mem ms) _ (ms_regs ms) fq HIT HJ).
      -- apply Permutation_refl.
      -- intros a _. exact (HMEQ a).
      -- exact HRK.
      -- apply l2_freg_refl.
      -- apply hs_csr_refl.
    * unfold reac_hunt_step.hs_fb. rewrite (reac_hunt_step.hs_st2 T i now Hlt).
      replace (5000000000 <? now - last_of T i) with true by (symmetry; apply Z.ltb_lt; exact Hc). reflexivity.
  + rewrite branch_ltu_U in Hc. rewrite U_lit in Hc by lia.
    rewrite (l2_U_sub E (SOff 18 0) (SOff 33 0) now (last_of T i) (U_atom E 18 now E18 ltac:(lia))
      (U_atom E 33 (last_of T i) E33 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan L2_LIVE. { awr_ok_tac. }
    l2_meq HS.
    pose proof (l2_same_regs fq E _ _ _ _ _ HS0 HS ltac:(vm_compute; reflexivity)) as HRK.
    pmkst HS.
    eapply (l2_live k IH fq Q ly lyc S Sc W0 W mem0 memr (ms_mem ms) md0 _ (ms_regs ms) sp0 h now hb hn i T bl0 Hk).
    * apply (l2_it_gen fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 lyc Sc (ms_mem ms) _ (ms_regs ms) fq HIT HJ).
      -- apply Permutation_refl.
      -- intros a _. exact (HMEQ a).
      -- exact HRK.
      -- apply l2_freg_refl.
      -- apply hs_csr_refl.
    * rewrite (reac_hunt_step.hs_st2 T i now Hlt). apply Z.ltb_ge. exact Hc.
Qed.
Lemma l2_loop : forall k, l2_P k.
Proof.
induction k as [|k IH]; intros fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0 Hk HIT.
- pose proof HIT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi & _). lia.
- apply (l2_head k IH fq Q ly lyc S Sc W0 W mem0 memr memc md0 mdc regs sp0 h now hb hn i T bl0); [lia | exact HIT].
Qed.
Section w. Context {fx : YK11.FPState}.
Lemma hs_loop2 : forall (Q : world SEGS -> config -> Prop)
  (ly lyc : alayout) (S Sc : astate) (W0 W : world SEGS) (mem0 memc : word -> option byte)
  (md0 mdc : Model) (regsc : bvmap 5 word) (sp0 h now hb hn i : Z) (T' : list byte),
  ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyc Sc W memc mdc 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 96) + -1628) 8 D3837 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn -> h mod 8 = 0 ->
  length T' = 400%nat -> table_ok T' ->
  garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) T') ->
  0 <= now < 2 ^ 64 -> 0 <= i < n_of T' ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fb h T' now j = false) ->
  spZ regsc = sp0 - 112 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 8 = w64 (h + 440) -> getr regsc 9 = w64 (h + 48 * i) -> getr regsc 18 = w64 now ->
  getr regsc 19 = w64 (h + 384) -> getr regsc 20 = w64 (h + 48 * i + 40) -> getr regsc 21 = w64 i ->
  getr regsc 22 = w64 2 -> getr regsc 23 = w64 SHADOW_OFF -> getr regsc 24 = w64 (SHADOW_OFF + (h + 384) / 8) ->
  getr regsc 25 = w64 1 -> getr regsc 26 = w64 (SHADOW_OFF + (h + 48 * i + 40) / 8) ->
  getr regsc 27 = w64 5000000000 ->
  (forall (fq' : YK11.FPState) (lyd : alayout) (Sd : astate) (Wd : world SEGS)
          (memd : word -> option byte) (mdd : Model) (regsd : bvmap 5 word) (v : Z),
     freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
     ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd Wd memd mdd 0 ->
     v = (if box_present h T' now then 1 else 0) ->
     Wd = W /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) ->
        aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a) ->
     Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) ->
     getr regsd 2 = Z_to_bv 64 (sp0 - 112) -> getr regsd 3 = w64 (as_gp B) -> getr regsd 4 = w64 (as_tp B) ->
     getr regsd 8 = Z_to_bv 64 (h + 440) -> getr regsd 23 = Z_to_bv 64 SHADOW_OFF -> getr regsd 10 = Z_to_bv 64 v ->
     SRr SEGS Wd (cfg_at (fx := fq') SEGS (BASE + 0x7664) regsd memd mdd) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x78cc) regsc memc mdc) Q.
Proof.
intros Q ly lyc S Sc W0 W mem0 memc md0 mdc regsc sp0 h now hb hn i T' HJ HRO HRA HRT HD6 HD3 Hin Hlo Hhi Hh8 LT HTOK HG
  Rnow Hi HNW R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (WK : REAC_SENDER_KIND_STK = 4224) by reflexivity.
apply (l2_loop (Z.to_nat (n_of T' - i)) fx Q ly lyc S Sc W0 W mem0 memc memc md0 mdc regsc sp0 h now hb hn i T' (ablocks B lyc Sc)).
- lia.
- split; [exact HJ|].
  split; [split; [exact HRO|]; split; [exact HRA|]; split; [exact HRT|]; split; [exact HD6|]; split; [exact HD3 | exact HG]|].
  split; [intros a _; reflexivity|].
  split; [apply Permutation_refl|]. split; [exact Hin|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hh8|].
  split; [exact LT|]. split; [exact HTOK|]. split; [exact Rnow|]. split; [exact Hi|]. split; [exact HNW|].
  split.
  { unfold l2_regs_at. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
    split; [exact R9|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
    split; [exact R22|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26 | exact R27]. }
  intros fq' lyd Sd Wd memd mdd regsd v Hf Hc HJd Hv HWd HP Hkept Hsp HR3 HR4 HR8 HR23 HR10.
  apply (HK fq' lyd Sd Wd memd mdd regsd v Hf Hc HJd Hv).
  + split; [exact HWd|]. intros a Ha Hw.
    apply (l2_aview_kept (w_H W) memc memd (l2_win sp0) Hkept). rewrite Z.mod_small by lia.
    unfold l2_win. rewrite WK. rewrite WS in Hw. lia.
  + exact HP.
  + rewrite <- Hsp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
  + exact HR3.
  + exact HR4.
  + exact HR8.
  + exact HR23.
  + exact HR10.
Qed.
End w.
Lemma l1_vm : forall (m : word -> option byte) p (T : list byte) o (n : nat),
garr8 SEGS m p (map (fun b : byte => bv_unsigned b) T) -> 0 <= o -> o + Z.of_nat n <= Z.of_nat (length T) ->
val_mem SEGS m (p + o) n (u_at T o n).
Proof.
intros m p T o n HG Ho Hn k Hk.
assert (Hj : (Z.to_nat o + k < length (map (fun b : byte => bv_unsigned b) T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m p _ _ HG Hj) as Hb.
replace (p + Z.of_nat (Z.to_nat o + k)) with (p + o + Z.of_nat k) in Hb by lia.
rewrite Hb. f_equal. f_equal.
unfold u_at, sub, YO0f.le_byte.
assert (Hl : length (firstn n (skipn (Z.to_nat o) T)) = n) by (rewrite length_firstn, length_skipn; lia).
pose proof (disco_table.ble_range (firstn n (skipn (Z.to_nat o) T))) as Hr. rewrite Hl in Hr.
rewrite (Z.mod_small _ _ Hr).
rewrite l1_ble_byte by lia.
rewrite nth_firstn. replace (k <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite (map_nth (fun b : byte => bv_unsigned b)). reflexivity.
Qed.
Definition l1_sr : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 21 (SOff 22 20)) 23 HSBx)
24 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) HSBx))
27 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 40) (SLit 3)) HSBx).
Definition l1_RE : YP09.region := YP09.mkRegion (Some 22%nat) 0 48 0 0
[YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 20 (CVal 4 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition l1_RN : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition l1_facts : facts :=
mkFacts [ (19%nat, PTR 3); (22%nat, PTR 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition l1_ss (pc : Z) : sstate := mkSS pc l1_sr [l1_RE; l1_RN] None l1_facts.
Definition l1_SH : list shent := [mkSHE 22 0 48; mkSHE 19 0 8].
Definition l1_E (regs : bvmap 5 word) (T' : list byte) (i : Z) : env :=
Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (last_of T' i); Z_to_bv 64 (u_at T' (48 * i + 8) 4);
Z_to_bv 64 (ch_of T' i); Z_to_bv 64 (u_at T' 384 4)]).
Lemma l1_shd : forall E (m : nat) c a, ew E m = Z_to_bv 64 a -> ew E 32 = Z_to_bv 64 SB -> 0 <= a -> 0 <= c -> a + c < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) HSBx) = Z_to_bv 64 (SHADOW_OFF + (a + c) / 8).
Proof.
intros E m c a Hm H32 Ha Hc Hac. rewrite denot_lit_U. f_equal. unfold HSBx.
rewrite !U_SAlu, !U_SOff, U_SLit, Hm, H32. rewrite !unsigned_lit_small by (unfold SB; lia).
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (a + c)) by (unfold M64; lia). rewrite (zcanon_id ((a + c) / 8)).
2: { unfold M64. split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (a + c)); [apply Z.div_le_upper_bound; lia | lia]. }
rewrite Z.add_0_r, (zcanon_id SB) by (unfold M64, SB; lia). rewrite SB_SHADOW_OFF.
assert (0 <= (a + c) / 8 <= a + c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.
Definition l1_regs (regs : bvmap 5 word) (sp0 h now i : Z) : Prop :=
getr regs 2 = w64 (sp0 - 112) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (h + 440) /\ getr regs 9 = w64 h /\ getr regs 18 = w64 now /\
getr regs 19 = w64 (h + 384) /\ getr regs 20 = w64 (h + 412) /\ getr regs 21 = w64 (h + 48 * i + 20) /\
getr regs 22 = w64 (h + 48 * i) /\ getr regs 23 = w64 SHADOW_OFF /\
getr regs 24 = w64 (SHADOW_OFF + (h + 384) / 8) /\ getr regs 25 = w64 i /\
getr regs 26 = w64 5000000000 /\ getr regs 27 = w64 (SHADOW_OFF + (h + 40 + 48 * i) / 8).
Definition l1_fix (sp0 h hb hn now : Z) (T' U : list byte) (lyc : alayout) (Sc : astate) (W : world SEGS)
(memc : word -> option byte) : Prop :=
In (hb, hn) (ablocks B lyc Sc) /\ hb <= h /\ h + 480 <= hb + req_size hn /\ 0 < h /\ h mod 8 = 0 /\
length T' = 400%nat /\ table_ok T' /\ length U = 6%nat /\ 0 <= now < 2 ^ 64 /\
garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) T') /\
garr8 SEGS (mrestrict (w_H W) memc) (h + 412) (map (fun b : byte => bv_unsigned b) U) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 97) + -1832) 8 D6000 /\
val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 96) + -1628) 8 D3837 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc).
Definition l1_inv (sp0 h : Z) (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(lyd : alayout) (Sd : astate) (memd : word -> option byte) (mdd : Model) : Prop :=
ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd W memd mdd 0 /\
Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) ->
aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a).
Lemma l1_fr : forall (H : word -> bool) E (m m' : word -> option byte),
frame_of E [l1_RE; l1_RN] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H E m m' HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Hb). cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn in Hb; lia.
Qed.
Lemma l1_kept_garr8 : forall (W : world SEGS) memc memd p L lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a) ->
0 <= p -> p + Z.of_nat (length L) <= lo -> lo < 2 ^ 64 ->
garr8 SEGS (mrestrict (w_H W) memc) p L -> garr8 SEGS (mrestrict (w_H W) memd) p L.
Proof.
intros W memc memd p L lo hi HK Hp Hl Hlo HG. apply (garr8_aview_kept SEGS (w_H W) (w_H W) memc memd p L); [|exact HG].
intros a Ha. apply HK; lia.
Qed.
Lemma l1_ewl : forall regs T' i (n : nat), (n < 32)%nat -> ew (l1_E regs T' i) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs T' i n Hn. unfold l1_E. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [Ereg ew].
replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity.
Qed.
Lemma l1_envf : forall regs T' i sp0 h now, l1_regs regs sp0 h now i ->
ew (l1_E regs T' i) 2 = w64 (sp0 - 112) /\ ew (l1_E regs T' i) 3 = w64 (as_gp B) /\ ew (l1_E regs T' i) 4 = w64 (as_tp B) /\
ew (l1_E regs T' i) 8 = w64 (h + 440) /\ ew (l1_E regs T' i) 9 = w64 h /\ ew (l1_E regs T' i) 18 = w64 now /\
ew (l1_E regs T' i) 19 = w64 (h + 384) /\ ew (l1_E regs T' i) 20 = w64 (h + 412) /\
ew (l1_E regs T' i) 21 = w64 (h + 48 * i + 20) /\ ew (l1_E regs T' i) 22 = w64 (h + 48 * i) /\
ew (l1_E regs T' i) 23 = w64 SHADOW_OFF /\ ew (l1_E regs T' i) 24 = w64 (SHADOW_OFF + (h + 384) / 8) /\
ew (l1_E regs T' i) 25 = w64 i /\ ew (l1_E regs T' i) 26 = w64 5000000000 /\
ew (l1_E regs T' i) 27 = w64 (SHADOW_OFF + (h + 40 + 48 * i) / 8) /\
ew (l1_E regs T' i) 32 = Z_to_bv 64 SB /\ ew (l1_E regs T' i) 33 = Z_to_bv 64 (last_of T' i) /\
ew (l1_E regs T' i) 34 = Z_to_bv 64 (u_at T' (48 * i + 8) 4) /\ ew (l1_E regs T' i) 35 = Z_to_bv 64 (ch_of T' i) /\
ew (l1_E regs T' i) 36 = Z_to_bv 64 (u_at T' 384 4).
Proof.
intros regs T' i sp0 h now (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
repeat split; try (rewrite l1_ewl by lia; assumption);
unfold l1_E; rewrite Eimg_low by (unfold A_TEXT; lia); first [exact (ew_Ereg_extra regs _ 0) | exact (ew_Ereg_extra regs _ 1)
| exact (ew_Ereg_extra regs _ 2) | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)].
Qed.
Lemma l1_shv : forall x, 0 <= x < 2 ^ 47 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = Z_to_bv 64 (SHADOW_OFF + x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. rewrite (unsigned_lit_small SB) by (unfold SB; lia).
rewrite alu64_unsigned. rewrite !unsigned_lit_small by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (x / 8)) by lia.
rewrite SB_SHADOW_OFF. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_comm. apply Z.mod_small. unfold SHADOW_OFF. lia.
Qed.
Lemma l1_add : forall a b, 0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hab. apply alu_add_small; unfold M64; lia. Qed.
Lemma l1_sext : forall v, 0 <= v < 2 ^ 32 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 v)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros v Hv. rewrite (zext_low_sound true 32 v). unfold zext_low. apply Z_to_bv64_eq_mod.
unfold zcanon, M64. rewrite Zmod_mod. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (cbn; lia). reflexivity.
Qed.
Lemma l1_lts : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit.
assert (S1 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 (zcanon z) = z).
{ intros z Hz. unfold bv_swrap, zcanon, M64, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. destruct (Z.ltb_spec z 0).
- replace (z + 2 ^ 63) with ((z + 2 ^ 64 + 2 ^ 63) - 2 ^ 64) by lia. rewrite Z.mod_small; lia.
- rewrite Z.mod_small; lia. }
rewrite !S1 by lia. reflexivity.
Qed.
Lemma l1_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma l1_freg_refl : forall F, freg_kept F F.
Proof. intros F k _ _ _. reflexivity. Qed.
Lemma l1_freg_trans : forall F1 F2 F3, freg_kept F1 F2 -> freg_kept F2 F3 -> freg_kept F1 F3.
Proof. intros F1 F2 F3 A C k H1 H2 H3. rewrite (C k H1 H2 H3). apply A; assumption. Qed.
Lemma l1_awr : forall E STK sp0 FP bl0 blc ly own, awr_ok E [l1_RE; l1_RN] STK sp0 FP bl0 blc ly own.
Proof. intros E STK sp0 FP bl0 blc ly own a (r & Hr & Ha). destruct Hr as [<- | [<- | []]]; cbn in Ha; lia. Qed.
Lemma l1_uat : forall T o (n : nat), 0 <= u_at T o n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T o n. unfold u_at. pose proof (disco_table.ble_range (sub T o n)) as R. unfold sub in *.
rewrite length_firstn, length_skipn in R. split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 R)|].
apply Z.pow_le_mono_r; lia.
Qed.
Lemma l1_regs_pres : forall (R R' : bvmap 5 word) sp0 h now i, aregs_preserved R R' -> l1_regs R sp0 h now i -> l1_regs R' sp0 h now i.
Proof.
intros R R' sp0 h now i HP (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
assert (K : forall r v, acallee_saved r -> getr R (Z_to_bv 5 r) = v -> getr R' (Z_to_bv 5 r) = v) by (intros r v Hr Hv; rewrite (HP r Hr); exact Hv).
unfold l1_regs.
split; [apply (K 2); [unfold acallee_saved; lia | exact R2]|].
split; [apply (K 3); [unfold acallee_saved; lia | exact R3]|].
split; [apply (K 4); [unfold acallee_saved; lia | exact R4]|].
split; [apply (K 8); [unfold acallee_saved; lia | exact R8]|].
split; [apply (K 9); [unfold acallee_saved; lia | exact R9]|].
split; [apply (K 18); [unfold acallee_saved; lia | exact R18]|].
split; [apply (K 19); [unfold acallee_saved; lia | exact R19]|].
split; [apply (K 20); [unfold acallee_saved; lia | exact R20]|].
split; [apply (K 21); [unfold acallee_saved; lia | exact R21]|].
split; [apply (K 22); [unfold acallee_saved; lia | exact R22]|].
split; [apply (K 23); [unfold acallee_saved; lia | exact R23]|].
split; [apply (K 24); [unfold acallee_saved; lia | exact R24]|].
split; [apply (K 25); [unfold acallee_saved; lia | exact R25]|].
split; [apply (K 26); [unfold acallee_saved; lia | exact R26]|].
apply (K 27); [unfold acallee_saved; lia | exact R27].
Qed.
Lemma l1_vm_swrap : forall m a v, val_mem SEGS m a 4 v -> 0 <= v < 2 ^ 32 -> val_mem SEGS m a 4 (bv_swrap 32 v).
Proof.
intros m a v H Hv k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte. f_equal. f_equal.
change (8 * Z.of_nat 4) with 32. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma l1_mac : forall (H : word -> bool) (mem : word -> option byte) h (T' U : list byte) i,
garr8 SEGS (mrestrict H mem) h (map (fun b : byte => bv_unsigned b) T') ->
garr8 SEGS (mrestrict H mem) (h + 412) (map (fun b : byte => bv_unsigned b) U) ->
length T' = 400%nat -> length U = 6%nat -> 0 <= i <= 7 ->
((forall j, 0 <= j < 6 -> aview SEGS H mem (h + 48 * i + j) = aview SEGS H mem (h + 412 + j)) <-> mac_of T' i = U).
Proof.
intros H mem h T' U i GT GU LT LU Hi.
assert (AT : forall j, 0 <= j < 6 -> aview SEGS H mem (h + 48 * i + j) = Some (bv_unsigned (nth (Z.to_nat (48 * i + j)) T' (Z_to_bv 8 0)))).
{ intros j Hj. unfold aview. replace (h + 48 * i + j) with (h + Z.of_nat (Z.to_nat (48 * i + j))) by lia.
rewrite (garr8_mbyte SEGS _ _ _ _ GT) by (rewrite length_map; lia). cbn [option_map].
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite (map_nth (fun b : byte => bv_unsigned b)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (AU : forall j, 0 <= j < 6 -> aview SEGS H mem (h + 412 + j) = Some (bv_unsigned (nth (Z.to_nat j) U (Z_to_bv 8 0)))).
{ intros j Hj. unfold aview. replace (h + 412 + j) with (h + 412 + Z.of_nat (Z.to_nat j)) by lia.
rewrite (garr8_mbyte SEGS _ _ _ _ GU) by (rewrite length_map; lia). cbn [option_map].
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite (map_nth (fun b : byte => bv_unsigned b)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (MU : forall j, (j < 6)%nat -> nth j (mac_of T' i) (Z_to_bv 8 0) = nth (Z.to_nat (48 * i) + j) T' (Z_to_bv 8 0)).
{ intros j Hj. unfold mac_of, sub. rewrite nth_firstn. replace (j <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. reflexivity. }
assert (LM : length (mac_of T' i) = 6%nat) by (unfold mac_of, sub; rewrite length_firstn, length_skipn; lia).
split.
- intros Heq. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite LM, LU; reflexivity|].
intros j Hj. rewrite LM in Hj. rewrite MU by lia.
specialize (Heq (Z.of_nat j) ltac:(lia)). rewrite AT, AU in Heq by lia. injection Heq as Heq.
replace (Z.to_nat (48 * i + Z.of_nat j)) with (Z.to_nat (48 * i) + j)%nat in Heq by lia.
rewrite Nat2Z.id in Heq. apply bv_eq. exact Heq.
- intros Heq j Hj. rewrite AT, AU by lia. f_equal. f_equal. rewrite <- Heq. rewrite (MU (Z.to_nat j)) by lia.
f_equal. lia.
Qed.
Lemma l1_aview_mod : forall (H : word -> bool) (m : word -> option byte) x, aview SEGS H m x = aview SEGS H m (x mod 2 ^ 64).
Proof.
intros H m x. unfold aview, mbyte. replace (Z_to_bv 64 (x mod 2 ^ 64)) with (Z_to_bv 64 x); [reflexivity|].
apply Z_to_bv64_eq_mod. rewrite Zmod_mod. reflexivity.
Qed.
Lemma l1_ro_low : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
- apply pa_segs_low. apply pa_relro_img. exact Hr.
Qed.
Lemma l1_hi_near : forall kk (rd : bv 5) j, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
exists s, - 2 ^ 31 <= s < 2 ^ 31 /\ VAL (A_HI j) = (BASE + kk + s) mod 2 ^ 64 /\ 0 <= BASE + kk < kLowMemEnd.
Proof.
intros kk rd j Hk40 Hk. pose proof pa_B_ok as HB.
rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert kk _ Hk) as [Hc [Hk0 Hk4]].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + kk)) as [wz|] eqn:Hf; [|discriminate Hc].
assert (Himg : 0 <= BASE + kk < kLowMemEnd).
{ pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (HI : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ HI) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia. }
destruct (decode_any (Z_to_bv 32 wz)) as [[ins isz]|]; [|discriminate Hc].
apply andb_prop in Hc as [_ Hc]. destruct ins; try (cbn in Hc; discriminate Hc).
apply andb_prop in Hc as [_ Hc]. apply Z.eqb_eq in Hc. unfold auipc_val, zcanon, M64 in Hc.
exists (bv_signed (bv_concat 32 imm (Z_to_bv 12 0))).
pose proof (bv_signed_in_range 32 (bv_concat 32 imm (Z_to_bv 12 0)) ltac:(discriminate)) as Hr.
change (bv_half_modulus 32) with (2 ^ 31) in Hr.
split; [lia|]. split; [rewrite <- Hc; reflexivity | exact Himg].
Qed.
Lemma l1_hi_win : forall kk (rd : bv 5) j c x lo hi, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
-4096 <= c <= 4096 -> 0 <= x < 8 -> alloc_ceiling <= lo -> hi <= 2 ^ 47 ->
~ (lo <= (VAL (A_HI j) + c + x) mod 2 ^ 64 < hi).
Proof.
intros kk rd j c x lo hi Hk40 Hk Hc Hx Hlo Hhi.
destruct (l1_hi_near kk rd j Hk40 Hk) as (s & Hs & Hv & Hb).
pose proof (asan_consts) as (C1 & _ & _ & _ & C5).
rewrite Hv. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
revert Hs Hb Hc Hx Hlo Hhi C1 C5. clear. intros. Z.div_mod_to_equations. lia.
Qed.
Lemma l1_fix_mem : forall sp0 h hb hn now T' U lyc Sc (W : world SEGS) memc memd,
l1_fix sp0 h hb hn now T' U lyc Sc W memc -> hb + req_size hn <= sp0 - REAC_HUNT_STEP_STK ->
alloc_ceiling <= sp0 - REAC_HUNT_STEP_STK -> sp0 <= 2 ^ 47 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) -> aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a) ->
garr8 SEGS (mrestrict (w_H W) memd) h (map (fun b : byte => bv_unsigned b) T') /\
garr8 SEGS (mrestrict (w_H W) memd) (h + 412) (map (fun b : byte => bv_unsigned b) U) /\
range_addressable (aview SEGS (w_H W) memd) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
garr8 SEGS (mrestrict (w_H W) memd) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
val_mem SEGS (mrestrict (w_H W) memd) (VAL (A_HI 97) + -1832) 8 D6000 /\
val_mem SEGS (mrestrict (w_H W) memd) (VAL (A_HI 96) + -1628) 8 D3837 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memd).
Proof.
intros sp0 h hb hn now T' U lyc Sc W memc memd HF Hbw Hcw Hsw HK.
pose proof HF as (Hin & Hlo & Hhi & Hh0 & Hh8 & LT & TOK & LU & Rnow & GT & GU & RR & GR & D60 & D38 & HROD).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 65 ltac:(unfold disco_nobj; lia)) as HO.
assert (HIT : IMG_TOP = 6283264) by reflexivity. assert (HIL : IMG_LO = 65536) by reflexivity.
assert (LR : length RATES = 12%nat) by reflexivity.
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
split; [apply (l1_kept_garr8 W memc memd h _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LT; lia | lia | exact GT]|].
split; [apply (l1_kept_garr8 W memc memd (h + 412) _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LU; lia | lia | exact GU]|].
split.
{ intros x Hx. destruct (RR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite HK; [exact Hs| |].
- assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). unfold SHADOW_OFF in *. lia.
- assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). unfold SHADOW_OFF in *. lia. }
split; [apply (l1_kept_garr8 W memc memd (VAL (A_OBJ 65)) _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LR; lia | lia | exact GR]|].
split.
- apply (val_mem_kept SEGS (w_H W) (w_H W) memc memd _ 8 D6000); [|exact D60]. intros k Hk.
rewrite l1_aview_mod, (l1_aview_mod _ memc). apply HK; [apply Z.mod_pos_bound; lia|].
apply (l1_hi_win 31476 11%bv 97 (-1832) k); [lia | vm_compute; reflexivity | lia | lia | lia | lia].
- split.
+ apply (val_mem_kept SEGS (w_H W) (w_H W) memc memd _ 8 D3837); [|exact D38]. intros k Hk.
rewrite l1_aview_mod, (l1_aview_mod _ memc). apply HK; [apply Z.mod_pos_bound; lia|].
apply (l1_hi_win 31472 10%bv 96 (-1628) k); [lia | vm_compute; reflexivity | lia | lia | lia | lia].
+ intros a Hro Ho He. pose proof (l1_ro_low a Hro) as Ha. rewrite HK; [exact (HROD a Hro Ho He) | lia | unfold kLowMemEnd in *; lia].
Qed.
Lemma l1_rawk : forall (H : word -> bool) (m m' : word -> option byte) lo hi,
(forall a : word, ~ (lo <= bv_unsigned a < hi) -> m' a = m a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' lo hi HK a Ha Hw. unfold aview, mbyte, mrestrict. rewrite (HK (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hw.
Qed.
Lemma l1_subm : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (mul_div M_MUL (Z_to_bv 64 b) (Z_to_bv 64 (-1))) = Z_to_bv 64 (a - b).
Proof.
intros a b Hb Ha. apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned, !Z_to_bv_unsigned.
cbn [zalu_raw zmd_raw]. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
f_equal. lia.
Qed.
Lemma l1_shok : forall (W : world SEGS) ly S mem md E (h hb hn i : Z),
AR SEGS B ly S W mem md -> In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn -> 0 <= i <= 7 ->
ew E 22 = w64 (h + 48 * i) -> ew E 19 = w64 (h + 384) -> ew E 32 = Z_to_bv 64 SB ->
sh_ok SEGS HSBx l1_SH E (mrestrict (w_H W) mem).
Proof.
intros W ly S mem md E h hb hn i HAR Hin Hlo Hhi Hi E22 E19 E32.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
assert (UBx : U E HSBx = SHADOW_OFF).
{ unfold U, HSBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). exact SB_SHADOW_OFF. }
assert (U22 : U E (SOff 22 0) = h + 48 * i).
{ unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
assert (U19 : U E (SOff 19 0) = h + 384).
{ unfold U. cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
unfold sh_ok, l1_SH. constructor; [|constructor; [|constructor]].
+ eapply (shent_ok_of_range SEGS (w_H W) mem E HSBx 22 h 480 (h + 48 * i) 0 48).
* eapply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
* exact UBx. * exact U22. * lia. * lia.
* intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3 Hi. clear.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
+ eapply (shent_ok_of_range SEGS (w_H W) mem E HSBx 19 h 480 (h + 384) 0 8).
* eapply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
* exact UBx. * exact U19. * lia. * lia.
* intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma l1_pav : forall (H : word -> bool) mem a, apresent H mem a -> aview SEGS H mem a <> None.
Proof.
intros H mem a (Ha & b & Hb). unfold aview, mbyte, mrestrict. rewrite Ha, Hb. discriminate.
Qed.
Ltac l1_kc W memc sp0 :=
let Kx := fresh "Kx" in let KCx := fresh "KCx" in
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => pose proof (l1_fr _ _ _ _ HFr) as Kx; clear HFr end;
lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF end;
lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end;
repeat match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress rewrite wvb_collapse in HJ end;
lazymatch type of Kx with forall a, aview _ _ ?m' a = aview _ _ ?m a =>
lazymatch goal with KC : forall a, _ -> _ -> aview _ _ m a = _ |- _ =>
assert (KCx : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a)
 by (intros a Ha Hw; rewrite (Kx a); exact (KC a Ha Hw));
clear KC Kx; rename KCx into KC end end.
Ltac l1_regs_tac h i :=
lazymatch goal with
| Q2 : getr _ 2 = _, Q3 : getr _ 3 = _, Q4 : getr _ 4 = _, Q8 : getr _ 8 = _, Q9 : getr _ 9 = _,
  Q18 : getr _ 18 = _, Q19 : getr _ 19 = _, Q20 : getr _ 20 = _, Q21 : getr _ 21 = _, Q22 : getr _ 22 = _,
  Q23 : getr _ 23 = _, Q24 : getr _ 24 = _, Q25 : getr _ 25 = _, Q26 : getr _ 26 = _, Q27 : getr _ 27 = _,
  E2 : ew _ 2 = _, E3 : ew _ 3 = _, E4 : ew _ 4 = _, E8 : ew _ 8 = _, E9 : ew _ 9 = _, E18 : ew _ 18 = _,
  E19 : ew _ 19 = _, E20 : ew _ 20 = _, E22 : ew _ 22 = _, E25 : ew _ 25 = _, E26 : ew _ 26 = _, E32 : ew _ 32 = _ |- _ =>
unfold l1_regs;
split; [rewrite Q2, E2; reflexivity|];
split; [rewrite Q3, E3; reflexivity|];
split; [rewrite Q4, E4; reflexivity|];
split; [rewrite Q8, E8; reflexivity|];
split; [rewrite Q9, E9; reflexivity|];
split; [rewrite Q18, E18; reflexivity|];
split; [rewrite Q19, E19; reflexivity|];
split; [rewrite Q20, E20; reflexivity|];
split; [rewrite Q21, E22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
split; [rewrite Q22, E22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|];
split; [rewrite Q23, E32; unfold w64; rewrite SB_SHADOW_OFF; reflexivity|];
split; [rewrite Q24, E19, E32; unfold w64; rewrite l1_shv by lia; reflexivity|];
split; [rewrite Q25, E25; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|];
split; [rewrite Q26, E26; reflexivity|];
rewrite Q27, E22, E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite l1_shv by lia;
rewrite l1_add by (pose proof (Z.div_le_upper_bound (h + 48 * i + 40) 8 (h + 48 * i + 40)); pose proof (Z.div_pos (h + 48 * i + 40) 8); unfold SHADOW_OFF; lia);
f_equal; replace (h + 40 + 48 * (i + 1)) with (h + 48 * i + 40 + 6 * 8) by lia; rewrite Z.div_add by lia; lia
end.
Ltac l1_regs_same h i :=
lazymatch goal with
| Q2 : getr _ 2 = _, Q3 : getr _ 3 = _, Q4 : getr _ 4 = _, Q8 : getr _ 8 = _, Q9 : getr _ 9 = _,
  Q18 : getr _ 18 = _, Q19 : getr _ 19 = _, Q20 : getr _ 20 = _, Q21 : getr _ 21 = _, Q22 : getr _ 22 = _,
  Q23 : getr _ 23 = _, Q24 : getr _ 24 = _, Q25 : getr _ 25 = _, Q26 : getr _ 26 = _, Q27 : getr _ 27 = _,
  E2 : ew _ 2 = _, E3 : ew _ 3 = _, E4 : ew _ 4 = _, E8 : ew _ 8 = _, E9 : ew _ 9 = _, E18 : ew _ 18 = _,
  E19 : ew _ 19 = _, E20 : ew _ 20 = _, E22 : ew _ 22 = _, E25 : ew _ 25 = _, E26 : ew _ 26 = _, E32 : ew _ 32 = _ |- _ =>
unfold l1_regs;
split; [rewrite Q2, E2; reflexivity|];
split; [rewrite Q3, E3; reflexivity|];
split; [rewrite Q4, E4; reflexivity|];
split; [rewrite Q8, E8; reflexivity|];
split; [rewrite Q9, E9; reflexivity|];
split; [rewrite Q18, E18; reflexivity|];
split; [rewrite Q19, E19; reflexivity|];
split; [rewrite Q20, E20; reflexivity|];
split; [rewrite Q21, E22; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|];
split; [rewrite Q22, E22; reflexivity|];
split; [rewrite Q23, E32; unfold w64; rewrite SB_SHADOW_OFF; reflexivity|];
split; [rewrite Q24, E19, E32; unfold w64; rewrite l1_shv by lia; reflexivity|];
split; [rewrite Q25, E25; reflexivity|];
split; [rewrite Q26, E26; reflexivity|];
rewrite Q27, E22, E32; unfold w64; rewrite unsigned_lit_small by lia; rewrite l1_shv by lia;
replace (h + 40 + 48 * i) with (h + 48 * i + 40) by lia; reflexivity
end.
Ltac l1_prregs HS :=
let Q2 := fresh "Q2" in prreg HS (2%bv : bv 5) Q2;
let Q3 := fresh "Q3" in prreg HS (3%bv : bv 5) Q3;
let Q4 := fresh "Q4" in prreg HS (4%bv : bv 5) Q4;
let Q8 := fresh "Q8" in prreg HS (8%bv : bv 5) Q8;
let Q9 := fresh "Q9" in prreg HS (9%bv : bv 5) Q9;
let Q18 := fresh "Q18" in prreg HS (18%bv : bv 5) Q18;
let Q19 := fresh "Q19" in prreg HS (19%bv : bv 5) Q19;
let Q20 := fresh "Q20" in prreg HS (20%bv : bv 5) Q20;
let Q21 := fresh "Q21" in prreg HS (21%bv : bv 5) Q21;
let Q22 := fresh "Q22" in prreg HS (22%bv : bv 5) Q22;
let Q23 := fresh "Q23" in prreg HS (23%bv : bv 5) Q23;
let Q24 := fresh "Q24" in prreg HS (24%bv : bv 5) Q24;
let Q25 := fresh "Q25" in prreg HS (25%bv : bv 5) Q25;
let Q26 := fresh "Q26" in prreg HS (26%bv : bv 5) Q26;
let Q27 := fresh "Q27" in prreg HS (27%bv : bv 5) Q27.
Section w1. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Lemma l1_build : forall (W : world SEGS) ly S mem md (regs : bvmap 5 word) (h hb hn i : Z) (T' : list byte) (pc : Z),
AR SEGS B ly S W mem md -> In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn -> h mod 8 = 0 ->
length T' = 400%nat -> 0 <= i <= 7 ->
garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) T') ->
getr regs 19 = w64 (h + 384) -> getr regs 21 = w64 (h + 48 * i + 20) -> getr regs 22 = w64 (h + 48 * i) ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 24 = w64 (SHADOW_OFF + (h + 384) / 8) ->
getr regs 27 = w64 (SHADOW_OFF + (h + 40 + 48 * i) / 8) ->
st_ok_pi SEGS VAL (l1_E regs T' i) (l1_ss pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
sh_ok SEGS HSBx l1_SH (l1_E regs T' i) (mrestrict (w_H W) mem).
Proof.
intros W ly S mem md regs h hb hn i T' pc HAR Hin Hlo Hhi Hh8 LT Hi HG R19 R21 R22 R23 R24 R27.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
set (E := l1_E regs T' i).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (last_of T' i); Z_to_bv 64 (u_at T' (48 * i + 8) 4);
Z_to_bv 64 (ch_of T' i); Z_to_bv 64 (u_at T' 384 4)]) n) by (intros n Hn; subst E; unfold l1_E; apply Eimg_low; exact Hn).
assert (E19 : ew E 19 = Z_to_bv 64 (h + 384)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 (h + 48 * i)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (last_of T' i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (u_at T' (48 * i + 8) 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (ch_of T' i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (u_at T' 384 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (UBx : U E HSBx = SHADOW_OFF).
{ unfold U, HSBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). exact SB_SHADOW_OFF. }
assert (U22 : U E (SOff 22 0) = h + 48 * i).
{ unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
assert (U19 : U E (SOff 19 0) = h + 384).
{ unfold U. cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
assert (VM : forall o n, 0 <= o -> o + Z.of_nat n <= 400 -> val_mem SEGS (mrestrict (w_H W) mem) (h + o) n (u_at T' o n)).
{ intros o n Ho Hn. apply l1_vm; [exact HG | lia | rewrite LT; lia]. }
assert (UR : forall o n, 0 <= u_at T' o n < 2 ^ (8 * Z.of_nat n)).
{ intros o n. unfold u_at. pose proof (disco_table.ble_range (sub T' o n)) as R. unfold sub in *.
rewrite length_firstn, length_skipn in R. split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 R)|].
apply Z.pow_le_mono_r; lia. }
rewrite restrict_mkst_fx. split.
- unfold l1_ss. apply pa_entry_st_ok_full.
+ unfold l1_sr.
apply regs_ok_rereg; [|reflexivity|].
2: { rewrite R27. unfold w64. symmetry. replace (h + 40 + 48 * i) with (h + 48 * i + 40) by lia. apply l1_shd; [exact E22 | exact E32 | lia | lia | lia]. }
apply regs_ok_rereg; [|reflexivity|].
2: { rewrite R24. unfold w64. symmetry. replace (h + 384) with (h + 384 + 0) by lia. apply l1_shd; [exact E19 | exact E32 | lia | lia | lia]. }
apply regs_ok_rereg; [|reflexivity|].
2: { rewrite R23. unfold HSBx. rewrite denot_lit_U. unfold w64. f_equal. }
apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg|reflexivity|].
rewrite R21, denot_lit_U. unfold w64. f_equal. rewrite U_SOff, E22, unsigned_lit_small by lia. symmetry. apply zcanon_id. unfold M64. lia.
+ vm_compute. reflexivity.
+ unfold l1_RE, l1_RN. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
* rewrite E22, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_ok_val SEGS E _ (h + 48 * i) 8 4 (SOff 34 0) (u_at T' (48 * i + 8) 4)).
++ cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
++ exact (UR _ 4%nat).
++ lia.
++ replace (h + 48 * i + 8) with (h + (48 * i + 8)) by lia. apply VM; lia.
-- apply (chunk_ok_val SEGS E _ (h + 48 * i) 20 4 (SOff 35 0) (ch_of T' i)).
++ cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
++ exact (UR _ 4%nat).
++ lia.
++ replace (h + 48 * i + 20) with (h + (48 * i + 20)) by lia. apply VM; lia.
-- apply (chunk_ok_val SEGS E _ (h + 48 * i) 40 8 (SOff 33 0) (last_of T' i)).
++ cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
++ exact (UR _ 8%nat).
++ lia.
++ replace (h + 48 * i + 40) with (h + (48 * i + 40)) by lia. apply VM; lia.
* rewrite E19, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
apply (chunk_ok_val SEGS E _ (h + 384) 0 4 (SOff 36 0) (u_at T' 384 4)).
++ cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
++ exact (UR _ 4%nat).
++ lia.
++ rewrite Z.add_0_r. apply VM; lia.
+ apply pairwise_disjoint_of_extents. unfold l1_RE, l1_RN, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E22, E19, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. lia.
+ split; [|split; [exact I | exact I]].
cbn [l1_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite E19, E22, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert ((h + 384) mod 8 = 0) by (rewrite Z.add_mod, Hh8 by lia; reflexivity).
assert ((h + 48 * i) mod 8 = 0) by (replace (h + 48 * i) with (h + (6 * i) * 8) by lia; rewrite Z_mod_plus_full; exact Hh8).
revert Hb4096 Hbceil C1 Hlo Hhi Hi Hrq0 Hrq1. clear - H H0. intros. repeat split; try lia.
- unfold sh_ok, l1_SH. constructor; [|constructor; [|constructor]].
+ eapply (shent_ok_of_range SEGS (w_H W) mem E HSBx 22 h 480 (h + 48 * i) 0 48).
* eapply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
* exact UBx. * exact U22. * lia. * lia.
* intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3 Hi. clear.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
+ eapply (shent_ok_of_range SEGS (w_H W) mem E HSBx 19 h 480 (h + 384) 0 8).
* eapply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
* exact UBx. * exact U19. * lia. * lia.
* intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma l1_next : forall Q (ly : alayout) S W0 mem0 md0 lyc Sc (W : world SEGS) memc
(sp0 h hb hn now i : Z) (T' U : list byte) lyd Sd memd mdd (regs : bvmap 5 word),
l1_fix sp0 h hb hn now T' U lyc Sc W memc ->
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lyd Sd memd mdd ->
l1_regs regs sp0 h now i -> 0 <= i < n_of T' ->
(i + 1 < n_of T' -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now (i + 1) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x7760) regse meme mde) Q) ->
(n_of T' <= i + 1 -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now (i + 1) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x782c) regse meme mde) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x77d8) regs memd mdd) Q.
Proof.
intros Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs HF HI HR Hi LOOPK EXITK.
pose proof HF as (Hin & Hlo & Hhi & Hh0 & Hh8 & LT & TOK & LU & Rnow & GT & GU & RR & GR & D60 & D38 & HROD).
pose proof HI as (HJ & HP & HK).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (Hind : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hind) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
assert (GTd : garr8 SEGS (mrestrict (w_H W) memd) h (map (fun b : byte => bv_unsigned b) T')).
{ apply (l1_kept_garr8 W memc memd h _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LT; lia | lia | exact GT]. }
destruct (l1_build W lyd Sd memd mdd regs h hb hn i T' 0x77d8 HAR Hind Hlo Hhi Hh8 LT ltac:(lia) GTd R19 R21 R22 R23 R24 R27) as [HS SHOK].
destruct (l1_envf regs T' i sp0 h now HR) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E32 & E33 & E34 & E35 & E36).
assert (HEI : img_env VAL A_LIM (l1_E regs T' i)) by (unfold l1_E; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x77d8)) with (Z_to_bv 64 (BASE + 0x77d8)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K1. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
assert (UN : 0 <= u_at T' 384 4 < 2 ^ 32).
by exact (l1_uat T' 384 4).
assert (NE : n_of T' = bv_swrap 32 (u_at T' 384 4)) by reflexivity.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
- cbn [branch_taken sv_denot] in Hc. rewrite E25, E36 in Hc. unfold w64 in Hc.
rewrite !unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite l1_sext, <- NE in Hc by lia.
rewrite l1_lts in Hc by lia. apply Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7760.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K2. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS.
apply (LOOPK Hc lyd Sd (ms_mem ms0) _ (ms_regs ms0)).
+ split; [exact HJ|]. split; [exact HP|]. intros a Ha Hw. rewrite (K2 a), (K1 a). exact (HK a Ha Hw).
+ l1_regs_tac h i.
- cbn [branch_taken sv_denot] in Hc. rewrite E25, E36 in Hc. unfold w64 in Hc.
rewrite !unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite l1_sext, <- NE in Hc by lia.
rewrite l1_lts in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x782c.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K2. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS.
apply (EXITK Hc lyd Sd (ms_mem ms0) _ (ms_regs ms0)).
+ split; [exact HJ|]. split; [exact HP|]. intros a Ha Hw. rewrite (K2 a), (K1 a). exact (HK a Ha Hw).
+ l1_regs_tac h i.
Qed.
Lemma l1_aftersk : forall Q (ly : alayout) S W0 mem0 md0 lyc Sc (W : world SEGS) memc
(sp0 h hb hn now i : Z) (T' U : list byte) lyd Sd memd mdd (regs : bvmap 5 word) (kind : Z),
l1_fix sp0 h hb hn now T' U lyc Sc W memc ->
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lyd Sd memd mdd ->
l1_regs regs sp0 h now i -> 0 <= i < n_of T' -> getr regs 10 = w64 kind -> 0 <= kind <= 4 ->
(kind <> 3 -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at SEGS (BASE + 0x77d8) regse meme mde) Q) ->
(kind = 3 -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at SEGS (BASE + 0x795c) regse meme mde) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x77d0) regs memd mdd) Q.
Proof.
intros Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs kind HF HI HR Hi R10 Hk NEXTK HITK.
pose proof HF as (Hin & Hlo & Hhi & Hh0 & Hh8 & LT & TOK & LU & Rnow & GT & GU & RR & GR & D60 & D38 & HROD).
pose proof HI as (HJ & HP & HK).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (Hind : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hind) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
assert (GTd : garr8 SEGS (mrestrict (w_H W) memd) h (map (fun b : byte => bv_unsigned b) T')).
{ apply (l1_kept_garr8 W memc memd h _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LT; lia | lia | exact GT]. }
destruct (l1_envf regs T' i sp0 h now HR) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E32 & E33 & E34 & E35 & E36).
assert (HEI : img_env VAL A_LIM (l1_E regs T' i)) by (unfold l1_E; apply Eimg_env).
destruct (l1_build W lyd Sd memd mdd regs h hb hn i T' 0x77d0 HAR Hind Hlo Hhi Hh8 LT ltac:(lia) GTd R19 R21 R22 R23 R24 R27) as [HS SHOK].
assert (E10 : ew (l1_E regs T' i) 10 = w64 kind) by (rewrite l1_ewl by lia; exact R10).
unfold cfg_at. change (w64 (BASE + 0x77d0)) with (Z_to_bv 64 (BASE + 0x77d0)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K1. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
- cbn [branch_taken sv_denot] in Hc. rewrite E10 in Hc. unfold w64 in Hc.
rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite reac_hunt_step.hs_eqbk in Hc by lia. apply Z.eqb_eq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x795c.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K2. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
l1_prregs HS.
pmkst HS.
apply (HITK Hc lyd Sd (ms_mem ms0) _ (ms_regs ms0)).
+ split; [exact HJ|]. split; [exact HP|]. intros a Ha Hw. rewrite (K2 a), (K1 a). exact (HK a Ha Hw).
+ l1_regs_same h i.
- cbn [branch_taken sv_denot] in Hc. rewrite E10 in Hc. unfold w64 in Hc.
rewrite unsigned_lit_small, Z.add_0_r in Hc by lia. rewrite reac_hunt_step.hs_eqbk in Hc by lia. apply Z.eqb_neq in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
pose proof (l1_fr _ _ _ _ HFr) as K2. repeat rewrite wvb_collapse in HJ. clear HF HFr HG.
l1_prregs HS.
pmkst HS.
apply (NEXTK Hc lyd Sd (ms_mem ms0) _ (ms_regs ms0)).
+ split; [exact HJ|]. split; [exact HP|]. intros a Ha Hw. rewrite (K2 a), (K1 a). exact (HK a Ha Hw).
+ l1_regs_same h i.
Qed.
End w1.
Section w2. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Lemma l1_live : forall Q (ly : alayout) S W0 mem0 md0 lyc Sc (W : world SEGS) memc
(sp0 h hb hn now i : Z) (T' U : list byte) lyd Sd memd mdd (regs : bvmap 5 word),
l1_fix sp0 h hb hn now T' U lyc Sc W memc ->
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lyd Sd memd mdd ->
l1_regs regs sp0 h now i -> 0 <= i < n_of T' -> disco_stale T' i now = false ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
reac_hunt_step.hs_fd h T' U now i = false -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x77d8) regse meme mde) Q) ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
reac_hunt_step.hs_fd h T' U now i = true -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x795c) regse meme mde) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x7778) regs memd mdd) Q.
Proof.
intros Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs HF HI HR Hi HST NEXTK HITK.
pose proof HF as (Hin & Hlo & Hhi & Hh0 & Hh8 & LT & TOK & LU & Rnow & GT & GU & RR & GR & D60 & D38 & HROD).
pose proof HI as (HJ & HP & HK).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (Hind : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hind) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
assert (GTd : garr8 SEGS (mrestrict (w_H W) memd) h (map (fun b : byte => bv_unsigned b) T')).
{ apply (l1_kept_garr8 W memc memd h _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LT; lia | lia | exact GT]. }
destruct (l1_envf regs T' i sp0 h now HR) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E32 & E33 & E34 & E35 & E36).
assert (HEI : img_env VAL A_LIM (l1_E regs T' i)) by (unfold l1_E; apply Eimg_env).
assert (ES : ESTACK = 4096) by reflexivity.
assert (Hbw : hb + req_size hn <= sp0 - REAC_HUNT_STEP_STK) by lia.
assert (Hcw : alloc_ceiling <= sp0 - REAC_HUNT_STEP_STK) by lia.
rename HK into KC.
destruct (l1_build W lyd Sd memd mdd regs h hb hn i T' 0x7778 HAR Hind Hlo Hhi Hh8 LT ltac:(lia) GTd R19 R21 R22 R23 R24 R27) as [HS SHOK].
unfold cfg_at. change (w64 (BASE + 0x7778)) with (Z_to_bv 64 (BASE + 0x7778)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply l1_awr. }
l1_kc W memc sp0.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
pose proof (proj1 HJ) as HAR1.
destruct (l1_fix_mem sp0 h hb hn now T' U lyc Sc W memc _ HF Hbw Hcw ltac:(lia) KC) as (GT1 & GU1 & RR1 & GR1 & D601 & D381 & ROD1).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR1 Hind) as (_ & _ & _ & _ & Hbpres1 & _).
pmkst HS.
eapply SRr_bind.
{ apply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (ABCMP fx) W (ms_regs ms) (ms_mem ms) REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd _ 0
(h + 48 * i) (h + 412) 6 (-112) (Z_to_bv 64 (BASE + 30600))).
- exact HJ.
- rewrite P10, E22. reflexivity.
- rewrite P11, E20. reflexivity.
- exact P12.
- lia. - lia. - lia. - lia. - lia.
- unfold spZ. rewrite P2, E2. unfold w64. rewrite unsigned_lit_small by lia. lia.
- reflexivity.
- lia.
- rewrite ES, WS. lia.
- rewrite P3, E3. reflexivity.
- rewrite P4, E4. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply l1_pav; apply (proj1 (Hbpres1 a ltac:(lia)))|].
unfold spZ. rewrite P2, E2. unfold w64. rewrite unsigned_lit_small by lia. rewrite ES. lia.
- intros a Ha. split; [apply l1_pav; apply (proj1 (Hbpres1 a ltac:(lia)))|].
unfold spZ. rewrite P2, E2. unfold w64. rewrite unsigned_lit_small by lia. rewrite ES. lia.
- intros a Ha. rewrite ES. lia.
- intros a Ha. rewrite ES. lia.
- eapply (amem_range_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 48 * i) 6 HAR1 Hind); lia.
- eapply (amem_range_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 412) 6 HAR1 Hind); lia.
- eapply (range_addressable_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 48 * i) 6 HAR1 Hind); lia.
- intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 48 * i) 6 HAR1 Hind); lia.
- eapply (range_addressable_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 412) 6 HAR1 Hind); lia.
- intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS lyd Sd W (ms_mem ms) _ hb hn (h + 412) 6 HAR1 Hind); lia. }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hkept & Hpres2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; split;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?E22, ?E19; unfold w64; rewrite ?unsigned_lit_small by lia;
intros a Ha; first [lia | apply mbyte_of_aview; apply Hkept; rewrite ?ES; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc (l1_E regs T' i) 40 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDb : forall n, (n < 40)%nat -> ew Eb n = ew (l1_E regs T' i) n) by (intros n Hn; rewrite HEb; apply ew_havoc_old; exact Hn).
assert (EV : ew Eb 44 = v) by (rewrite HEb, <- Hv; reflexivity).
clear HEb.
assert (F2 : ew Eb 2 = w64 (sp0 - 112)) by (rewrite OLDb by lia; exact E2).
assert (F3 : ew Eb 3 = w64 (as_gp B)) by (rewrite OLDb by lia; exact E3).
assert (F4 : ew Eb 4 = w64 (as_tp B)) by (rewrite OLDb by lia; exact E4).
assert (F8 : ew Eb 8 = w64 (h + 440)) by (rewrite OLDb by lia; exact E8).
assert (F9 : ew Eb 9 = w64 h) by (rewrite OLDb by lia; exact E9).
assert (F18 : ew Eb 18 = w64 now) by (rewrite OLDb by lia; exact E18).
assert (F19 : ew Eb 19 = w64 (h + 384)) by (rewrite OLDb by lia; exact E19).
assert (F20 : ew Eb 20 = w64 (h + 412)) by (rewrite OLDb by lia; exact E20).
assert (F21 : ew Eb 21 = w64 (h + 48 * i + 20)) by (rewrite OLDb by lia; exact E21).
assert (F22 : ew Eb 22 = w64 (h + 48 * i)) by (rewrite OLDb by lia; exact E22).
assert (F23 : ew Eb 23 = w64 SHADOW_OFF) by (rewrite OLDb by lia; exact E23).
assert (F24 : ew Eb 24 = w64 (SHADOW_OFF + (h + 384) / 8)) by (rewrite OLDb by lia; exact E24).
assert (F25 : ew Eb 25 = w64 i) by (rewrite OLDb by lia; exact E25).
assert (F26 : ew Eb 26 = w64 5000000000) by (rewrite OLDb by lia; exact E26).
assert (F27 : ew Eb 27 = w64 (SHADOW_OFF + (h + 40 + 48 * i) / 8)) by (rewrite OLDb by lia; exact E27).
assert (F32 : ew Eb 32 = Z_to_bv 64 SB) by (rewrite OLDb by lia; exact E32).
assert (F33 : ew Eb 33 = Z_to_bv 64 (last_of T' i)) by (rewrite OLDb by lia; exact E33).
assert (F34 : ew Eb 34 = Z_to_bv 64 (u_at T' (48 * i + 8) 4)) by (rewrite OLDb by lia; exact E34).
assert (F35 : ew Eb 35 = Z_to_bv 64 (ch_of T' i)) by (rewrite OLDb by lia; exact E35).
assert (F36 : ew Eb 36 = Z_to_bv 64 (u_at T' 384 4)) by (rewrite OLDb by lia; exact E36).
clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E32 E33 E34 E35 E36.
clear SHOK. pose proof (l1_shok W lyd Sd mem2 md2 Eb h hb hn i (proj1 HJ2) Hind Hlo Hhi ltac:(lia) F22 F19 F32) as SHOK.
clear HJ. rename HJ2 into HJ.
assert (KCx : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
by (intros a Ha Hw; rewrite (Hkept a Ha) by (rewrite ES; lia); exact (KC a Ha Hw)).
clear KC. rename KCx into KC.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
- cbn [branch_taken sv_denot] in Hc. rewrite EV, Z.add_0_r, Z_to_bv_bv_unsigned in Hc. apply bv_eqb_eq in Hc.
assert (HM : mac_of T' i = U) by (apply (proj1 (l1_mac (w_H W) (ms_mem ms) h T' U i GT1 GU1 LT LU ltac:(lia))); exact (proj1 Hcmp Hc)).
assert (HFD : reac_hunt_step.hs_fd h T' U now i = false).
{ unfold reac_hunt_step.hs_fd. rewrite (proj2 (reac_hunt_step.hs_beqb _ _) HM). cbn [negb]. rewrite andb_false_r. reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (NEXTK fx (l1_freg_refl _) (hs_csr_refl _) HFD lyd Sd); [split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i].
- cbn [branch_taken sv_denot] in Hc. rewrite EV, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
assert (HM : mac_of T' i <> U).
{ intros HM. pose proof (proj2 (l1_mac (w_H W) (ms_mem ms) h T' U i GT1 GU1 LT LU ltac:(lia)) HM) as HM2.
pose proof (proj2 Hcmp HM2) as HV. rewrite HV in Hc. vm_compute in Hc. discriminate Hc. }
assert (HBE : bytes_eqb (mac_of T' i) U = false).
{ destruct (bytes_eqb (mac_of T' i) U) eqn:EB; [|reflexivity]. apply reac_hunt_step.hs_beqb in EB. contradiction. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
pose proof (l1_uat T' (48 * i + 8) 4) as UR8. pose proof (l1_uat T' (48 * i + 20) 4) as UR20.
pose proof (disco_table.s32_range T' (48 * i + 8)) as SR8. pose proof (disco_table.s32_range T' (48 * i + 20)) as SR20.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in UR8, UR20.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
+ cbn [branch_taken sv_denot] in Hc. rewrite F34 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by lia.
rewrite l1_sext in Hc by lia. change (bv_swrap 32 (u_at T' (48 * i + 8) 4)) with (s32_at T' (48 * i + 8)) in Hc.
rewrite reac_hunt_step.hs_eqb0 in Hc by lia. change (s32_at T' (48 * i + 8)) with (role_of_e T' i) in Hc.
assert (HFD : reac_hunt_step.hs_fd h T' U now i = false).
{ unfold reac_hunt_step.hs_fd. destruct (role_of_e T' i =? 0); [discriminate Hc|]. rewrite andb_false_r. reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (NEXTK fx (l1_freg_refl _) (hs_csr_refl _) HFD lyd Sd); [split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i].
+ cbn [branch_taken sv_denot] in Hc. rewrite F34 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by lia.
rewrite l1_sext in Hc by lia. change (bv_swrap 32 (u_at T' (48 * i + 8) 4)) with (s32_at T' (48 * i + 8)) in Hc.
rewrite reac_hunt_step.hs_eqb0 in Hc by lia. change (s32_at T' (48 * i + 8)) with (role_of_e T' i) in Hc.
assert (HRL : (role_of_e T' i =? 0) = true) by (destruct (role_of_e T' i =? 0); [reflexivity | discriminate Hc]).
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
* cbn [branch_taken sv_denot] in Hc. rewrite F35 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by (unfold ch_of; lia).
rewrite l1_sext in Hc by (unfold ch_of; lia). change (bv_swrap 32 (ch_of T' i)) with (s32_at T' (48 * i + 20)) in Hc.
rewrite reac_hunt_step.hs_eqb0 in Hc by lia. change (s32_at T' (48 * i + 20)) with (bv_swrap 32 (ch_of T' i)) in Hc.
rewrite reac_hunt_step.hs_swrap0 in Hc by (unfold ch_of; lia).
assert (HFD : reac_hunt_step.hs_fd h T' U now i = false).
{ unfold reac_hunt_step.hs_fd. rewrite Hc. cbn [negb]. rewrite andb_false_r. reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (NEXTK fx (l1_freg_refl _) (hs_csr_refl _) HFD lyd Sd); [split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i].
* cbn [branch_taken sv_denot] in Hc. rewrite F35 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small, Z.add_0_r in Hc by (unfold ch_of; lia).
rewrite l1_sext in Hc by (unfold ch_of; lia). change (bv_swrap 32 (ch_of T' i)) with (s32_at T' (48 * i + 20)) in Hc.
rewrite reac_hunt_step.hs_eqb0 in Hc by lia. change (s32_at T' (48 * i + 20)) with (bv_swrap 32 (ch_of T' i)) in Hc.
rewrite reac_hunt_step.hs_swrap0 in Hc by (unfold ch_of; lia).
assert (HCH : (ch_of T' i =? 0) = false) by (destruct (ch_of T' i =? 0); [discriminate Hc | reflexivity]).
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
prreg HS (1%bv : bv 5) S1. prreg HS (10%bv : bv 5) S10. prreg HS (11%bv : bv 5) S11. prreg HS (12%bv : bv 5) S12.
assert (RC : l1_regs (ms_regs ms0) sp0 h now i) by l1_regs_same h i.
pmkst HS. rewrite pa_sigma_reac_sender_kind.
pose proof (proj1 HJ) as HAR2.
destruct (l1_fix_mem sp0 h hb hn now T' U lyc Sc W memc _ HF Hbw Hcw ltac:(lia) KC) as (GT2 & GU2 & RR2 & GR2 & D602 & D382 & ROD2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR2 Hind) as (_ & _ & _ & Hbapp2 & Hbpres2 & _).
pose proof (blk_off_imgP B lyd Sd W _ _ hb hn HAR2 Hind) as Hbimg.
assert (SKS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (Hsp2 : spZ (ms_regs ms0) = sp0 - 112) by (unfold spZ; rewrite (proj1 RC); unfold w64; apply unsigned_lit_small; lia).
assert (VMk : forall o n, 0 <= o -> o + Z.of_nat n <= 48 -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (h + 48 * i + o) n (u_at T' (48 * i + o) n)).
{ intros o n Ho Hn. replace (h + 48 * i + o) with (h + (48 * i + o)) by lia. apply l1_vm; [exact GT2 | lia | rewrite LT; lia]. }
eapply SRr_bind.
{ apply (TSENDER fx lyd Sd W (ms_regs ms0) (ms_mem ms0) _ [] (h + 48 * i) now 0 (role_of_e T' i) (hd_of T' i) (slots_of T' i)
(ch_of T' i) (fs_of T' i)).
- apply (afn_pre_at SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd W (ms_mem ms0) _ 0 (ms_regs ms0) REAC_SENDER_KIND_STK (-112) []).
+ exact HJ.
+ rewrite Hsp2. lia.
+ reflexivity.
+ lia.
+ rewrite SKS. lia.
+ rewrite SKS, WS. lia.
+ rewrite S1. apply ret_ok_codeptr_v; [lia | reflexivity].
+ unfold raZ. rewrite S1, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. unfold IMG_LO in *. lia.
+ exact (proj1 (proj2 RC)).
+ exact (proj1 (proj2 (proj2 RC))).
+ left. split; [|reflexivity]. left. unfold s0Z. rewrite (proj1 (proj2 (proj2 (proj2 RC)))). unfold w64. rewrite unsigned_lit_small by lia. lia.
- exact ROD2.
- rewrite S10, F22. reflexivity.
- lia.
- replace (h + 48 * i) with (h + (6 * i) * 8) by lia. rewrite Z_mod_plus_full. exact Hh8.
- rewrite S11, F18. reflexivity.
- exact Rnow.
- exact S12.
- lia.
- intros _. split; [lia|]. split; [unfold in_app in *; lia|]. split; [unfold off_img in *; lia|].
split; [eapply (range_addressable_of_block SEGS B LAWS lyd Sd W (ms_mem ms0) _ hb hn (h + 48 * i + 8) 32 HAR2 Hind); lia|].
split; [intros a Ha; exact (proj1 (Hbpres2 a ltac:(lia)))|].
split; [lia|].
split; [unfold hd_of; pose proof (l1_uat T' (48 * i + 12) 1); change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in *; lia|].
split; [unfold slots_of; pose proof (l1_uat T' (48 * i + 16) 1); change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8) in *; lia|].
split; [unfold ch_of; lia|].
split; [unfold fs_of; pose proof (l1_uat T' (48 * i + 32) 8); change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in *; lia|].
split; [unfold role_of_e, s32_at; apply l1_vm_swrap; [apply VMk; lia | lia]|].
split; [unfold hd_of; replace (48 * i + 12) with (48 * i + 12) by lia; replace (h + 48 * i + 12) with (h + 48 * i + 12) by lia; apply (VMk 12 1%nat); lia|].
split; [unfold slots_of; apply (VMk 16 1%nat); lia|].
split; [unfold ch_of; apply (VMk 20 4%nat); lia|].
unfold fs_of; apply (VMk 32 8%nat); lia.
- exact RR2.
- exact GR2.
- exact D602.
- exact D382. }
cbv beta. intros W3 c3 Hwle3 (fq' & HFK & HCSR & fq3 & ly3 & S3 & regs3 & mem3 & md3 & -> & Hfr3 & Hcs3 & HJ3 & HP3 & HK10 & HPm & -> & Hmk).
pose proof (hs_freg_apost _ _ _ HFK Hfr3) as HFK3. rewrite HCSR in Hcs3. clear HFK HCSR Hfr3. clear fq'.
rename fq3 into fq'. rename HFK3 into HFK. rename Hcs3 into HCSR.
rewrite S1.
assert (HJ4 : ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] ly3 S3 W mem3 md3 0).
{ rewrite Hsp2 in HJ3.
pose proof (ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ3 ltac:(rewrite SKS, WS; lia) ltac:(lia) ltac:(intros a (rg & [] & _))) as HJ5.
cbn [app] in HJ5. rewrite Z.add_0_r in HJ5. exact HJ5. }
apply (l1_aftersk (fx := fq') Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U ly3 S3 mem3 md3 regs3 (hs_kind h T' now i)).
-- exact HF.
-- split; [exact HJ4|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
intros a Ha Hw. rewrite (l1_rawk (w_H W) (ms_mem ms0) mem3 (spZ (ms_regs ms0) - REAC_SENDER_KIND_STK) (spZ (ms_regs ms0)) Hmk a Ha) by (rewrite Hsp2, SKS; rewrite WS in Hw; lia).
exact (KC a Ha Hw).
-- exact (l1_regs_pres _ _ _ _ _ _ HP3 RC).
-- exact Hi.
-- exact HK10.
-- apply reac_hunt_step.hs_sk_range.
-- intros Hk3 lye Se meme mde regse HIe HRe. refine (NEXTK fq' HFK HCSR _ lye Se meme mde regse HIe HRe).
unfold reac_hunt_step.hs_fd. replace (hs_kind h T' now i =? 3) with false by (symmetry; apply Z.eqb_neq; exact Hk3).
rewrite andb_false_r. reflexivity.
-- intros Hk3 lye Se meme mde regse HIe HRe. refine (HITK fq' HFK HCSR _ lye Se meme mde regse HIe HRe).
unfold reac_hunt_step.hs_fd. rewrite HST, HBE, HRL, HCH, Hk3. reflexivity.
Qed.
Lemma l1_head : forall Q (ly : alayout) S W0 mem0 md0 lyc Sc (W : world SEGS) memc
(sp0 h hb hn now i : Z) (T' U : list byte) lyd Sd memd mdd (regs : bvmap 5 word),
l1_fix sp0 h hb hn now T' U lyc Sc W memc ->
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lyd Sd memd mdd ->
l1_regs regs sp0 h now i -> 0 <= i < n_of T' ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
reac_hunt_step.hs_fd h T' U now i = false -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x77d8) regse meme mde) Q) ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
reac_hunt_step.hs_fd h T' U now i = true -> forall lye Se meme mde (regse : bvmap 5 word),
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde -> l1_regs regse sp0 h now i ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x795c) regse meme mde) Q) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x7760) regs memd mdd) Q.
Proof.
intros Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs HF HI HR Hi NEXTK HITK.
pose proof HF as (Hin & Hlo & Hhi & Hh0 & Hh8 & LT & TOK & LU & Rnow & GT & GU & RR & GR & D60 & D38 & HROD).
pose proof HI as (HJ & HP & HK).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (Hind : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hind) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
assert (GTd : garr8 SEGS (mrestrict (w_H W) memd) h (map (fun b : byte => bv_unsigned b) T')).
{ apply (l1_kept_garr8 W memc memd h _ (sp0 - REAC_HUNT_STEP_STK) (sp0 - 112)); [exact HK | lia | rewrite length_map, LT; lia | lia | exact GT]. }
destruct (l1_envf regs T' i sp0 h now HR) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E32 & E33 & E34 & E35 & E36).
assert (HEI : img_env VAL A_LIM (l1_E regs T' i)) by (unfold l1_E; apply Eimg_env).
rename HK into KC.
destruct (l1_build W lyd Sd memd mdd regs h hb hn i T' 0x7760 HAR Hind Hlo Hhi Hh8 LT ltac:(lia) GTd R19 R21 R22 R23 R24 R27) as [HS SHOK].
unfold cfg_at. change (w64 (BASE + 0x7760)) with (Z_to_bv 64 (BASE + 0x7760)).
pose proof (l1_uat T' (48 * i + 40) 8) as UL. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in UL.
assert (LE : last_of T' i = u_at T' (48 * i + 40) 8) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply l1_awr. }
l1_kc W memc sp0.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
- cbn [branch_taken sv_denot] in Hc. rewrite E33, E18 in Hc. unfold w64 in Hc. rewrite !unsigned_lit_small, !Z.add_0_r in Hc by lia.
rewrite l1_ltu in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc.
assert (HST : disco_stale T' i now = false) by (apply reac_hunt_step.hs_st1; lia).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7778.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (l1_live Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd); [exact HF | split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i | exact Hi | exact HST | exact NEXTK | exact HITK].
- cbn [branch_taken sv_denot] in Hc. rewrite E33, E18 in Hc. unfold w64 in Hc. rewrite !unsigned_lit_small, !Z.add_0_r in Hc by lia.
rewrite l1_ltu in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7778.
{ apply l1_awr. }
l1_kc W memc sp0.
psrr_branch_tok RUN paj_branch HS SHOK Bspan.
+ cbn [branch_taken sv_denot] in Hc0. rewrite E26, E18, E33 in Hc0. unfold w64 in Hc0. rewrite !unsigned_lit_small, !Z.add_0_r in Hc0 by lia.
rewrite l1_subm in Hc0 by lia. rewrite l1_ltu in Hc0 by lia.
assert (HST : disco_stale T' i now = true) by (rewrite reac_hunt_step.hs_st2 by lia; exact Hc0).
assert (HFD : reac_hunt_step.hs_fd h T' U now i = false) by (unfold reac_hunt_step.hs_fd; rewrite HST; reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x77d8.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (NEXTK fx (l1_freg_refl _) (hs_csr_refl _) HFD lyd Sd); [split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i].
+ cbn [branch_taken sv_denot] in Hc0. rewrite E26, E18, E33 in Hc0. unfold w64 in Hc0. rewrite !unsigned_lit_small, !Z.add_0_r in Hc0 by lia.
rewrite l1_subm in Hc0 by lia. rewrite l1_ltu in Hc0 by lia.
assert (HST : disco_stale T' i now = false) by (rewrite reac_hunt_step.hs_st2 by lia; exact Hc0).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7778.
{ apply l1_awr. }
l1_kc W memc sp0.
l1_prregs HS.
pmkst HS.
eapply (l1_live Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd); [exact HF | split; [exact HJ | split; [exact HP | exact KC]] | l1_regs_same h i | exact Hi | exact HST | exact NEXTK | exact HITK].
Qed.
End w2.
Definition l1_P (k : nat) : Prop :=
forall (fx0 fx : YK11.FPState) (Q : world SEGS -> config -> Prop) (ly : alayout) S W0 mem0 md0 lyc Sc (W : world SEGS) memc
(sp0 h hb hn now i : Z) (T' U : list byte) lyd Sd memd mdd (regs : bvmap 5 word),
Z.of_nat k = n_of T' - i ->
freg_kept (@YK11.fp_regs fx0) (@YK11.fp_regs fx) -> hs_csr fx0 fx ->
l1_fix sp0 h hb hn now T' U lyc Sc W memc ->
l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lyd Sd memd mdd ->
l1_regs regs sp0 h now i -> 0 <= i < n_of T' ->
(forall j, 0 <= j < i -> reac_hunt_step.hs_fd h T' U now j = false) ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx0) (@YK11.fp_regs fq') -> hs_csr fx0 fq' ->
forall lye Se meme mde (regse : bvmap 5 word), l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde ->
(exists j, l1_regs regse sp0 h now j) -> desk_geometry_live h T' U now = false ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x782c) regse meme mde) Q) ->
(forall fq' : YK11.FPState, freg_kept (@YK11.fp_regs fx0) (@YK11.fp_regs fq') -> hs_csr fx0 fq' ->
forall lye Se meme mde (regse : bvmap 5 word), l1_inv sp0 h ly S W0 mem0 md0 lyc Sc W memc lye Se meme mde ->
(exists j, l1_regs regse sp0 h now j) -> desk_geometry_live h T' U now = true ->
SRr SEGS W (cfg_at (fx := fq') SEGS (BASE + 0x795c) regse meme mde) Q) ->
SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + 0x7760) regs memd mdd) Q.
Lemma l1_loop : forall k, l1_P k.
Proof.
induction k as [|k IH]; intros fx0 fx Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs
Hk HFK HCS HF HI HR Hi HNW NOHIT HIT; [lia|].
apply (l1_head (fx := fx) Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyd Sd memd mdd regs HF HI HR Hi).
- intros fq' HFK1 HCS1 HFD lye Se meme mde regse HIe HRe.
assert (HFK2 : freg_kept (@YK11.fp_regs fx0) (@YK11.fp_regs fq')) by exact (l1_freg_trans _ _ _ HFK HFK1).
assert (HCS2 : hs_csr fx0 fq') by exact (hs_csr_trans _ _ _ HCS HCS1).
assert (HNW2 : forall j, 0 <= j < i + 1 -> reac_hunt_step.hs_fd h T' U now j = false).
{ intros j Hj. destruct (Z.eq_dec j i) as [->|Hji]; [exact HFD | apply HNW; lia]. }
apply (l1_next (fx := fq') Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lye Se meme mde regse HF HIe HRe Hi).
+ intros Hlt lyf Sf memf mdf regsf HIf HRf.
exact (IH fx0 fq' Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now (i + 1) T' U lyf Sf memf mdf regsf ltac:(lia) HFK2 HCS2 HF HIf HRf
ltac:(lia) HNW2 NOHIT HIT).
+ intros Hge lyf Sf memf mdf regsf HIf HRf.
apply (NOHIT fq' HFK2 HCS2 lyf Sf memf mdf regsf HIf (ex_intro _ (i + 1) HRf)).
apply reac_hunt_step.hs_dgl_false. intros j Hj. apply HNW2. lia.
- intros fq' HFK1 HCS1 HFD lye Se meme mde regse HIe HRe.
apply (HIT fq' (l1_freg_trans _ _ _ HFK HFK1) (hs_csr_trans _ _ _ HCS HCS1) lye Se meme mde regse HIe (ex_intro _ i HRe)).
exact (reac_hunt_step.hs_dgl_true h T' U now i Hi HFD).
Qed.
Section w. Context {fx : YK11.FPState}.
Lemma hs_loop1 : forall (Q : world SEGS -> config -> Prop)
  (ly lyc : alayout) (S Sc : astate) (W0 W : world SEGS) (mem0 memc : word -> option byte)
  (md0 mdc : Model) (regsc : bvmap 5 word) (sp0 h now hb hn i : Z) (T' U : list byte),
  ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyc Sc W memc mdc 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_HI 96) + -1628) 8 D3837 ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn -> h mod 8 = 0 ->
  length T' = 400%nat -> table_ok T' ->
  garr8 SEGS (mrestrict (w_H W) memc) h (map (fun b : byte => bv_unsigned b) T') ->
  length U = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (h + 412) (map (fun b : byte => bv_unsigned b) U) ->
  0 <= now < 2 ^ 64 -> 0 <= i < n_of T' ->
  (forall j, 0 <= j < i -> reac_hunt_step.hs_fd h T' U now j = false) ->
  spZ regsc = sp0 - 112 -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 8 = w64 (h + 440) -> getr regsc 9 = w64 h -> getr regsc 18 = w64 now ->
  getr regsc 19 = w64 (h + 384) -> getr regsc 20 = w64 (h + 412) -> getr regsc 21 = w64 (h + 48 * i + 20) ->
  getr regsc 22 = w64 (h + 48 * i) -> getr regsc 23 = w64 SHADOW_OFF ->
  getr regsc 24 = w64 (SHADOW_OFF + (h + 384) / 8) -> getr regsc 25 = w64 i ->
  getr regsc 26 = w64 5000000000 -> getr regsc 27 = w64 (SHADOW_OFF + (h + 40 + 48 * i) / 8) ->
  (forall (fq' : YK11.FPState) (lyd : alayout) (Sd : astate) (Wd : world SEGS)
          (memd : word -> option byte) (mdd : Model) (regsd : bvmap 5 word),
     freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
     ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd Wd memd mdd 0 ->
     desk_geometry_live h T' U now = false ->
     Wd = W /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) ->
        aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a) ->
     Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) ->
     getr regsd 2 = Z_to_bv 64 (sp0 - 112) -> getr regsd 3 = w64 (as_gp B) -> getr regsd 4 = w64 (as_tp B) ->
     getr regsd 8 = Z_to_bv 64 (h + 440) -> getr regsd 9 = Z_to_bv 64 h -> getr regsd 18 = Z_to_bv 64 now ->
     getr regsd 19 = Z_to_bv 64 (h + 384) -> getr regsd 23 = Z_to_bv 64 SHADOW_OFF ->
     getr regsd 24 = Z_to_bv 64 (SHADOW_OFF + (h + 384) / 8) ->
     SRr SEGS Wd (cfg_at (fx := fq') SEGS (BASE + 0x782c) regsd memd mdd) Q) ->
  (forall (fq' : YK11.FPState) (lyd : alayout) (Sd : astate) (Wd : world SEGS)
          (memd : word -> option byte) (mdd : Model) (regsd : bvmap 5 word),
     freg_kept (@YK11.fp_regs fx) (@YK11.fp_regs fq') -> hs_csr fx fq' ->
     ajournal SEGS B REAC_HUNT_STEP_STK sp0 (HSFP h) ly S W0 mem0 md0 [] lyd Sd Wd memd mdd 0 ->
     desk_geometry_live h T' U now = true ->
     Wd = W /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - REAC_HUNT_STEP_STK <= a < sp0 - 112) ->
        aview SEGS (w_H W) memd a = aview SEGS (w_H W) memc a) ->
     Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) ->
     getr regsd 2 = Z_to_bv 64 (sp0 - 112) -> getr regsd 3 = w64 (as_gp B) -> getr regsd 4 = w64 (as_tp B) ->
     getr regsd 8 = Z_to_bv 64 (h + 440) -> getr regsd 23 = Z_to_bv 64 SHADOW_OFF ->
     SRr SEGS Wd (cfg_at (fx := fq') SEGS (BASE + 0x795c) regsd memd mdd) Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x7760) regsc memc mdc) Q.
Proof.
intros Q ly lyc S Sc W0 W mem0 memc md0 mdc regsc sp0 h now hb hn i T' U HJ HROD HRA HRT HD6 HD3 Hin Hlo Hhi Hh8 LT HTOK HG
LU HGU Rnow Hi HNW R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 NOHIT HIT.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn (proj1 HJ) Hin) as (_ & Hb4096 & _).
apply (l1_loop (Z.to_nat (n_of T' - i)) fx fx Q ly S W0 mem0 md0 lyc Sc W memc sp0 h hb hn now i T' U lyc Sc memc mdc regsc).
- lia.
- apply l1_freg_refl.
- apply hs_csr_refl.
- unfold l1_fix. repeat (split; [eassumption|]). split; [lia|]. repeat (split; [eassumption|]). exact HROD.
- split; [exact HJ|]. split; [apply Permutation_refl|]. intros a _ _. reflexivity.
- unfold l1_regs. split; [unfold w64; rewrite <- R2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned|].
repeat (split; [eassumption|]). exact R27.
- exact Hi.
- exact HNW.
- intros fq' HFK HCS lye Se meme mde regse (HJe & HPe & HKe) (j & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & _ & _ & _ & Q23 & Q24 & _) HDG.
exact (NOHIT fq' lye Se W meme mde regse HFK HCS HJe HDG (conj eq_refl HKe) HPe Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q23 Q24).
- intros fq' HFK HCS lye Se meme mde regse (HJe & HPe & HKe) (j & Q2 & Q3 & Q4 & Q8 & _ & _ & _ & _ & _ & _ & Q23 & _) HDG.
exact (HIT fq' lye Se W meme mde regse HFK HCS HJe HDG (conj eq_refl HKe) HPe Q2 Q3 Q4 Q8 Q23).
Qed.
End w.
Lemma a1_sub_app_l : forall (A L2 : list byte) (k : Z) (n : nat), 0 <= k -> (Z.to_nat k + n <= length A)%nat ->
  sub (A ++ L2) k n = sub A k n.
Proof.
intros A L2 k n Hk Hn. unfold sub. rewrite skipn_app.
replace (Z.to_nat k - length A)%nat with 0%nat by lia. cbn [skipn].
rewrite firstn_app. rewrite length_skipn. replace (n - (length A - Z.to_nat k))%nat with 0%nat by lia.
cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.
Lemma a1_sub_app_r : forall (A L2 : list byte) (k : Z) (n : nat), Z.of_nat (length A) <= k ->
  sub (A ++ L2) k n = sub L2 (k - Z.of_nat (length A)) n.
Proof.
intros A L2 k n Hk. unfold sub. rewrite skipn_app.
rewrite skipn_all2 by lia. cbn [app]. f_equal. f_equal. lia.
Qed.
Lemma a1_u_range : forall (A : list byte) (k : Z) (n : nat), 0 <= u_at A k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros A k n. unfold u_at.
pose proof (YK11.bytes_le_to_Z_bound (sub A k n)) as Hb.
pose proof (YK11.bytes_le_to_Z_nonneg (sub A k n)) as Hb0.
assert (Hl : (length (sub A k n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact Hb0|]. eapply Z.lt_le_trans; [exact Hb|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma a1_u32_small : forall (A : list byte) (k : Z), 0 <= k -> (Z.to_nat k + 4 <= length A)%nat ->
  0 <= bv_swrap 32 (u_at A k 4) -> u_at A k 4 = bv_swrap 32 (u_at A k 4).
Proof.
intros A k Hk Hn H0.
pose proof (a1_u_range A k 4) as Hb. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma a1_img_len : forall h now Hb, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
  length (hs_arb h Hb now) = 32%nat -> length (hs_img h now Hb) = 480%nat.
Proof.
intros h now Hb LH LT LA. unfold hs_img, sub. rewrite !length_app, !length_firstn, !length_skipn, LT, LA, LH.
change (Z.to_nat 400) with 400%nat. change (Z.to_nat 476) with 476%nat. reflexivity.
Qed.
Lemma a1_img_hb : forall h now Hb k n, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
  400 <= k -> (Z.to_nat k + n <= 444)%nat -> sub (hs_img h now Hb) k n = sub Hb k n.
Proof.
intros h now Hb k n LH LT Hk Hn. unfold hs_img.
rewrite a1_sub_app_r by lia. rewrite LT.
rewrite a1_sub_app_l.
2: lia.
2: unfold sub; rewrite length_firstn, length_skipn, LH; change (Z.to_nat 400) with 400%nat; lia.
rewrite reac_hunt_step.hs_sub_sub by lia. f_equal. lia.
Qed.
Lemma a1_img_tab : forall h now Hb k n, length (hs_table Hb now) = 400%nat -> 0 <= k -> (Z.to_nat k + n <= 400)%nat ->
  sub (hs_img h now Hb) k n = sub (hs_table Hb now) k n.
Proof. intros h now Hb k n LT Hk Hn. unfold hs_img. apply a1_sub_app_l; lia. Qed.
Lemma a1_verdict : forall h Hb now, s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 <> 2 ->
  desk_geometry_live h (hs_table Hb now) (sub Hb 412 6) now = false ->
  hs_verdict h Hb now = if negb (s32_at Hb 420 =? 0) then 1
    else if (now - u_at Hb 424 8) mod 2 ^ 64 <? 3000000000 then 0
    else if box_present h (hs_table Hb now) now then 1 else 0.
Proof.
intros h Hb now Hp Hst Hd. unfold hs_verdict. rewrite Hp, Hd. unfold decide_model.
replace (s32_at (hs_arb h Hb now) 0 =? 2) with false by (symmetry; apply Z.eqb_neq; exact Hst).
reflexivity.
Qed.
Definition a1_regs : list sv :=
  sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 32 0)).
Definition a1_stk : YP09.region := YP09.mkRegion (Some 2%nat) 0 8 0 8 [].
Definition a1_hreg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 420 432 0 0 [YP09.mkChunk 420 (CVal 4 (SOff 33 0)); YP09.mkChunk 424 (CVal 8 (SOff 34 0))].
Definition a1_nreg : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition a1_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, PTR 3); (18%nat, mkAF 0 (2 ^ 64 - 1) 0); (19%nat, PTR 3);
            (32%nat, mkAF SB SB 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 64 - 1) 0);
            (35%nat, mkAF 0 8 0) ] [] [].
Definition a1_ss (pc : Z) : sstate := mkSS pc a1_regs [a1_stk; a1_hreg; a1_nreg] None a1_facts.
Definition a1_Bx : sv := SOff 32 0.
Definition a1_SH : list shent := [ mkSHE 9 0 480; mkSHE 19 0 8 ].
Definition a1_E (regs : bvmap 5 word) (sil op n : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 sil; Z_to_bv 64 op; Z_to_bv 64 n]).
Lemma a1_U_sh : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SB -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 50 ->
  U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = SB + (v + c) / 8 /\
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = (v + c) / 8 + SB.
Proof.
intros E n v c Hn H32 Hv Hc. rewrite !U_SAlu, !U_SOff, !U_SLit, Hn, H32. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SB; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite (zcanon_id (v + c)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 50) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id (SB + 0)) by (unfold M64, SB; lia).
rewrite Z.add_0_r. split; apply zcanon_id; unfold M64, SB; lia.
Qed.
Lemma a1_U_sub : forall E a b x y, U E a = x -> U E b = y ->
  U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = (x - y) mod 2 ^ 64.
Proof.
intros E a b x y Ha Hb. rewrite U_SAlu, U_SMd, U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Z.mul_mod_idemp_r by lia. rewrite Z.add_mod_idemp_r by lia.
replace (x + y * -1) with (x - y) by lia. reflexivity.
Qed.
Lemma a1_bge : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. unfold U in Ha, Hb. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite Ha, Hb.
assert (Hs : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z).
{ intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
rewrite !Hs by lia. reflexivity.
Qed.
Lemma a1_aview_mod : forall H (m : word -> option byte) x, aview SEGS H m x = aview SEGS H m (x mod 2 ^ 64).
Proof.
intros H m x. unfold aview, mbyte.
replace (Z_to_bv 64 (x mod 2 ^ 64)) with (Z_to_bv 64 x); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma a1_ro_low : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
- apply pa_segs_low. apply pa_relro_img. exact Hr.
Qed.
Lemma a1_hi_near : forall kk (rd : bv 5) j, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  exists s, - 2 ^ 31 <= s < 2 ^ 31 /\ VAL (A_HI j) = (BASE + kk + s) mod 2 ^ 64 /\ 0 <= BASE + kk < kLowMemEnd.
Proof.
intros kk rd j Hk40 Hk. pose proof pa_B_ok as HB.
rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert kk _ Hk) as [Hc [Hk0 Hk4]].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + kk)) as [wz|] eqn:Hf; [|discriminate Hc].
assert (Himg : 0 <= BASE + kk < kLowMemEnd).
{ pose proof (pa_tbl_ok _ _ Hf) as Hfw.
  unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
  unfold code_read in Hfw.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
  destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
  assert (HI : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk)))).
  { exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
  pose proof (pa_segs_low _ HI) as HR.
  rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  rewrite Z.mod_small in HR by lia. lia. }
destruct (decode_any (Z_to_bv 32 wz)) as [[ins isz]|]; [|discriminate Hc].
apply andb_prop in Hc as [_ Hc]. destruct ins; try (cbn in Hc; discriminate Hc).
apply andb_prop in Hc as [_ Hc]. apply Z.eqb_eq in Hc. unfold auipc_val, zcanon, M64 in Hc.
exists (bv_signed (bv_concat 32 imm (Z_to_bv 12 0))).
pose proof (bv_signed_in_range 32 (bv_concat 32 imm (Z_to_bv 12 0)) ltac:(discriminate)) as Hr.
change (bv_half_modulus 32) with (2 ^ 31) in Hr.
split; [lia|]. split; [rewrite <- Hc; reflexivity | exact Himg].
Qed.
Lemma a1_hi_win : forall kk (rd : bv 5) j c x lo hi, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  -4096 <= c <= 4096 -> 0 <= x < 8 -> alloc_ceiling <= lo -> hi <= 2 ^ 47 ->
  ~ (lo <= (VAL (A_HI j) + c + x) mod 2 ^ 64 < hi).
Proof.
intros kk rd j c x lo hi Hk40 Hk Hc Hx Hlo Hhi.
destruct (a1_hi_near kk rd j Hk40 Hk) as (s & Hs & Hv & Hb).
pose proof (asan_consts) as (C1 & _ & _ & _ & C5).
rewrite Hv. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
revert Hs Hb Hc Hx Hlo Hhi C1 C5. clear. intros. Z.div_mod_to_equations. lia.
Qed.
Lemma a1_mem_kept : forall (W : world SEGS) (m0 m1 : word -> option byte) sp0,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) m0 a) ->
  alloc_ceiling <= sp0 - 112 -> sp0 <= 2 ^ 47 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m0) ->
  range_addressable (aview SEGS (w_H W) m0) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) m0) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) m0) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) m0) (VAL (A_HI 96) + -1628) 8 D3837 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m1) /\
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
  garr8 SEGS (mrestrict (w_H W) m1) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
  val_mem SEGS (mrestrict (w_H W) m1) (VAL (A_HI 97) + -1832) 8 D6000 /\
  val_mem SEGS (mrestrict (w_H W) m1) (VAL (A_HI 96) + -1628) 8 D3837.
Proof.
intros W m0 m1 sp0 HK Hlo Hhi H1 H2 H3 H4 H5.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (AK : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m1 x = aview SEGS (w_H W) m0 x).
{ intros x Hx. apply HK; lia. }
assert (AKm : forall x, ~ (sp0 - 112 <= x mod 2 ^ 64 < sp0 - 104) -> aview SEGS (w_H W) m1 x = aview SEGS (w_H W) m0 x).
{ intros x Hx. rewrite (a1_aview_mod (w_H W) m1 x), (a1_aview_mod (w_H W) m0 x).
  apply HK; [apply Z.mod_pos_bound; lia | exact Hx]. }
pose proof (pa_obj_img 65 ltac:(unfold disco_nobj; lia)) as H65.
assert (HimgL : 0 <= IMG_LO /\ IMG_TOP <= kLowMemEnd) by (unfold IMG_LO, IMG_TOP, kLowMemEnd; lia).
assert (LR : length RATES = 12%nat) by reflexivity.
split; [|split; [|split; [|split]]].
- intros a Hro Ho He. pose proof (a1_ro_low a Hro) as Ha. rewrite AK by lia. exact (H1 a Hro Ho He).
- intros x Hx. destruct (H2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite AK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
  revert Hx H65 HimgL C1 C5. clear. intros. Z.div_mod_to_equations. lia.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) m0 m1); [|exact H3].
  intros a Ha. rewrite length_map, LR in Ha. apply AK. lia.
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m0 m1); [|exact H4].
  intros x Hx. apply AKm.
  replace x with (VAL (A_HI 97) + -1832 + (x - (VAL (A_HI 97) + -1832))) by lia.
  apply (a1_hi_win 31476 11%bv 97 (-1832) (x - (VAL (A_HI 97) + -1832)));
  [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m0 m1); [|exact H5].
  intros x Hx. apply AKm.
  replace x with (VAL (A_HI 96) + -1628 + (x - (VAL (A_HI 96) + -1628))) by lia.
  apply (a1_hi_win 31472 10%bv 96 (-1628) (x - (VAL (A_HI 96) + -1628)));
  [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
Qed.
Section w2. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma a1_entry : forall (pc : Z) (W : world SEGS) lyc Sc (regs : bvmap 5 word) memc mdc (sp h now hb hn sil op n : Z),
  AR SEGS B lyc Sc W memc mdc ->
  In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn -> h mod 8 = 0 ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> h + 480 <= sp ->
  (forall a, sp <= a < sp + 8 -> apresent (w_H W) memc a) ->
  0 <= now < 2 ^ 64 -> 0 <= sil < 2 ^ 32 -> 0 <= op < 2 ^ 64 -> 0 <= n <= 8 ->
  spZ regs = sp -> getr regs 9 = w64 h -> getr regs 18 = w64 now -> getr regs 19 = w64 (h + 384) ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 24 = w64 (SHADOW_OFF + (h + 384) / 8) ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 420) 4 sil ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 424) 8 op ->
  val_mem SEGS (mrestrict (w_H W) memc) (h + 384) 4 n ->
  st_ok_pi SEGS VAL (a1_E regs sil op n) (a1_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS a1_Bx a1_SH (a1_E regs sil op n) (mrestrict (w_H W) memc).
Proof.
intros pc W lyc Sc regs memc mdc sp h now hb hn sil op n HAR Hin Hlo Hhi Hh8 Hsp Hsp16 Hhsp Hspw Rnow Rsil Rop Rn
  Hspr R9 R18 R19 R23 R24 V420 V424 V384.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc hb hn HAR Hin) as (_ & Hbb4096 & Hbbceil & Hbbapp & _ & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
rewrite restrict_mkst_fx.
set (E := a1_E regs sil op n).
assert (EL : forall k, (k < A_TEXT)%nat ->
  ew E k = ew (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 sil; Z_to_bv 64 op; Z_to_bv 64 n]) k)
  by (intros k Hk; subst E; unfold a1_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (h + 384)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 sil) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 op) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hspr).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (UBx : U E a1_Bx = SHADOW_OFF) by (unfold a1_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
split.
- unfold a1_ss. apply pa_entry_st_ok_full.
  + unfold a1_regs.
    apply regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite denot_lit_U. replace (h + 384) with (h + 384 + 0) in R24 by lia.
         rewrite (proj2 (a1_U_sh E 19 (h + 384) 0 E19 E32 ltac:(lia) ltac:(lia))), Z.add_comm. exact R24. }
    apply regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact R23].
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold a1_stk, a1_hreg, a1_nreg.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply Hspw; lia | constructor].
    * rewrite (VB 9%nat h E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ h 420 4 (SOff 33 0) sil);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V420].
      -- apply (chunk_ok_val SEGS E _ h 424 8 (SOff 34 0) op);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V424].
    * rewrite (VB 19%nat (h + 384) E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (h + 384) 0 4 (SOff 35 0) n);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact V384.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, a1_stk, a1_hreg, a1_nreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
    change (bv_unsigned (ew E 9)) with (base_val E (Some 9%nat)). change (bv_unsigned (ew E 19)) with (base_val E (Some 19%nat)).
    rewrite (VB 9%nat h E9) by lia. rewrite (VB 19%nat (h + 384) E19) by lia.
    revert Hhsp. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [a1_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E9, E18, E19, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hlo Hhi Hbb4096 Hbbceil Hh8 Hsp Hsp16 Rnow Rsil Rop Rn C1 Hrq0 Hrq1. clear. unfold SB. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    all: Z.div_mod_to_equations; lia.
- unfold sh_ok, a1_SH. constructor; [|constructor; [|constructor]].
  + eapply (shent_ok_of_range SEGS (w_H W) memc E a1_Bx 9 h 480 h 0 480).
    * eapply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn h 480 HAR Hin); lia.
    * exact UBx.
    * apply (U_atom E 9 h E9). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      unfold SHADOW_OFF in *. revert Hx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 C1 C3.
      clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
  + eapply (shent_ok_of_range SEGS (w_H W) memc E a1_Bx 19 (h + 384) 8 (h + 384) 0 8).
    * eapply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc hb hn (h + 384) 8 HAR Hin); lia.
    * exact UBx.
    * apply (U_atom E 19 (h + 384) E19). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
      unfold SHADOW_OFF in *. revert Hx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 C1 C3.
      clear. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma a1_sext_eq0 : forall E k u, ew E k = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  (U E (SExt true 32 (SOff k 0)) =? U E (SLit 0)) = (bv_swrap 32 u =? 0).
Proof.
intros E k u Hk Hu. rewrite U_SExt, (U_atom E k u Hk) by lia. rewrite U_SLit. cbv beta iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia.
assert (R : - 2 ^ 31 <= bv_swrap 32 u < 2 ^ 31).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia. }
unfold zcanon, M64. rewrite Zmod_0_l.
destruct (Z.eqb_spec (bv_swrap 32 u) 0) as [E0 | E0].
- rewrite E0, Zmod_0_l. reflexivity.
- apply Z.eqb_neq. intros C. apply E0. revert R C. clear. intros. Z.div_mod_to_equations. lia.
Qed.
Lemma a1_fin : forall (fq fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte)
  lyc Sc Wc memc lyd Sd memd mdd (regsd : bvmap 5 word) (pc v : Z),
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyd Sd Wc memd mdd 0 ->
  freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fq) -> hs_csr fq0 fq ->
  (pc = 0x7664 /\ getr regsd 10 = w64 v \/ pc = 0x795c /\ v = 0) ->
  getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
  getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_HUNT_STEP_STK <= a < spZ regs - 104) ->
     aview SEGS (w_H Wc) memd a = aview SEGS (w_H Wc) memc a) ->
  hs_frame regs (mrestrict (w_H Wc) memc) (spZ regs) ->
  0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  hunt_ok Hb -> length (hs_table Hb now) = 400%nat -> length (hs_arb h Hb now) = 32%nat ->
  garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
  v = hs_verdict h Hb now -> hunt_ok (hs_hunt h Hb now) ->
  Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) -> Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  SRr SEGS Wc (cfg_at (fx := fq) SEGS (BASE + pc) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc memc lyd Sd memd mdd regsd pc v HPRE HJd HFk HFc Hpc
  R2 R3 R4 R8 R23 HK HFR Hh0 Hh8 Hin Hlo Hhi HOK LT LA HG Hv HOKH HPd HPc.
pose proof HJd as (HARd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HsJ & _ & _).
pose proof HsJ as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
assert (Hind : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HPd | exact Hin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HARd Hind) as (_ & Hbb4096 & Hbbceil & _ & _ & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof HOK as (LHb & _ & _ & _).
assert (LI : length (hs_img h now Hb) = 480%nat) by (apply a1_img_len; assumption).
set (sp0 := spZ regs) in *.
assert (Hsp0 : 0 <= sp0 < 2 ^ 64) by (subst sp0; unfold spZ; apply bv_unsigned_in_range).
apply (@hs_epi fq fq0 ly S W regs mem md ch h now hb hn Hb lyd Sd Wc regsd memd mdd pc v HPRE HJd HFk HFc Hpc
  R2 R3 R4 R8 R23).
- apply (hs_frame_kept regs (w_H Wc) (w_H Wc) memc memd sp0); [|exact HFR].
  intros a Ha. apply HK; lia.
- exact Hh0.
- exact Hh8.
- exact Hind.
- exact Hlo.
- exact Hhi.
- exact HOK.
- exact LT.
- exact LA.
- apply (garr8_aview_kept SEGS (w_H Wc) (w_H Wc) memc memd); [|exact HG].
  intros a Ha. rewrite length_map, LI in Ha. apply HK; lia.
- exact Hv.
- exact HOKH.
- eapply Permutation_trans; [exact HPd | exact HPc].
Qed.
Ltac a1_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac a1_awr Usp :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc ly own) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-112)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |];
  awr_ok_tac.
Ltac a1_kept HFr Usp HK sp0 :=
  let HK2 := fresh "HK" in let HK3 := fresh "HK" in
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) =>
  assert (HK2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) -> aview SEGS H m1 a = aview SEGS H m0 a)
    by (intros a Ha H1; rewrite !(aview_mbyte SEGS); f_equal; apply (mbyte_of_frame_x SEGS E rs _ _ a HFr Ha);
        intros r Hr; let rs' := eval vm_compute in rs in change (In r rs') in Hr;
        repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; first [rewrite Usp; lia | lia] |]);
        destruct Hr);
  lazymatch type of HK with forall a, _ -> _ -> aview SEGS H m0 a = aview SEGS H ?mc a =>
  assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) -> aview SEGS H m1 a = aview SEGS H mc a)
    by (intros a Ha H1; rewrite (HK2 a Ha H1); exact (HK a Ha H1))
  end end;
  clear HK HK2 HFr; rename HK3 into HK;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Lemma hs_after1 : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte)
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc,
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memc mdc 0 ->
  freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 96) + -1628) 8 D3837 ->
  getr regsc 2 = w64 (spZ regs - 112) -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = w64 (h + 440) -> getr regsc 9 = w64 h -> getr regsc 18 = w64 now ->
  getr regsc 19 = w64 (h + 384) -> getr regsc 23 = w64 SHADOW_OFF ->
  getr regsc 24 = w64 (SHADOW_OFF + (h + 384) / 8) ->
  hs_frame regs (mrestrict (w_H Wc) memc) (spZ regs) ->
  0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 <= now < 2 ^ 64 ->
  hunt_ok Hb -> length (hs_table Hb now) = 400%nat -> table_ok (hs_table Hb now) -> length (hs_arb h Hb now) = 32%nat ->
  garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
  s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 <> 2 ->
  desk_geometry_live h (hs_table Hb now) (sub Hb 412 6) now = false ->
  hunt_ok (hs_hunt h Hb now) ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  SRr SEGS Wc (cfg_at (fx := fx) SEGS (BASE + 0x782c) regsc memc mdc) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc regsc memc mdc HPRE HJ HFk HFc HRO HRA HRT HD6 HD3
  R2 R3 R4 R8 R9 R18 R19 R23 R24 HFR Hh0 Hh8 Hin Hlo Hhi Rnow HOK LT HTOK LA HG Hpin Hst Hdgl HOKH HPerm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpJ & HsJ & _ & _).
pose proof HsJ as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (Hbb16 & Hbb4096 & Hbbceil & Hbbapp & Hbbpres & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
pose proof HOK as (LHb & _ & _ & _).
pose proof HTOK as (T1 & _). unfold tbl_T1 in T1.
set (sp0 := spZ regs) in *.
assert (Hsp0 : 0 <= sp0 < 2 ^ 64) by (subst sp0; unfold spZ; apply bv_unsigned_in_range).
assert (LI : length (hs_img h now Hb) = 480%nat) by (apply a1_img_len; assumption).
assert (Usil : u_at (hs_img h now Hb) 420 4 = u_at Hb 420 4)
  by (unfold u_at; rewrite a1_img_hb by (assumption || lia); reflexivity).
assert (Uop : u_at (hs_img h now Hb) 424 8 = u_at Hb 424 8)
  by (unfold u_at; rewrite a1_img_hb by (assumption || lia); reflexivity).
assert (Un : u_at (hs_img h now Hb) 384 4 = n_of (hs_table Hb now)).
{ transitivity (u_at (hs_table Hb now) 384 4); [unfold u_at; rewrite a1_img_tab by (assumption || lia); reflexivity|].
  unfold n_of, s32_at in T1 |- *. apply a1_u32_small; [lia | rewrite LT; lia | lia]. }
assert (V420 : val_mem SEGS (mrestrict (w_H Wc) memc) (h + 420) 4 (u_at Hb 420 4)).
{ rewrite <- Usil. apply hs_val_mem_of_garr8; [exact HG | lia | rewrite LI; lia]. }
assert (V424 : val_mem SEGS (mrestrict (w_H Wc) memc) (h + 424) 8 (u_at Hb 424 8)).
{ rewrite <- Uop. apply hs_val_mem_of_garr8; [exact HG | lia | rewrite LI; lia]. }
assert (V384 : val_mem SEGS (mrestrict (w_H Wc) memc) (h + 384) 4 (n_of (hs_table Hb now))).
{ rewrite <- Un. apply hs_val_mem_of_garr8; [exact HG | lia | rewrite LI; lia]. }
pose proof (a1_u_range Hb 420 4) as Rsil. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Rsil.
pose proof (a1_u_range Hb 424 8) as Rop. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rop.
assert (Hspc : spZ regsc = sp0 - 112) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
destruct (a1_entry 0x782c Wc lyc Sc regsc memc mdc (sp0 - 112) h now hb hn (u_at Hb 420 4) (u_at Hb 424 8)
  (n_of (hs_table Hb now)) HAR Hin Hlo Hhi Hh8 ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity) ltac:(lia)
  ltac:(intros a Ha; apply HpJ; lia) Rnow Rsil Rop ltac:(lia) Hspc R9 R18 R19 R23 R24 V420 V424 V384) as [HS SHOK].
set (E := a1_E regsc (u_at Hb 420 4) (u_at Hb 424 8) (n_of (hs_table Hb now))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold a1_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regsc [Z_to_bv 64 SB; Z_to_bv 64 (u_at Hb 420 4);
  Z_to_bv 64 (u_at Hb 424 8); Z_to_bv 64 (n_of (hs_table Hb now))]) k)
  by (intros k Hk; subst E; unfold a1_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regsc 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsc 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regsc 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl)).
assert (E9 : ew E 9 = getr regsc 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 9 9%bv eq_refl)).
assert (E18 : ew E 18 = Z_to_bv 64 now)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = getr regsc 19) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (u_at Hb 420 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (u_at Hb 424 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (n_of (hs_table Hb now)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; exact Hspc).
clearbody E. clear EL.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 <= a < sp0 - 104) ->
  aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
pose proof (a1_verdict h Hb now Hpin Hst Hdgl) as HV.
unfold cfg_at. change (w64 (BASE + 0x782c)) with (Z_to_bv 64 (BASE + 0x782c)).
paj_run_tok RUN HS HJ SHOK Bspan. { a1_awr Usp. }
a1_kept HFr Usp HK sp0.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, (a1_sext_eq0 E 33 (u_at Hb 420 4) E33 Rsil) in Hc.
  change (bv_swrap 32 (u_at Hb 420 4)) with (s32_at Hb 420) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hsil.
  rewrite Hsil, Z.eqb_refl in HV. cbn [negb] in HV.
  paj_run_tok RUN HS HJ SHOK Bspan. { a1_awr Usp. }
  a1_kept HFr Usp HK sp0.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ltu_U, (a1_U_sub E (SOff 18 0) (SOff 34 0) now (u_at Hb 424 8) (U_atom E 18 now E18 Rnow)
      (U_atom E 34 (u_at Hb 424 8) E34 Rop)), U_lit in Hc by lia.
    rename Hc into Hwin. rewrite Hwin in HV.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x795c. { a1_awr Usp. }
    a1_kept HFr Usp HK sp0.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (23%bv : bv 5) Q23.
    pmkst HS.
    apply (a1_fin fx fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc memc lyc Sc _ _ _ 0x795c 0 HPRE HJ HFk HFc);
    [ right; split; reflexivity | rewrite Q2, E2; exact R2 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
    | rewrite Q8, E8; exact R8 | rewrite Q23, E32; reflexivity
    | intros a Ha H1; apply HK; [exact Ha | rewrite WS in H1; lia] | exact HFR | exact Hh0 | exact Hh8 | exact Hin
    | exact Hlo | exact Hhi | exact HOK | exact LT | exact LA | exact HG | symmetry; exact HV | exact HOKH
    | apply Permutation_refl | exact HPerm ].
  + rewrite branch_ltu_U, (a1_U_sub E (SOff 18 0) (SOff 34 0) now (u_at Hb 424 8) (U_atom E 18 now E18 Rnow)
      (U_atom E 34 (u_at Hb 424 8) E34 Rop)), U_lit in Hc by lia.
    rename Hc into Hwin. rewrite Hwin in HV.
    paj_run_tok RUN HS HJ SHOK Bspan. { a1_awr Usp. }
    a1_kept HFr Usp HK sp0.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rewrite (a1_bge E (SLit 0) (SOff 35 0) 0 (n_of (hs_table Hb now)) (U_lit E 0 ltac:(lia))
        (U_atom E 35 _ E35 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
      apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hn0.
      assert (BP : box_present h (hs_table Hb now) now = false)
        by (unfold box_present, hs_idx; replace (n_of (hs_table Hb now)) with 0 by lia; reflexivity).
      rewrite BP in HV.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x795c. { a1_awr Usp. }
      a1_kept HFr Usp HK sp0.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (8%bv : bv 5) Q8. prreg HS (23%bv : bv 5) Q23.
      pmkst HS.
      apply (a1_fin fx fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc memc lyc Sc _ _ _ 0x795c 0 HPRE HJ HFk HFc);
      [ right; split; reflexivity | rewrite Q2, E2; exact R2 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
      | rewrite Q8, E8; exact R8 | rewrite Q23, E32; reflexivity
      | intros a Ha H1; apply HK; [exact Ha | rewrite WS in H1; lia] | exact HFR | exact Hh0 | exact Hh8 | exact Hin
      | exact Hlo | exact Hhi | exact HOK | exact LT | exact LA | exact HG | symmetry; exact HV | exact HOKH
      | apply Permutation_refl | exact HPerm ].
    * rewrite (a1_bge E (SLit 0) (SOff 35 0) 0 (n_of (hs_table Hb now)) (U_lit E 0 ltac:(lia))
        (U_atom E 35 _ E35 ltac:(lia)) ltac:(lia) ltac:(lia)) in Hc.
      apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hn0.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x78cc. { a1_awr Usp. }
      a1_kept HFr Usp HK sp0.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
      prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. a1_rreg HS (24%bv : bv 5) Q24.
      prreg HS (25%bv : bv 5) Q25. a1_rreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      pose proof (a1_mem_kept Wc memc _ sp0 HK ltac:(lia) ltac:(lia) HRO HRA HRT HD6 HD3)
        as (HRO' & HRA' & HRT' & HD6' & HD3').
      assert (HGT : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms)) h
        (map (fun b : byte => bv_unsigned b) (hs_table Hb now))).
      { pose proof HG as HG2. unfold hs_img in HG2. rewrite map_app in HG2.
        apply (garr8_aview_kept SEGS (w_H Wc) (w_H Wc) memc (ms_mem ms)).
        - intros a Ha. rewrite length_map, LT in Ha. apply HK; lia.
        - exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) HG2)). }
      pmkst HS.
      apply (hs_loop2 (treac_hunt_step_post fq0 regs ly S W mem md h now Hb) ly lyc S Sc W Wc mem (ms_mem ms) md _
        (ms_regs ms) sp0 h now hb hn 0 (hs_table Hb now) HJ HRO' HRA' HRT' HD6' HD3' Hin Hlo Hhi Hh8 LT HTOK HGT Rnow
        ltac:(lia) ltac:(intros j Hj; lia)).
      -- unfold spZ at 1. rewrite Q2. exact Usp.
      -- rewrite Q3, E3, R3. exact Hgp.
      -- rewrite Q4, E4, R4. exact Htp.
      -- rewrite Q8, E8. exact R8.
      -- rewrite Q9, E9, R9. f_equal. lia.
      -- rewrite Q18, E18. reflexivity.
      -- rewrite Q19, E19. exact R19.
      -- rewrite Q20, E9, R9. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
      -- rewrite Q21. reflexivity.
      -- rewrite Q22. reflexivity.
      -- rewrite Q23, E32. reflexivity.
      -- rewrite Q24, denot_lit_U, (proj2 (a1_U_sh E 19 (h + 384) 0 (eq_trans E19 R19) E32 ltac:(lia) ltac:(lia))).
         unfold w64. f_equal. rewrite Z.add_0_r. unfold SB, SHADOW_OFF. lia.
      -- rewrite Q25. reflexivity.
      -- rewrite Q26, denot_lit_U, (proj1 (a1_U_sh E 9 h 40 (eq_trans E9 R9) E32 ltac:(lia) ltac:(lia))).
         unfold w64. f_equal. replace (h + 48 * 0 + 40) with (h + 40) by lia. reflexivity.
      -- rewrite Q27. reflexivity.
      -- intros fq' lyd Sd Wd memd mdd regsd v Hf Hcs HJd Hv [HWd HKd] HPd R2d R3d R4d R8d R23d R10d. subst Wd.
         apply (a1_fin fq' fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc memc lyd Sd memd mdd regsd 0x7664 v HPRE HJd
           (reac_hunt_step.hs_freg_trans _ _ _ HFk Hf) (hs_csr_trans _ _ _ HFc Hcs));
         [ left; split; [reflexivity | exact R10d] | exact R2d | rewrite R3d; symmetry; exact Hgp
         | rewrite R4d; symmetry; exact Htp | exact R8d | exact R23d
         | intros a Ha H1; rewrite (HKd a Ha ltac:(lia)); apply HK; [exact Ha | lia]
         | exact HFR | exact Hh0 | exact Hh8 | exact Hin | exact Hlo | exact Hhi | exact HOK | exact LT | exact LA
         | exact HG | rewrite Hv; symmetry; exact HV | exact HOKH | exact HPd | exact HPerm ].
- rewrite branch_eq_U, (a1_sext_eq0 E 33 (u_at Hb 420 4) E33 Rsil) in Hc.
  change (bv_swrap 32 (u_at Hb 420 4)) with (s32_at Hb 420) in Hc. rename Hc into Hsil.
  rewrite Hsil in HV. cbn [negb] in HV.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7664. { a1_awr Usp. }
  a1_kept HFr Usp HK sp0.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (23%bv : bv 5) Q23.
  pmkst HS.
  apply (a1_fin fx fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc memc lyc Sc _ _ _ 0x7664 1 HPRE HJ HFk HFc);
  [ left; split; [reflexivity | rewrite Q10; reflexivity] | rewrite Q2, E2; exact R2 | rewrite Q3, E3; exact R3
  | rewrite Q4, E4; exact R4 | rewrite Q8, E8; exact R8 | rewrite Q23, E32; reflexivity
  | intros a Ha H1; apply HK; [exact Ha | rewrite WS in H1; lia] | exact HFR | exact Hh0 | exact Hh8 | exact Hin
  | exact Hlo | exact Hhi | exact HOK | exact LT | exact LA | exact HG | symmetry; exact HV | exact HOKH
  | apply Permutation_refl | exact HPerm ].
Qed.
End w2.
Section w4. Context {fx : YK11.FPState}.
Lemma u1_bge : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. unfold U in Ha, Hb. cbn [branch_taken]. unfold bv_lts, bv_signed. rewrite Ha, Hb.
assert (Hs : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z).
{ intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
rewrite !Hs by lia. reflexivity.
Qed.
Ltac u1_awr Usp WS :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply awr_ok_cons_gen with (n := 2%nat);
  [ reflexivity | exact Usp | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite WS; lia
  | apply awr_ok_nil ].
Definition u1_E (regs : bvmap 5 word) (T : list byte) : env := Eimg (Ereg regs [Z_to_bv 64 (n_of T)]).
Definition u1_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 32 0))];
   YP09.mkRegion (Some 2%nat) 0 8 0 8 []].
Definition u1_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, PTR 3); (23%nat, mkAF SB SB 0); (32%nat, mkAF 0 8 0)] [] [].
Definition u1_ss (pc : Z) : sstate := mkSS pc sr_atoms u1_regions None u1_facts.
Definition u1_SH : list shent := [mkSHE 9 384 392].
Definition u1_Bx : sv := SOff 23 0.
Lemma u1_u32_small : forall (A : list byte) (k : Z), 0 <= k -> (Z.to_nat k + 4 <= length A)%nat ->
0 <= bv_swrap 32 (u_at A k 4) -> u_at A k 4 = bv_swrap 32 (u_at A k 4).
Proof.
intros A k Hk Hn H0.
assert (LS : length (sub A k 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (PropExec.bytes_le_to_Z_bound (sub A k 4)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub A k 4)) as Hb0.
unfold u_at in *. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *.
change (bv_modulus 32) with (2 ^ 32) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma u1_entry : forall ly S W mem md lyc Sc Wc (regsc regs : bvmap 5 word) memc mdc (h hb hn : Z) (T : list byte) pc,
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memc mdc 0 ->
  getr regsc 2 = w64 (spZ regs - 112) -> getr regsc 9 = w64 h -> getr regsc 23 = w64 SHADOW_OFF ->
  0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  length T = 400%nat -> 0 <= n_of T <= 8 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) T) ->
  st_ok_pi SEGS VAL (u1_E regsc T) (u1_ss pc)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS u1_Bx u1_SH (u1_E regsc T) (mrestrict (w_H Wc) memc).
Proof.
intros ly S W mem md lyc Sc Wc regsc regs memc mdc h hb hn T pc HJ R2 R9 R23 Hh0 Hh8 Hin Hlo Hhi LT Hn HG.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
set (sp0 := spZ regs) in *.
assert (Hsp0 : 0 <= sp0 < 2 ^ 64) by (subst sp0; unfold spZ; apply bv_unsigned_in_range).
rewrite restrict_mkst_fx.
set (E := u1_E regsc T).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsc [Z_to_bv 64 (n_of T)]) n)
  by (intros n Hn'; subst E; unfold u1_E; apply Eimg_low; exact Hn').
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 (n_of T)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Uh : bv_unsigned (ew E 9) = h) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = n_of T) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Un : u_at T 384 4 = n_of T) by (unfold n_of, s32_at in *; apply u1_u32_small; lia).
split.
- unfold u1_ss, u1_regions. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Uh. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ h 384 4 (SOff 32 0) (n_of T));
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite <- Un. apply hs_val_mem_of_garr8; [exact HG | lia | rewrite LT; cbn; lia].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uh, Usp.
    split; [split; [lia | exact I] | split; [exact I | exact I]].
  + split; [|split; [exact I | exact I]].
    cbn [u1_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uh, U23, U32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hsh H47 Hceil Hbceil Hb4096 Hlo Hhi Hh0 Hh8 Hal C1 C3 WS Hstk0 Hrq0 Hrq1 Hn.
    clear. unfold SB, SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end;
    first [exact I | lia | rewrite Zminus_mod, Hal; reflexivity].
- unfold sh_ok, u1_SH. constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E u1_Bx 9 (h + 384) 8 h 384 392).
  + eapply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc hb hn (h + 384) 8 HAR Hin); lia.
  + unfold U, u1_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U23.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Uh.
  + lia.
  + lia.
  + intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
    unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma u1_ro_low : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
- apply pa_segs_low. apply pa_relro_img. exact Hr.
Qed.
Lemma u1_hi_near : forall kk (rd : bv 5) j, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  exists s, - 2 ^ 31 <= s < 2 ^ 31 /\ VAL (A_HI j) = (BASE + kk + s) mod 2 ^ 64 /\ 0 <= BASE + kk < kLowMemEnd.
Proof.
intros kk rd j Hk40 Hk. pose proof pa_B_ok as HB.
rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert kk _ Hk) as [Hc [Hk0 Hk4]].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + kk)) as [wz|] eqn:Hf; [|discriminate Hc].
assert (Himg : 0 <= BASE + kk < kLowMemEnd).
{ pose proof (pa_tbl_ok _ _ Hf) as Hfw.
  unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
  unfold code_read in Hfw.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
  destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
  assert (HI : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + kk)))).
  { exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
  pose proof (pa_segs_low _ HI) as HR.
  rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
  rewrite Z.mod_small in HR by lia. lia. }
destruct (decode_any (Z_to_bv 32 wz)) as [[ins isz]|]; [|discriminate Hc].
apply andb_prop in Hc as [_ Hc]. destruct ins; try (cbn in Hc; discriminate Hc).
apply andb_prop in Hc as [_ Hc]. apply Z.eqb_eq in Hc. unfold auipc_val, zcanon, M64 in Hc.
exists (bv_signed (bv_concat 32 imm (Z_to_bv 12 0))).
pose proof (bv_signed_in_range 32 (bv_concat 32 imm (Z_to_bv 12 0)) ltac:(discriminate)) as Hr.
change (bv_half_modulus 32) with (2 ^ 31) in Hr.
split; [lia|]. split; [rewrite <- Hc; reflexivity | exact Himg].
Qed.
Lemma u1_hi_win : forall kk (rd : bv 5) j c x lo hi, 0 <= kk < 2 ^ 40 -> plookup pl_tpi kk = Some (PHi rd j) ->
  -4096 <= c <= 4096 -> 0 <= x < 8 -> alloc_ceiling <= lo -> hi <= 2 ^ 47 ->
  ~ (lo <= (VAL (A_HI j) + c + x) mod 2 ^ 64 < hi).
Proof.
intros kk rd j c x lo hi Hk40 Hk Hc Hx Hlo Hhi.
destruct (u1_hi_near kk rd j Hk40 Hk) as (s & Hs & Hv & Hb).
pose proof (asan_consts) as (C1 & _ & _ & _ & C5).
rewrite Hv. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by lia.
revert Hs Hb Hc Hx Hlo Hhi C1 C5. clear. intros. Z.div_mod_to_equations. lia.
Qed.
Lemma u1_U_sh : forall E (n k : nat) v c, ew E n = Z_to_bv 64 v -> ew E k = Z_to_bv 64 SB -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ 50 ->
  U E (SAlu ALU_ADD (SOff k 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = SB + (v + c) / 8 /\
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff k 0)) = (v + c) / 8 + SB.
Proof.
intros E n k v c Hn Hk Hv Hc. rewrite !U_SAlu, !U_SOff, !U_SLit, Hn, Hk. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SB; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite (zcanon_id (v + c)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 50) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id (SB + 0)) by (unfold M64, SB; lia).
rewrite Z.add_0_r. split; apply zcanon_id; unfold M64, SB; lia.
Qed.
Lemma u1_nth_fs : forall (L : list Z) (k n j : nat), (j < n)%nat -> nth j (firstn n (skipn k L)) 0 = nth (k + j) L 0.
Proof.
intros L k n j Hj. rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn; f_equal; lia.
Qed.
Lemma u1_img_parts : forall m h now Hb, length (hs_table Hb now) = 400%nat -> length Hb = 480%nat ->
  garr8 SEGS m h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
  garr8 SEGS m h (map (fun b : byte => bv_unsigned b) (hs_table Hb now)) /\
  garr8 SEGS m (h + 412) (map (fun b : byte => bv_unsigned b) (sub Hb 412 6)).
Proof.
intros m h now Hb LT LH HG. unfold hs_img in HG. rewrite !map_app in HG.
apply (garr8_app SEGS) in HG. destruct HG as [HG1 HG2]. split; [exact HG1|].
apply (garr8_app SEGS) in HG2. destruct HG2 as [HG2 _].
rewrite length_map, LT in HG2. rewrite hs_map_sub in HG2 |- *.
change (Z.to_nat 400) with 400%nat in HG2. change (Z.to_nat 412) with 412%nat.
intros j Hj. rewrite length_firstn, length_skipn, length_map, LH in Hj.
destruct (HG2 (12 + j)%nat) as [HV HR]; [rewrite length_firstn, length_skipn, length_map, LH; lia|].
rewrite u1_nth_fs in HV, HR by lia. rewrite u1_nth_fs by lia.
replace (400 + (12 + j))%nat with (412 + j)%nat in HV, HR by lia.
replace (h + Z.of_nat 400 + Z.of_nat (12 + j)) with (h + 412 + Z.of_nat j) in HV by lia.
split; assumption.
Qed.
Definition u1_inv (W : world SEGS) (m : word -> option byte) (regs : bvmap 5 word) (h now : Z) (Hb : list byte) : Prop :=
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) /\
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
  garr8 SEGS (mrestrict (w_H W) m) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_HI 97) + -1832) 8 D6000 /\
  val_mem SEGS (mrestrict (w_H W) m) (VAL (A_HI 96) + -1628) 8 D3837 /\
  hs_frame regs (mrestrict (w_H W) m) (spZ regs) /\
  garr8 SEGS (mrestrict (w_H W) m) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)).
Lemma u1_aview_mod : forall H (m : word -> option byte) a, aview SEGS H m (a mod 2 ^ 64) = aview SEGS H m a.
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u1_inv_kept : forall W (m m' : word -> option byte) regs h now Hb lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  alloc_ceiling <= lo -> lo <= hi -> hi <= spZ regs - 104 -> spZ regs <= 2 ^ 47 -> 0 <= h ->
  h + 480 <= alloc_ceiling -> length (hs_img h now Hb) = 480%nat ->
  u1_inv W m regs h now Hb -> u1_inv W m' regs h now Hb.
Proof.
intros W m m' regs h now Hb lo hi HK Hlo Hlh Hhi Hsp H0 Hh LI (H1 & H2 & H3 & H4 & H5 & H6 & H7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HKx : forall x, ~ (lo <= x mod 2 ^ 64 < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros x Hx. rewrite <- (u1_aview_mod (w_H W) m' x), <- (u1_aview_mod (w_H W) m x).
  apply HK; [apply Z.mod_pos_bound; lia | exact Hx]. }
assert (AK : forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros x Hx. apply HK; lia. }
pose proof (pa_obj_img 65 ltac:(unfold disco_nobj; lia)) as H65.
assert (HimgL : 0 <= IMG_LO /\ IMG_TOP <= kLowMemEnd) by (unfold IMG_LO, IMG_TOP, kLowMemEnd; lia).
assert (LR : length RATES = 12%nat) by reflexivity.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros a Hro Ho He. pose proof (u1_ro_low a Hro) as Ha. rewrite AK by lia. exact (H1 a Hro Ho He).
- intros x Hx. destruct (H2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite AK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
  revert Hx H65 HimgL C1 C5. clear. intros. Z.div_mod_to_equations. lia.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) m m'); [|exact H3].
  intros a Ha. rewrite length_map, LR in Ha. apply AK. lia.
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact H4].
  intros x Hx. apply HKx.
  replace x with (VAL (A_HI 97) + -1832 + (x - (VAL (A_HI 97) + -1832))) by lia.
  apply (u1_hi_win 31476 11%bv 97 (-1832) (x - (VAL (A_HI 97) + -1832)));
  [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
- apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) m m'); [|exact H5].
  intros x Hx. apply HKx.
  replace x with (VAL (A_HI 96) + -1628 + (x - (VAL (A_HI 96) + -1628))) by lia.
  apply (u1_hi_win 31472 10%bv 96 (-1628) (x - (VAL (A_HI 96) + -1628)));
  [lia | vm_compute; reflexivity | lia | change (Z.of_nat 8) with 8 in Hx; lia | lia | lia].
- apply (hs_frame_kept regs (w_H W) (w_H W) m m'); [|exact H6].
  intros a Ha. apply HK; lia.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) m m'); [|exact H7].
  intros a Ha. rewrite length_map, LI in Ha. apply AK. lia.
Qed.
Lemma u1_frame_kept : forall E rs H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF HW a Ha Hn. apply (aview_eq_of SEGS). apply HF.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hw. apply Hn. exact (HW a Hw).
Qed.
Ltac u1_wr Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha); cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp in Ha; revert Ha; clear; intros; lia|]);
  destruct Hr.
Ltac u1_inv_step INV Usp A1w A2w A3 A4 A5 LIMG :=
  lazymatch type of INV with u1_inv ?W0 ?m0 ?rg ?h0 ?n0 ?H0 =>
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ m0) (mrestrict _ ?m1) |- _ =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let Hn := fresh "INV" in
    pose proof (u1_inv_kept W0 m0 m1 rg h0 n0 H0 _ _
       (u1_frame_kept E0 rs' (w_H W0) m0 m1 (spZ rg - 112) (spZ rg - 104) HFr ltac:(u1_wr Usp))
       A1w A2w (Z.le_refl _) A3 A4 A5 LIMG INV) as Hn;
    clear HFr INV; rename Hn into INV
  end end.
Ltac u1_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Lemma hs_unp_n : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte)
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc,
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memc mdc 0 ->
  freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 96) + -1628) 8 D3837 ->
  getr regsc 2 = w64 (spZ regs - 112) -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 8 = w64 (h + 440) -> getr regsc 9 = w64 h -> getr regsc 18 = w64 now ->
  getr regsc 20 = w64 (h + 412) -> getr regsc 23 = w64 SHADOW_OFF ->
  hs_frame regs (mrestrict (w_H Wc) memc) (spZ regs) ->
  0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 <= now < 2 ^ 64 ->
  hunt_ok Hb -> length (hs_table Hb now) = 400%nat -> table_ok (hs_table Hb now) -> length (hs_arb h Hb now) = 32%nat ->
  garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
  s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 <> 2 ->
  hunt_ok (hs_hunt h Hb now) ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  SRr SEGS Wc (cfg_at (fx := fx) SEGS (BASE + 0x7714) regsc memc mdc) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc regsc memc mdc HPRE HJ HFk HFc HRO HRA HRT H60 H38
  R2 R3 R4 R8 R9 R18 R20 R23 HFR Hh0 Hh8 Hin Hlo Hhi Rnow HOK LT TOK LA HG H432 Hst HOKH HPerm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof HOK as (LHb & _).
pose proof TOK as (T1 & _). unfold tbl_T1 in T1.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
assert (Hsp0 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
assert (A1 : alloc_ceiling <= spZ regs - REAC_HUNT_STEP_STK) by (revert Hceil Hslo; clear; intros; lia).
assert (A1w : alloc_ceiling <= spZ regs - 112) by (revert A1 WS; clear; intros; lia).
assert (A2w : spZ regs - 112 <= spZ regs - 104) by (clear; lia).
assert (A2l : spZ regs - REAC_HUNT_STEP_STK <= spZ regs - 112) by (revert WS; clear; intros; lia).
assert (A3 : spZ regs <= 2 ^ 47) by (revert Hsh H47; clear; intros; lia).
assert (A4 : 0 <= h) by (revert Hh0; clear; intros; lia).
assert (A5 : h + 480 <= alloc_ceiling) by (revert Hhi Hbceil; clear; intros; lia).
assert (Bh : 0 <= h + 480 < 2 ^ 47) by (revert A4 A5 C1; clear; intros; lia).
assert (LIMG : length (hs_img h now Hb) = 480%nat).
{ unfold hs_img. rewrite !length_app, LT, LA. unfold sub. rewrite !length_firstn, !length_skipn, LHb. reflexivity. }
assert (LU : length (sub Hb 412 6) = 6%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
assert (INV : u1_inv Wc memc regs h now Hb) by exact (conj HRO (conj HRA (conj HRT (conj H60 (conj H38 (conj HFR HG)))))).
clear HRO HRA HRT H60 H38 HFR.
assert (HGT : garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) (hs_table Hb now)))
  by exact (proj1 (u1_img_parts _ h now Hb LT LHb HG)).
destruct (u1_entry ly S W mem md lyc Sc Wc regsc regs memc mdc h hb hn (hs_table Hb now) 0x7714 HJ R2 R9 R23
  Hh0 Hh8 Hin Hlo Hhi LT T1 HGT) as [HS SHOK].
clear HG HGT.
set (E := u1_E regsc (hs_table Hb now)) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold u1_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsc [Z_to_bv 64 (n_of (hs_table Hb now))]) n)
  by (intros n Hn'; subst E; unfold u1_E; apply Eimg_low; exact Hn').
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 112))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regsc 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 (h + 440))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 h)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 now)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 (h + 412))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl); exact R20).
assert (E23 : ew E 23 = Z_to_bv 64 SB)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew E 32 = Z_to_bv 64 (n_of (hs_table Hb now)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
clear EL.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = h) by (rewrite E9; apply unsigned_lit_small; lia).
pose proof (paj_run (fx := fx) B LAWS) as RUN. pose proof (paj_run_to (fx := fx) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0x7714)) with (Z_to_bv 64 (BASE + 0x7714)).
paj_run_tok RUN HS HJ SHOK Bspan. { u1_awr Usp WS. }
u1_inv_step INV Usp A1w A2w A3 A4 A5 LIMG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (u1_bge E _ _ 0 (n_of (hs_table Hb now)) (U_lit E 0 ltac:(lia)) (U_atom E 32 _ E32 ltac:(lia))) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x782c. { u1_awr Usp WS. }
  u1_inv_step INV Usp A1w A2w A3 A4 A5 LIMG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msf end.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (23%bv : bv 5) N23.
  u1_rreg HS (24%bv : bv 5) N24.
  pmkst HS.
  destruct INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  assert (Q2 : getr (ms_regs msf) 2 = w64 (spZ regs - 112)) by (rewrite N2; exact E2).
  assert (Q3 : getr (ms_regs msf) 3 = getr regs 3) by (rewrite N3, E3; exact R3).
  assert (Q4 : getr (ms_regs msf) 4 = getr regs 4) by (rewrite N4, E4; exact R4).
  assert (Q8 : getr (ms_regs msf) 8 = w64 (h + 440)) by (rewrite N8; exact E8).
  assert (Q9 : getr (ms_regs msf) 9 = w64 h) by (rewrite N9; exact E9).
  assert (Q18 : getr (ms_regs msf) 18 = w64 now) by (rewrite N18; exact E18).
  assert (Q19 : getr (ms_regs msf) 19 = w64 (h + 384)) by (rewrite N19, U9; reflexivity).
  assert (Q23 : getr (ms_regs msf) 23 = w64 SHADOW_OFF) by (rewrite N23; exact E23).
  assert (Q24 : getr (ms_regs msf) 24 = w64 (SHADOW_OFF + (h + 384) / 8)).
  { rewrite N24, denot_lit_U, (proj2 (u1_U_sh E 9 23 h 384 E9 E23 ltac:(lia) ltac:(lia))).
    unfold w64. rewrite SB_SHADOW_OFF, Z.add_comm. reflexivity. }
  assert (HDG : desk_geometry_live h (hs_table Hb now) (sub Hb 412 6) now = false)
    by (apply reac_hunt_step.hs_dgl_false; intros j Hj; exfalso; lia).
  clear N2 N3 N4 N8 N9 N18 N19 N23 N24.
  eapply (@hs_after1 fx fq0) with (ch := ch) (hb := hb) (hn := hn); eassumption.
- rewrite (u1_bge E _ _ 0 (n_of (hs_table Hb now)) (U_lit E 0 ltac:(lia)) (U_atom E 32 _ E32 ltac:(lia))) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x7760. { u1_awr Usp WS. }
  u1_inv_step INV Usp A1w A2w A3 A4 A5 LIMG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msf end.
  prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23. prreg HS (25%bv : bv 5) N25.
  prreg HS (26%bv : bv 5) N26.
  u1_rreg HS (24%bv : bv 5) N24. u1_rreg HS (27%bv : bv 5) N27.
  pmkst HS.
  pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
  destruct (u1_img_parts _ h now Hb LT LHb I7) as [IG1 IG2].
  apply (@hs_loop1 fx (treac_hunt_step_post fq0 regs ly S W mem md h now Hb) ly lyc S Sc W Wc mem (ms_mem msf) md _
    (ms_regs msf) (spZ regs) h now hb hn 0 (hs_table Hb now) (sub Hb 412 6) HJ I1 I2 I3 I4 I5 Hin Hlo Hhi Hh8 LT TOK
    IG1 LU IG2 Rnow).
  + lia.
  + intros j Hj. exfalso. lia.
  + unfold spZ at 1. rewrite N2, E2. apply unsigned_lit_small. lia.
  + rewrite N3, E3, R3. exact Hgp.
  + rewrite N4, E4, R4. exact Htp.
  + rewrite N8. exact E8.
  + rewrite N9. exact E9.
  + rewrite N18. exact E18.
  + rewrite N19, U9. reflexivity.
  + rewrite N20. exact E20.
  + rewrite N21, U9. unfold w64. f_equal. lia.
  + rewrite N22. rewrite ?U9, ?E9. unfold w64. f_equal. lia.
  + rewrite N23. exact E23.
  + rewrite N24, denot_lit_U, (proj2 (u1_U_sh E 9 23 h 384 E9 E23 ltac:(lia) ltac:(lia))).
    unfold w64. rewrite SB_SHADOW_OFF, Z.add_comm. reflexivity.
  + rewrite N25. reflexivity.
  + rewrite N26. reflexivity.
  + rewrite N27, denot_lit_U, (proj1 (u1_U_sh E 9 23 h 40 E9 E23 ltac:(lia) ltac:(lia))).
    unfold w64. rewrite SB_SHADOW_OFF. f_equal. f_equal. f_equal. lia.
  + intros fq' lyd Sd Wd memd mdd regsd Hf' Hc' HJd Hdgl [-> HKd] HPd R2' R3' R4' R8' R9' R18' R19' R23' R24'.
    pose proof (u1_inv_kept Wc (ms_mem msf) memd regs h now Hb _ _ HKd A1 A2l A2w A3 A4 A5 LIMG INV)
      as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    assert (Hf2 : freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fq')) by exact (reac_hunt_step.hs_freg_trans _ _ _ HFk Hf').
    assert (Hc2 : hs_csr fq0 fq') by exact (hs_csr_trans _ _ _ HFc Hc').
    assert (Hin2 : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HPd | exact Hin]).
    assert (HP2 : Permutation (ablocks B lyd Sd) (ablocks B ly S)) by (eapply Permutation_trans; [exact HPd | exact HPerm]).
    assert (Q2 : getr regsd 2 = w64 (spZ regs - 112)) by exact R2'.
    assert (Q3 : getr regsd 3 = getr regs 3) by (rewrite R3'; symmetry; exact Hgp).
    assert (Q4 : getr regsd 4 = getr regs 4) by (rewrite R4'; symmetry; exact Htp).
    assert (Q8 : getr regsd 8 = w64 (h + 440)) by exact R8'.
    assert (Q9 : getr regsd 9 = w64 h) by exact R9'.
    assert (Q18 : getr regsd 18 = w64 now) by exact R18'.
    assert (Q19 : getr regsd 19 = w64 (h + 384)) by exact R19'.
    assert (Q23 : getr regsd 23 = w64 SHADOW_OFF) by exact R23'.
    assert (Q24 : getr regsd 24 = w64 (SHADOW_OFF + (h + 384) / 8)) by exact R24'.
    clear R2' R3' R4' R8' R9' R18' R19' R23' R24' I1 I2 I3 I4 I5 I6 I7 IG1 IG2 Hin INV.
    eapply (@hs_after1 fq' fq0) with (ch := ch) (hb := hb) (hn := hn); eassumption.
  + intros fq' lyd Sd Wd memd mdd regsd Hf' Hc' HJd Hdgl [-> HKd] HPd R2' R3' R4' R8' R23'.
    pose proof (u1_inv_kept Wc (ms_mem msf) memd regs h now Hb _ _ HKd A1 A2l A2w A3 A4 A5 LIMG INV)
      as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    assert (Hf2 : freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fq')) by exact (reac_hunt_step.hs_freg_trans _ _ _ HFk Hf').
    assert (Hc2 : hs_csr fq0 fq') by exact (hs_csr_trans _ _ _ HFc Hc').
    assert (Hin2 : In (hb, hn) (ablocks B lyd Sd)) by (eapply Permutation_in; [apply Permutation_sym; exact HPd | exact Hin]).
    assert (HP2 : Permutation (ablocks B lyd Sd) (ablocks B ly S)) by (eapply Permutation_trans; [exact HPd | exact HPerm]).
    assert (Q3 : getr regsd 3 = getr regs 3) by (rewrite R3'; symmetry; exact Hgp).
    assert (Q4 : getr regsd 4 = getr regs 4) by (rewrite R4'; symmetry; exact Htp).
    assert (HV : hs_verdict h Hb now = 0).
    { unfold hs_verdict. rewrite H432, reac_hunt_step.hs_dm_unp, Hdgl.
      destruct (Z.eqb_spec (s32_at (hs_arb h Hb now) 0) 2) as [E'|_]; [exact (False_ind _ (Hst E')) | reflexivity]. }
    exact (@hs_epi fq' fq0 ly S W regs mem md ch h now hb hn Hb lyd Sd Wc regsd memd mdd 0x795c 0 HPRE HJd Hf2 Hc2
      (or_intror (conj eq_refl eq_refl)) R2' Q3 Q4 R8' R23' J6 Hh0 Hh8 Hin2 Hlo Hhi HOK LT LA J7 (eq_sym HV) HOKH HP2).
Qed.
End w4.
Definition t1_sr : list sv := sr_set sr_atoms 19 (SOff 9 444).
Definition t1_R : YP09.region := YP09.mkRegion (Some 9%nat) 432 472 0 0
[YP09.mkChunk 432 (CVal 4 (SOff 32 0)); YP09.mkChunk 436 (CVal 4 (SOff 33 0)); YP09.mkChunk 440 (CVal 4 (SOff 34 0));
YP09.mkChunk 444 (CVal 4 (SOff 35 0)); YP09.mkChunk 468 (CVal 4 (SOff 36 0))].
Definition t1_facts : facts := mkFacts [(9%nat, PTR 3); (23%nat, mkAF SB SB 0)] [] [].
Definition t1_ss (pc : Z) : sstate := mkSS pc t1_sr [t1_R] None t1_facts.
Definition t1_SH : list shent := [mkSHE 9 0 480].
Definition t1_Bx : sv := SOff 23 0.
Definition t1_E (regs : bvmap 5 word) (I : list byte) : env :=
Eimg (Ereg regs [Z_to_bv 64 (u_at I 432 4); Z_to_bv 64 (u_at I 436 4); Z_to_bv 64 (u_at I 440 4);
Z_to_bv 64 (u_at I 444 4); Z_to_bv 64 (u_at I 468 4)]).
Lemma t1_ewl : forall regs I (n : nat), (n < 32)%nat -> ew (t1_E regs I) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs I n Hn. unfold t1_E. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [Ereg ew].
replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity.
Qed.
Lemma t1_ewx : forall regs I,
ew (t1_E regs I) 32 = Z_to_bv 64 (u_at I 432 4) /\ ew (t1_E regs I) 33 = Z_to_bv 64 (u_at I 436 4) /\
ew (t1_E regs I) 34 = Z_to_bv 64 (u_at I 440 4) /\ ew (t1_E regs I) 35 = Z_to_bv 64 (u_at I 444 4) /\
ew (t1_E regs I) 36 = Z_to_bv 64 (u_at I 468 4).
Proof.
intros regs I. unfold t1_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1)|].
split; [exact (ew_Ereg_extra regs _ 2)|]. split; [exact (ew_Ereg_extra regs _ 3)|]. exact (ew_Ereg_extra regs _ 4).
Qed.
Lemma t1_uat : forall T o (n : nat), 0 <= u_at T o n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T o n. unfold u_at. pose proof (YK11.bytes_le_to_Z_bound (sub T o n)) as HB.
pose proof (YK11.bytes_le_to_Z_nonneg (sub T o n)) as HN.
assert (LS : (length (sub T o n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [lia|]. eapply Z.lt_le_trans; [exact HB|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma t1_awr : forall E (rs : smem) STK sp0 FP bl0 blc ly own,
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hw a (r & Hr & Ha). rewrite forallb_forall in Hw. specialize (Hw r Hr).
apply Z.leb_le in Hw. lia.
Qed.
Lemma t1_fr : forall (H : word -> bool) E (rs : smem) (m m' : word -> option byte),
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H E rs m m' Hw HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Hb). rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.
Definition t1_mf (regs : bvmap 5 word) (H : word -> bool) (m : word -> option byte) (h now : Z) (Hb : list byte) : Prop :=
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H m) /\
range_addressable (aview SEGS H m) SHADOW_OFF (VAL (A_OBJ 65)) 12 /\
garr8 SEGS (mrestrict H m) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
val_mem SEGS (mrestrict H m) (VAL (A_HI 97) + -1832) 8 D6000 /\
val_mem SEGS (mrestrict H m) (VAL (A_HI 96) + -1628) 8 D3837 /\
hs_frame regs (mrestrict H m) (spZ regs) /\
garr8 SEGS (mrestrict H m) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)).
Lemma t1_mf_kept : forall regs (H : word -> bool) (m m' : word -> option byte) h now Hb,
(forall a, aview SEGS H m' a = aview SEGS H m a) -> t1_mf regs H m h now Hb -> t1_mf regs H m' h now Hb.
Proof.
intros regs H m m' h now Hb K (HROD & HRR & HGR & HD60 & HD38 & HFR & HG).
split; [intros a Ha1 Ha2 Ha3; rewrite K; exact (HROD a Ha1 Ha2 Ha3)|].
split; [intros x Hx; destruct (HRR x Hx) as (s & Hs & Hok); exists s; split; [rewrite K; exact Hs | exact Hok]|].
split; [apply (garr8_aview_kept SEGS H H m m'); [intros a _; apply K | exact HGR]|].
split; [apply (val_mem_kept SEGS H H m m'); [intros k _; apply K | exact HD60]|].
split; [apply (val_mem_kept SEGS H H m m'); [intros k _; apply K | exact HD38]|].
split; [apply (hs_frame_kept regs H H m m'); [intros a _; apply K | exact HFR]|].
apply (garr8_aview_kept SEGS H H m m'); [intros a _; apply K | exact HG].
Qed.
Ltac t1_kept MF :=
let K := fresh "K" in
lazymatch goal with HFr : frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') |- _ =>
  let Hw := fresh "Hw" in
  assert (Hw : forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true) by (vm_compute; reflexivity);
  pose proof (t1_fr H E rs m m' Hw HFr) as K; clear HFr Hw end;
lazymatch goal with HF : frame_of _ _ _ _ |- _ => clear HF | _ => idtac end;
lazymatch goal with HG : mem_grows _ _ |- _ => clear HG | _ => idtac end;
repeat match goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => progress rewrite wvb_collapse in HJ end;
apply (t1_mf_kept _ _ _ _ _ _ _ K) in MF; clear K.
Lemma t1_u4 : forall T o, 0 <= u_at T o 4 < 2 ^ 32.
Proof. intros T o. exact (t1_uat T o 4). Qed.
Lemma t1_sw : forall u, 0 <= u < 2 ^ 32 -> - 2 ^ 31 <= bv_swrap 32 u < 2 ^ 31.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
pose proof (Z.mod_pos_bound (u + 2 ^ 31) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma t1_sext : forall v, 0 <= v < 2 ^ 32 -> sext 64 (bv_extract 0 32 (Z_to_bv 64 v)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros v Hv. rewrite (zext_low_sound true 32 v). unfold zext_low. apply Z_to_bv64_eq_mod.
unfold zcanon, M64. rewrite Zmod_mod. rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (cbn; lia). reflexivity.
Qed.
Lemma t1_eqk : forall s k, - 2 ^ 63 <= s < 2 ^ 63 -> 0 <= k < 2 ^ 63 -> (bv_unsigned (Z_to_bv 64 s) =? k) = (s =? k).
Proof.
intros s k Hs Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec s 0) as [Hn|Hp].
- replace (s mod 2 ^ 64) with (s + 2 ^ 64) by (apply (Z.mod_unique _ _ (-1)); lia).
  destruct (Z.eqb_spec (s + 2 ^ 64) k); destruct (Z.eqb_spec s k); try reflexivity; lia.
- rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma t1_Usx : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by lia. apply t1_sext. lia.
Qed.
Lemma t1_beq : forall E n u k, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit k)) = (bv_swrap 32 u =? k).
Proof.
intros E n u k Hn Hu Hk. rewrite branch_eq_U. unfold U at 1. rewrite (t1_Usx E n u Hn Hu). rewrite U_lit by lia.
pose proof (t1_sw u Hu). apply t1_eqk; lia.
Qed.
Lemma t1_bne : forall E n u k, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit k)) = negb (bv_swrap 32 u =? k).
Proof.
intros E n u k Hn Hu Hk. rewrite branch_ne_U. unfold U at 1. rewrite (t1_Usx E n u Hn Hu). rewrite U_lit by lia.
pose proof (t1_sw u Hu). f_equal. apply t1_eqk; lia.
Qed.
Lemma t1_sub_app_r : forall (L1 L2 : list byte) k n, (length L1 <= Z.to_nat k)%nat -> 0 <= k ->
sub (L1 ++ L2) k n = sub L2 (k - Z.of_nat (length L1)) n.
Proof.
intros L1 L2 k n Hl Hk. unfold sub. rewrite skipn_app. rewrite (skipn_all2 L1) by lia. cbn [app]. f_equal. f_equal. lia.
Qed.
Lemma t1_sub_app_l : forall (L1 L2 : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L1)%nat ->
sub (L1 ++ L2) k n = sub L1 k n.
Proof.
intros L1 L2 k n Hk Hl. unfold sub. rewrite skipn_app. replace (Z.to_nat k - length L1)%nat with 0%nat by lia.
cbn [skipn]. rewrite firstn_app. rewrite length_skipn. replace (n - (length L1 - Z.to_nat k))%nat with 0%nat by lia.
cbn [firstn]. apply app_nil_r.
Qed.
Lemma t1_img_lo : forall h now Hb k, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
400 <= k -> k + 4 <= 444 -> u_at (hs_img h now Hb) k 4 = u_at Hb k 4.
Proof.
intros h now Hb k LHb LT Hk1 Hk2. unfold u_at, hs_img. f_equal.
rewrite t1_sub_app_r by (rewrite ?LT; lia). rewrite LT.
assert (L44 : length (sub Hb 400 44) = 44%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
rewrite t1_sub_app_l by (rewrite ?L44; lia).
rewrite reac_hunt_step.hs_sub_sub by lia. f_equal. lia.
Qed.
Lemma t1_img_arb : forall h now Hb k, length Hb = 480%nat -> length (hs_table Hb now) = 400%nat ->
length (hs_arb h Hb now) = 32%nat -> 444 <= k -> k + 4 <= 476 ->
u_at (hs_img h now Hb) k 4 = u_at (hs_arb h Hb now) (k - 444) 4.
Proof.
intros h now Hb k LHb LT LA Hk1 Hk2. unfold u_at, hs_img. f_equal.
rewrite t1_sub_app_r by (rewrite ?LT; lia). rewrite LT.
assert (L44 : length (sub Hb 400 44) = 44%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
rewrite t1_sub_app_r by (rewrite ?L44; lia). rewrite L44.
rewrite t1_sub_app_l by (rewrite ?LA; lia). f_equal. lia.
Qed.
Lemma t1_seqzk : forall q m c, - 2 ^ 31 <= q < 2 ^ 31 -> - 3 <= m <= 0 -> 0 <= c <= 3 ->
alu64 ALU_ADD (alu64 ALU_SLTU (alu64 ALU_ADD (Z_to_bv 64 q) (Z_to_bv 64 m)) (Z_to_bv 64 1)) (Z_to_bv 64 c)
= Z_to_bv 64 (if q + m =? 0 then c + 1 else c).
Proof.
intros q m c Hq Hm Hc.
assert (A1 : alu64 ALU_ADD (Z_to_bv 64 q) (Z_to_bv 64 m) = Z_to_bv 64 (q + m)).
{ apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity. }
rewrite A1.
assert (A2 : alu64 ALU_SLTU (Z_to_bv 64 (q + m)) (Z_to_bv 64 1) = Z_to_bv 64 (if q + m =? 0 then 1 else 0)).
{ apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
  destruct (Z.eqb_spec (q + m) 0) as [E0|E0].
  - rewrite E0. reflexivity.
  - destruct (Z.ltb_spec ((q + m) mod 2 ^ 64) 1) as [L|L]; [|reflexivity].
    exfalso. destruct (Z.ltb_spec (q + m) 0).
    + replace ((q + m) mod 2 ^ 64) with (q + m + 2 ^ 64) in L by (apply (Z.mod_unique _ _ (-1)); lia). lia.
    + rewrite Z.mod_small in L by lia. lia. }
rewrite A2. destruct (q + m =? 0); rewrite alu_add_small by (unfold M64; lia); f_equal; lia.
Qed.
Lemma t1_vB : forall h Hb now, s32_at Hb 432 <> 0 ->
~ (s32_at Hb 436 = 0 /\ s32_at (hs_arb h Hb now) 0 = 2 /\ s32_at (hs_arb h Hb now) 24 = 2) ->
hs_verdict h Hb now = if s32_at Hb 436 + -1 =? 0 then 1 + 1 else 1.
Proof.
intros h Hb now HP HN. unfold hs_verdict. rewrite reac_hunt_step.hs_dm_pinned by exact HP.
set (q := s32_at Hb 436) in *. set (st := s32_at (hs_arb h Hb now) 0) in *. set (rv := s32_at (hs_arb h Hb now) 24) in *.
clearbody q st rv. clear - HN.
destruct (Z.eqb_spec q 0); destruct (Z.eqb_spec st 2); destruct (Z.eqb_spec rv 2); destruct (Z.eqb_spec q 1);
destruct (Z.eqb_spec (q + -1) 0); cbn [andb]; try reflexivity; lia.
Qed.
Lemma t1_vB2bi : forall h Hb now, s32_at Hb 432 <> 0 -> s32_at Hb 436 = 0 -> s32_at (hs_arb h Hb now) 0 = 2 ->
s32_at (hs_arb h Hb now) 24 = 2 -> hs_verdict h Hb now = 2.
Proof.
intros h Hb now HP HQ HS HR. unfold hs_verdict. rewrite reac_hunt_step.hs_dm_pinned by exact HP. rewrite HQ, HS, HR. reflexivity.
Qed.
Lemma t1_vA2a : forall h Hb now, s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 = 2 -> s32_at (hs_arb h Hb now) 24 <> 4 ->
hs_verdict h Hb now = if s32_at (hs_arb h Hb now) 24 + -3 =? 0 then 2 + 1 else 2.
Proof.
intros h Hb now HP HS HR. unfold hs_verdict. rewrite HP, reac_hunt_step.hs_dm_unp, HS, Z.eqb_refl.
set (rv := s32_at (hs_arb h Hb now) 24) in *. clearbody rv. clear - HR.
destruct (Z.eqb_spec rv 4); [lia|]. destruct (Z.eqb_spec rv 3); destruct (Z.eqb_spec (rv + -3) 0); try reflexivity; lia.
Qed.
Lemma t1_vA2b : forall h Hb now, s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 = 2 -> s32_at (hs_arb h Hb now) 24 = 4 ->
hs_verdict h Hb now = s32_at Hb 440.
Proof.
intros h Hb now HP HS HR. unfold hs_verdict. rewrite HP, reac_hunt_step.hs_dm_unp, HS, HR. reflexivity.
Qed.
Section w3. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (fx := fx) (PI := PI).
Lemma t1_entry : forall lyc Sc Wc (regsc : bvmap 5 word) memc mdc (h hb hn : Z) (Ib : list byte) pc,
AR SEGS B lyc Sc Wc memc mdc -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
0 < h -> h mod 8 = 0 ->
getr regsc 9 = w64 h -> getr regsc 19 = w64 (h + 444) -> getr regsc 23 = w64 SHADOW_OFF ->
length Ib = 480%nat -> garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) Ib) ->
st_ok_pi SEGS VAL (t1_E regsc Ib) (t1_ss pc) (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS t1_Bx t1_SH (t1_E regsc Ib) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc regsc memc mdc h hb hn Ib pc HAR Hin Hlo Hhi Hh0 Hh8 R9 R19 R23 LI HG.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
rewrite restrict_mkst_fx.
set (E := t1_E regsc Ib).
assert (E9 : ew E 9 = Z_to_bv 64 h) by (subst E; rewrite t1_ewl by lia; exact R9).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite t1_ewl by lia; exact R23).
destruct (t1_ewx regsc Ib) as (E32 & E33 & E34 & E35 & E36). fold E in E32, E33, E34, E35, E36.
assert (Uh : bv_unsigned (ew E 9) = h) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (VM : forall k, 0 <= k -> k + 4 <= 480 -> val_mem SEGS (mrestrict (w_H Wc) memc) (h + k) 4 (u_at Ib k 4)).
{ intros k Hk Hk4. apply hs_val_mem_of_garr8; [exact HG | lia | rewrite LI; lia]. }
split.
- unfold t1_ss. apply pa_entry_st_ok_full.
  + unfold t1_sr. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
    rewrite R19, denot_lit_U. unfold w64. f_equal. rewrite U_SOff. fold E. rewrite Uh. symmetry. apply zcanon_id. unfold M64. lia.
  + vm_compute. reflexivity.
  + unfold t1_R. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uh. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ h 432 4 (SOff 32 0) (u_at Ib 432 4));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (t1_uat Ib 432 4) | lia | apply VM; lia].
    * apply (chunk_ok_val SEGS E _ h 436 4 (SOff 33 0) (u_at Ib 436 4));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (t1_uat Ib 436 4) | lia | apply VM; lia].
    * apply (chunk_ok_val SEGS E _ h 440 4 (SOff 34 0) (u_at Ib 440 4));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (t1_uat Ib 440 4) | lia | apply VM; lia].
    * apply (chunk_ok_val SEGS E _ h 444 4 (SOff 35 0) (u_at Ib 444 4));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (t1_uat Ib 444 4) | lia | apply VM; lia].
    * apply (chunk_ok_val SEGS E _ h 468 4 (SOff 36 0) (u_at Ib 468 4));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact (t1_uat Ib 468 4) | lia | apply VM; lia].
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + split; [|split; [exact I | exact I]].
    cbn [t1_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Uh, U23. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hbceil Hb4096 Hlo Hhi Hh0 Hh8 C1 Hrq0 Hrq1.
    clear. unfold SB, SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, t1_SH. constructor; [|constructor].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E t1_Bx 9 h 480 h 0 480).
  + eapply (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc hb hn h 480 HAR Hin); lia.
  + unfold U, t1_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U23.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Uh.
  + lia.
  + lia.
  + intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
    unfold SHADOW_OFF in *. revert Hx Hbapp Hb4096 Hbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Ltac t1_run HS HJ SHOK MF := paj_run_tok RUN HS HJ SHOK Bspan; [apply t1_awr; vm_compute; reflexivity | t1_kept MF].
Ltac t1_runto HS HJ SHOK MF stop := paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; [apply t1_awr; vm_compute; reflexivity | t1_kept MF].
Definition t1_fix (fq0 : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md ch (h now hb hn : Z)
(Hb : list byte) lyc Sc : Prop :=
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch /\
freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) /\ hs_csr fq0 fx /\
0 < h /\ h mod 8 = 0 /\ In (hb, hn) (ablocks B lyc Sc) /\ hb <= h /\ h + 480 <= hb + req_size hn /\
0 <= now < 2 ^ 64 /\ hunt_ok Hb /\ length (hs_table Hb now) = 400%nat /\ table_ok (hs_table Hb now) /\
length (hs_arb h Hb now) = 32%nat /\ hunt_ok (hs_hunt h Hb now) /\ Permutation (ablocks B lyc Sc) (ablocks B ly S).
Lemma t1_epi_call : forall fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc Wc (regsd : bvmap 5 word) memd mdd,
t1_fix fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc ->
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memd mdd 0 ->
t1_mf regs (w_H Wc) memd h now Hb ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
getr regsd 8 = w64 (h + 440) -> getr regsd 23 = w64 SHADOW_OFF -> getr regsd 10 = w64 (hs_verdict h Hb now) ->
SRr SEGS Wc (cfg_at (fx := fx) SEGS (BASE + 0x7664) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc Wc regsd memd mdd FIX HJ MF R2 R3 R4 R8 R23 R10.
destruct FIX as (HPRE & HFk & HFc & Hh0 & Hh8 & Hin & Hlo & Hhi & Rnow & HOK & LT & TOK & LA & HOKH & HPerm).
destruct MF as (_ & _ & _ & _ & _ & HFR & HG).
exact (hs_epi fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc regsd memd mdd 0x7664 (hs_verdict h Hb now) HPRE HJ HFk HFc
(or_introl (conj eq_refl R10)) R2 R3 R4 R8 R23 HFR Hh0 Hh8 Hin Hlo Hhi HOK LT LA HG eq_refl HOKH HPerm).
Qed.
Lemma t1_unp_call : forall fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc Wc (regsd : bvmap 5 word) memd mdd,
t1_fix fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc ->
ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memd mdd 0 ->
t1_mf regs (w_H Wc) memd h now Hb ->
getr regsd 2 = w64 (spZ regs - 112) -> getr regsd 3 = getr regs 3 -> getr regsd 4 = getr regs 4 ->
getr regsd 8 = w64 (h + 440) -> getr regsd 9 = w64 h -> getr regsd 18 = w64 now ->
getr regsd 20 = w64 (h + 412) -> getr regsd 23 = w64 SHADOW_OFF ->
s32_at Hb 432 = 0 -> s32_at (hs_arb h Hb now) 0 <> 2 ->
SRr SEGS Wc (cfg_at (fx := fx) SEGS (BASE + 0x7714) regsd memd mdd) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc Wc regsd memd mdd FIX HJ MF R2 R3 R4 R8 R9 R18 R20 R23 HP0 HS2.
destruct FIX as (HPRE & HFk & HFc & Hh0 & Hh8 & Hin & Hlo & Hhi & Rnow & HOK & LT & TOK & LA & HOKH & HPerm).
destruct MF as (MROD & MRR & MGR & MD60 & MD38 & MFR & MG).
exact (hs_unp_n fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc regsd memd mdd HPRE HJ HFk HFc MROD MRR MGR MD60 MD38
R2 R3 R4 R8 R9 R18 R20 R23 MFR Hh0 Hh8 Hin Hlo Hhi Rnow HOK LT TOK LA MG HP0 HS2 HOKH HPerm).
Qed.
Ltac t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23 :=
let Q2 := fresh "Q2" in let Q3 := fresh "Q3" in let Q4 := fresh "Q4" in let Q8 := fresh "Q8" in
let Q10 := fresh "Q10" in let Q23 := fresh "Q23" in
t1_runto HS HJ SHOK MF 0x7664;
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8;
prreg HS (10%bv : bv 5) Q10; prreg HS (23%bv : bv 5) Q23; pmkst HS;
apply (t1_epi_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX HJ MF);
[ rewrite Q2, E2; exact R2 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4
| rewrite Q8; exact U8 | rewrite Q23, E23; exact R23 | rewrite Q10 ].
Lemma hs_tree : forall (fq0 : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte)
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc,
  afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
  ajournal SEGS B REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] lyc Sc Wc memc mdc 0 ->
  freg_kept (@YK11.fp_regs fq0) (@YK11.fp_regs fx) -> hs_csr fq0 fx ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (VAL (A_HI 96) + -1628) 8 D3837 ->
  getr regsc 2 = w64 (spZ regs - 112) -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  getr regsc 9 = w64 h -> getr regsc 18 = w64 now -> getr regsc 19 = w64 (h + 444) -> getr regsc 20 = w64 (h + 412) ->
  getr regsc 23 = w64 SHADOW_OFF ->
  hs_frame regs (mrestrict (w_H Wc) memc) (spZ regs) ->
  0 < h -> h mod 8 = 0 -> In (hb, hn) (ablocks B lyc Sc) -> hb <= h -> h + 480 <= hb + req_size hn ->
  0 <= now < 2 ^ 64 ->
  hunt_ok Hb -> length (hs_table Hb now) = 400%nat -> table_ok (hs_table Hb now) -> length (hs_arb h Hb now) = 32%nat ->
  garr8 SEGS (mrestrict (w_H Wc) memc) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb)) ->
  hunt_ok (hs_hunt h Hb now) ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  SRr SEGS Wc (cfg_at (fx := fx) SEGS (BASE + 0x75e0) regsc memc mdc) (treac_hunt_step_post fq0 regs ly S W mem md h now Hb).
Proof.
intros fq0 ly S W regs mem md ch h now hb hn Hb lyc Sc Wc regsc memc mdc HPRE HJ HFk HFc HROD HRR HGR HD60 HD38
R2 R3 R4 R9 R18 R19 R20 R23 HFR Hh0 Hh8 Hin Hlo Hhi Rnow HOK LT TOK LA HG HOKH HPerm.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HOK as (LHb & _ & _ & V0R).
assert (LI : length (hs_img h now Hb) = 480%nat).
{ unfold hs_img. rewrite !length_app, LT, LA. unfold sub. rewrite !length_firstn, !length_skipn, LHb. reflexivity. }
pose proof (proj1 HJ) as HAR.
assert (Hh64 : h + 480 < 2 ^ 47).
{ pose proof (asan_consts) as (C1 & _ & _ & _ & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ hb hn HAR Hin) as (_ & _ & Hbceil & _).
  revert C1 Hbceil Hhi. clear. intros. lia. }
destruct (t1_entry lyc Sc Wc regsc memc mdc h hb hn (hs_img h now Hb) 0x75e0 HAR Hin Hlo Hhi Hh0 Hh8 R9 R19 R23 LI HG) as [HS SHOK].
assert (MF : t1_mf regs (w_H Wc) memc h now Hb) by exact (conj HROD (conj HRR (conj HGR (conj HD60 (conj HD38 (conj HFR HG)))))).
assert (FIX : t1_fix fq0 regs ly S W mem md ch h now hb hn Hb lyc Sc)
by exact (conj HPRE (conj HFk (conj HFc (conj Hh0 (conj Hh8 (conj Hin (conj Hlo (conj Hhi (conj Rnow (conj HOK
(conj LT (conj TOK (conj LA (conj HOKH HPerm)))))))))))))).
clear HROD HRR HGR HD60 HD38 HFR HG.
destruct (t1_ewx regsc (hs_img h now Hb)) as (E32 & E33 & E34 & E35 & E36).
rewrite (t1_img_lo h now Hb 432 LHb LT) in E32 by lia.
rewrite (t1_img_lo h now Hb 436 LHb LT) in E33 by lia.
rewrite (t1_img_lo h now Hb 440 LHb LT) in E34 by lia.
rewrite (t1_img_arb h now Hb 444 LHb LT LA) in E35 by lia.
rewrite (t1_img_arb h now Hb 468 LHb LT LA) in E36 by lia.
assert (E2 : ew (t1_E regsc (hs_img h now Hb)) 2 = getr regsc 2) by (rewrite t1_ewl by lia; reflexivity).
assert (E3 : ew (t1_E regsc (hs_img h now Hb)) 3 = getr regsc 3) by (rewrite t1_ewl by lia; reflexivity).
assert (E4 : ew (t1_E regsc (hs_img h now Hb)) 4 = getr regsc 4) by (rewrite t1_ewl by lia; reflexivity).
assert (E9 : ew (t1_E regsc (hs_img h now Hb)) 9 = getr regsc 9) by (rewrite t1_ewl by lia; reflexivity).
assert (E18 : ew (t1_E regsc (hs_img h now Hb)) 18 = getr regsc 18) by (rewrite t1_ewl by lia; reflexivity).
assert (E20 : ew (t1_E regsc (hs_img h now Hb)) 20 = getr regsc 20) by (rewrite t1_ewl by lia; reflexivity).
assert (E23 : ew (t1_E regsc (hs_img h now Hb)) 23 = getr regsc 23) by (rewrite t1_ewl by lia; reflexivity).
set (E := t1_E regsc (hs_img h now Hb)) in HS, SHOK, E32, E33, E34, E35, E36, E2, E3, E4, E9, E18, E20, E23.
assert (U8 : Z_to_bv 64 (bv_unsigned (ew E 9) + 440) = w64 (h + 440)).
{ rewrite E9, R9. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold t1_E; apply Eimg_env).
unfold cfg_at. change (w64 (BASE + 0x75e0)) with (Z_to_bv 64 (BASE + 0x75e0)).
t1_run HS HJ SHOK MF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (t1_beq E 32 _ 0 E32 (t1_u4 _ _) ltac:(lia)) in Hc. change (bv_swrap 32 (u_at Hb 432 4)) with (s32_at Hb 432) in Hc.
  apply Z.eqb_eq in Hc. rename Hc into HP0.
  t1_run HS HJ SHOK MF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite (t1_bne E 35 _ 2 E35 (t1_u4 _ _) ltac:(lia)) in Hc.
    change (bv_swrap 32 (u_at (hs_arb h Hb now) (444 - 444) 4)) with (s32_at (hs_arb h Hb now) 0) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HS2.
    t1_runto HS HJ SHOK MF 0x7714.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23.
    pmkst HS.
    apply (t1_unp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIX HJ MF);
    [ rewrite Q2, E2; exact R2 | rewrite Q3, E3; exact R3 | rewrite Q4, E4; exact R4 | rewrite Q8; exact U8
    | rewrite Q9, E9; exact R9 | rewrite Q18, E18; exact R18 | rewrite Q20, E20; exact R20 | rewrite Q23, E23; exact R23
    | exact HP0 | exact HS2 ].
  + rewrite (t1_bne E 35 _ 2 E35 (t1_u4 _ _) ltac:(lia)) in Hc.
    change (bv_swrap 32 (u_at (hs_arb h Hb now) (444 - 444) 4)) with (s32_at (hs_arb h Hb now) 0) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HS2.
    t1_run HS HJ SHOK MF.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rewrite (t1_bne E 36 _ 4 E36 (t1_u4 _ _) ltac:(lia)) in Hc.
      change (bv_swrap 32 (u_at (hs_arb h Hb now) (468 - 444) 4)) with (s32_at (hs_arb h Hb now) 24) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HR4.
      t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
      rewrite E36, t1_sext by apply t1_u4.
      rewrite t1_seqzk by first [lia | apply t1_sw; apply t1_u4].
      rewrite (t1_vA2a h Hb now HP0 HS2 HR4). reflexivity.
    * rewrite (t1_bne E 36 _ 4 E36 (t1_u4 _ _) ltac:(lia)) in Hc.
      change (bv_swrap 32 (u_at (hs_arb h Hb now) (468 - 444) 4)) with (s32_at (hs_arb h Hb now) 24) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HR4.
      t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
      rewrite E34, t1_sext by apply t1_u4.
      rewrite (t1_vA2b h Hb now HP0 HS2 HR4). reflexivity.
- rewrite (t1_beq E 32 _ 0 E32 (t1_u4 _ _) ltac:(lia)) in Hc. change (bv_swrap 32 (u_at Hb 432 4)) with (s32_at Hb 432) in Hc.
  apply Z.eqb_neq in Hc. rename Hc into HP1.
  t1_run HS HJ SHOK MF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite (t1_bne E 33 _ 0 E33 (t1_u4 _ _) ltac:(lia)) in Hc. change (bv_swrap 32 (u_at Hb 436 4)) with (s32_at Hb 436) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HQ1.
    t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
    rewrite E33, t1_sext by apply t1_u4.
    rewrite t1_seqzk by first [lia | apply t1_sw; apply t1_u4].
    rewrite (t1_vB h Hb now HP1 ltac:(tauto)). reflexivity.
  + rewrite (t1_bne E 33 _ 0 E33 (t1_u4 _ _) ltac:(lia)) in Hc. change (bv_swrap 32 (u_at Hb 436 4)) with (s32_at Hb 436) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HQ0.
    t1_run HS HJ SHOK MF.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * rewrite (t1_bne E 35 _ 2 E35 (t1_u4 _ _) ltac:(lia)) in Hc.
      change (bv_swrap 32 (u_at (hs_arb h Hb now) (444 - 444) 4)) with (s32_at (hs_arb h Hb now) 0) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HS2.
      t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
      rewrite E33, t1_sext by apply t1_u4.
      rewrite t1_seqzk by first [lia | apply t1_sw; apply t1_u4].
      rewrite (t1_vB h Hb now HP1 ltac:(tauto)). reflexivity.
    * rewrite (t1_bne E 35 _ 2 E35 (t1_u4 _ _) ltac:(lia)) in Hc.
      change (bv_swrap 32 (u_at (hs_arb h Hb now) (444 - 444) 4)) with (s32_at (hs_arb h Hb now) 0) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HS2.
      t1_run HS HJ SHOK MF.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- rewrite (t1_beq E 36 _ 2 E36 (t1_u4 _ _) ltac:(lia)) in Hc.
         change (bv_swrap 32 (u_at (hs_arb h Hb now) (468 - 444) 4)) with (s32_at (hs_arb h Hb now) 24) in Hc.
         apply Z.eqb_eq in Hc. rename Hc into HR2.
         t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
         rewrite (t1_vB2bi h Hb now HP1 HQ0 HS2 HR2). reflexivity.
      -- rewrite (t1_beq E 36 _ 2 E36 (t1_u4 _ _) ltac:(lia)) in Hc.
         change (bv_swrap 32 (u_at (hs_arb h Hb now) (468 - 444) 4)) with (s32_at (hs_arb h Hb now) 24) in Hc.
         apply Z.eqb_neq in Hc. rename Hc into HR2.
         t1_epi_leaf HS HJ SHOK MF FIX E2 E3 E4 U8 E23 R2 R3 R4 R23.
         rewrite E33, t1_sext by apply t1_u4.
         rewrite t1_seqzk by first [lia | apply t1_sw; apply t1_u4].
         rewrite (t1_vB h Hb now HP1 ltac:(tauto)). reflexivity.
Qed.
End w3.
Section w5. Context {fx : YK11.FPState}.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Lemma hs_shok : forall (W : world SEGS) ly S mem md (E : env) (h hb hn : Z),
AR SEGS B ly S W mem md -> In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
U E HSBx = SHADOW_OFF -> U E (SOff 10 0) = h ->
sh_ok SEGS HSBx hs_SH E (mrestrict (w_H W) mem).
Proof.
intros W ly S mem md E h hb hn HAR Hin Hlo Hhi UBx Uh.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (_ & Hbb4096 & Hbbceil & Hbbapp & _ & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
unfold sh_ok, hs_SH. constructor; [|constructor].
eapply (shent_ok_of_range SEGS (w_H W) mem E HSBx 10 h 480 h 0 480).
- eapply (range_addressable_of_block SEGS B LAWS ly S W mem md hb hn h 480 HAR Hin); lia.
- exact UBx.
- exact Uh.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
unfold SHADOW_OFF in *. revert Hx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 C1 C3. clear.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma hs_entry : forall ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z),
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
getr regs 10 = w64 h -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
0 < h -> h mod 8 = 0 ->
In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
st_ok_pi SEGS VAL (EH regs) ss_hs
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_hunt_step)) mem (seg_rom SEGS)))
/\ sh_ok SEGS HSBx hs_SH (EH regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch h now hb hn HPRE H10 H11 Rnow Hh0 Hh8 Hin Hlo Hhi.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbn).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
pose proof pa_B_ok as HBASE.
pose proof (pa_val_range (A_OBJ 1)) as Rv1. pose proof (pa_val_range (A_OBJ 66)) as Rv66.
assert (HimgL : 0 <= IMG_LO /\ IMG_LO <= IMG_TOP /\ IMG_TOP <= kLowMemEnd).
{ unfold IMG_LO, IMG_TOP, kLowMemEnd. lia. }
rewrite restrict_mkst_fx.
set (E := EH regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
by (intros n Hn; subst E; unfold EH; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (UBx : U E HSBx = SHADOW_OFF).
{ unfold U, HSBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). exact SB_SHADOW_OFF. }
assert (Uh : U E (SOff 10 0) = h).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
split.
- unfold ss_hs. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold hs_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ecell) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 HSBx SB);
      [cbn [sv_denot HSBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold hs_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].

    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) Ecell) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hbceil Hbimg Hb4096 Hlo Hhi Hh0 C1 C3 WS Hstk0 HcellR HgcD HgotR Hrq0 Hrq1 HimgL.
    clear. unfold off_img, IMG_LO, IMG_TOP, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [hs_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hbceil Hb4096 Hlo Hhi Hh0 Hh8 Hal16 C1 C3 WS Hstk0 Rnow Hrq0 Hrq1.
    clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- exact (hs_shok W ly S mem md E h hb hn HAR Hin Hlo Hhi UBx Uh).
Qed.
(* YCbq.aj_call for a callee whose post leaves the FP state apost_base's way (an fx' with every f-register but
   f10 kept and the csr kept or with frm = 0), so the caller runs on in that fx'. Same proof as aj_call. *)
Lemma hs_aj_callF : forall W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) spw raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  YP0l.st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
  o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o) (s0Z (ms_regs ms)) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W (ms_regs ms) (ms_mem ms) mdc ch1 ->
   SRr SEGS W (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
        (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
        hs_csr fx fx' /\
        ajournal SEGS B STK1 (spZ (ms_regs ms)) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg ms mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
       hs_csr fx fx' /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W (ms_mem ms) mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved (ms_regs ms) regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o spw raw ch1 K
  HS Hrv HJ Hsp HE2 Hspw Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _). assert (ASTACK = 16384) as Has by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite YP0m.denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. lia. }
rewrite (st_ok_restrict_mkst SEGS (w_H W) E ss ms HS Hrv).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k (ms_regs ms) STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hcs|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma hs_spine : forall ly S W (regs : bvmap 5 word) mem md ch (h now hb hn : Z) (Hb : list byte),
afn_pre SEGS B REAC_HUNT_STEP_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 h -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
0 < h -> h mod 8 = 0 ->
In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
hunt_ok Hb ->
garr8 SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) Hb) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
(forall x, 0 <= x < 8 -> in_img SEGS (VAL (A_HI 97) + -1832 + x) /\ in_img SEGS (VAL (A_HI 96) + -1628 + x)) ->
(forall x, 0 <= x < 12 -> in_img SEGS (VAL (A_OBJ 65) + x)) ->
SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_reac_hunt_step) regs mem md)
  (treac_hunt_step_post fx regs ly S W mem md h now Hb).
Proof.
intros ly S W regs mem md ch h now hb hn Hb HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hlo Hhi HOK HGin
HRA HGR HD6 HD3 HIMG HIMGR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as HBASE.
pose proof HOK as (LHb & TOKb & LOKb & V0R).
destruct (hs_entry ly S W regs mem md ch h now hb hn HPRE H10 H11 Rnow Hh0 Hh8 Hin Hlo Hhi) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_HUNT_STEP_STK (HSFP h) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_STEP_STK = 8432) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hin) as (Hbb16 & Hbb4096 & Hbbceil & Hbbapp & Hbbpres & _ & Hbbn).
pose proof (req_size_pos' hn ltac:(lia)) as [Hrq0 Hrq1].
set (E := EH regs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EH; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SB]) n)
by (intros n Hn; subst E; unfold EH; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E2b : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold cfg_at. change (w64 (BASE + AF_reac_hunt_step)) with (Z_to_bv 64 (BASE + AF_reac_hunt_step)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
pose proof (proj1 HJ) as HARc.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 112).
{ unfold spZ at 1. rewrite Q2, Usp. apply unsigned_lit_small. lia. }
assert (HKrun : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1. rewrite !(aview_mbyte SEGS). f_equal. apply (mbyte_of_frame_x SEGS E _ _ _ a HFr Ha).
intros r Hr. unfold ss_hs, hs_regions in Hr. cbn [ss_mem In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP base_val];
[rewrite Usp; lia | lia | lia]. }
assert (HGc : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) h (map (fun b : byte => bv_unsigned b) Hb)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) h (map (fun b : byte => bv_unsigned b) Hb)).
- intros a Ha. rewrite length_map in Ha. apply HKrun; lia.
- exact HGin. }
pmkst HS.
rewrite pa_sigma_reac_disco_table_age.
eapply SRr_bind.
{ eapply (TAGE fx REAC_HUNT_STEP_STK (spZ regs) (HSFP h) ly S W mem md [] ly S W (ms_mem ms)
(with_vm_backing (m_vm_lazy md) mat md) 0 (ms_regs ms) h now (firstn 400 Hb)).
- exact HJ.
- eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ | exact HROD].
- rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Q1, unsigned_lit_small by lia. unfold IMG_LO in HBLO. lia.
- rewrite Q3, E3. exact Hgp.
- rewrite Q4, E4. exact Htp.
- rewrite Q10, E10. reflexivity.
- rewrite Q11, E11. reflexivity.
- exact Rnow.
- rewrite Hsp1, Zminus_mod, Hal16. reflexivity.
- rewrite Hsp1. unfold REAC_DISCO_TABLE_AGE_STK, ESTACK. lia.
- rewrite Hsp1. lia.
- lia.
- exact Hh8.
- lia.
- eapply (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) _ hb hn h 400 HARc Hin); lia.
- right. rewrite Hsp1. unfold REAC_DISCO_TABLE_AGE_STK, ESTACK. lia.
- intros a Ha. split.
+ right. left. split;
[exists (h, h + 400); split; [left; reflexivity | cbn; lia] | exists hb, hn; split; [exact Hin | lia]].
+ apply (apresent_grows (w_H W) mem (ms_mem ms) a HG). apply (proj1 (Hbbpres a ltac:(lia))).
- eapply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) _ hb hn h 400 HARc Hin); lia.
- eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) _ hb hn h 400 HARc Hin); lia.
- rewrite length_firstn. lia.
- exact TOKb.
- rewrite hs_map_firstn.
pose proof (garr8_sub_x SEGS (mrestrict (w_H W) (ms_mem ms)) h (map (fun b : byte => bv_unsigned b) Hb) 0 400
HGc ltac:(rewrite length_map; lia)) as Hgg.
cbn [skipn] in Hgg. rewrite Z.add_0_r in Hgg. exact Hgg. }
cbv beta.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & T' & rem & -> & HJ2 & HP2 & Ha0 & Hfrs2 & HPerm2 & HKEEP & HWeq & HKV & HGT & HAGEM & HAGEP).
rewrite Q1.
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (hb, hn) (ablocks B ly2 S2))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hin]).
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
pose proof HKEEP as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
rewrite Hsp1 in HK1, HK5, HK6.
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
- split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi stack_region base_val];
rewrite Usp; intros a Ha;
[ apply mbyte_of_aview_eq; apply HK1; [lia | lia | lia]
| intros _; apply (apresent_writable SEGS); apply HK5; [lia | lia | apply HJpres; lia] ].
- apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
[exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (val_mem_of_rdword SEGS _ _ _ _ Kgot) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 66) (VAL (A_OBJ 66)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 66) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| exact (val_mem_of_rdword SEGS _ _ _ _ Kcell) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDb : forall n, (n < 33)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
clear HEb.
assert (F2 : ew Eb 2 = getr regs 2) by (rewrite OLDb by (cbv; lia); exact E2).
assert (F10 : ew Eb 10 = Z_to_bv 64 h) by (rewrite OLDb by (cbv; lia); exact E10).
assert (F32 : ew Eb 32 = Z_to_bv 64 SB) by (rewrite OLDb by (cbv; lia); exact E32).
assert (Usp2 : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite F2; reflexivity).
assert (UBx2 : U Eb HSBx = SHADOW_OFF).
{ unfold U, HSBx. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). exact SB_SHADOW_OFF. }
assert (Uh2 : U Eb (SOff 10 0) = h).
{ unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
pose proof (hs_shok W2 ly2 S2 mem2 md2 Eb h hb hn HAR2 Hin2 Hlo Hhi UBx2 Uh2) as SHOK2.
paj_run_tok RUN HS HJ2 SHOK2 Bspan.
{ awr_ok_tac; exact Usp2. }
pose proof (proj1 (proj2 HJ2)) as HLY2.
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _).
pose proof HAGEP as (LT' & _ & _ & _ & _ & _ & TOK' & _).
prreg HS (1%bv : bv 5) Rr1. prreg HS (2%bv : bv 5) Rr2. prreg HS (3%bv : bv 5) Rr3.
prreg HS (4%bv : bv 5) Rr4. prreg HS (8%bv : bv 5) Rr8. prreg HS (10%bv : bv 5) Rr10.
prreg HS (11%bv : bv 5) Rr11. prreg HS (12%bv : bv 5) Rr12. prreg HS (13%bv : bv 5) Rr13.
prreg HS (14%bv : bv 5) Rr14. prreg HS (15%bv : bv 5) Rr15.
assert (HKrun2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1. rewrite !(aview_mbyte SEGS). f_equal. apply (mbyte_of_frame_x SEGS Eb _ _ _ a HFr0 Ha).
intros r Hr. unfold ss_hs, hs_regions in Hr. cbn [ss_mem In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP base_val];
[rewrite Usp2; lia | lia | lia]. }
assert (HGT2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) h (map (fun b : byte => bv_unsigned b) T')).
{ apply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms0) h (map (fun b : byte => bv_unsigned b) T')).
- intros a Ha. rewrite length_map, LT' in Ha. apply HKrun2; lia.
- exact HGT. }
assert (HGU0 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (h + 412)
(map (fun b : byte => bv_unsigned b) (sub Hb 412 6))).
{ rewrite hs_map_sub.
pose proof (garr8_sub_x SEGS (mrestrict (w_H W) (ms_mem ms)) h (map (fun b : byte => bv_unsigned b) Hb) 412 6
HGc ltac:(rewrite length_map; lia)) as G. cbn [Z.of_nat] in G. exact G. }
assert (L6 : length (map (fun b : byte => bv_unsigned b) (sub Hb 412 6)) = 6%nat)
by (rewrite length_map; unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
assert (HGU2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) (h + 412)
(map (fun b : byte => bv_unsigned b) (sub Hb 412 6))).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W2) (ms_mem ms) (ms_mem ms0) (h + 412)
(map (fun b : byte => bv_unsigned b) (sub Hb 412 6))).
- intros a Ha. rewrite L6 in Ha. cbn [Z.of_nat] in Ha.
rewrite HKrun2 by lia. replace a with (hb + (a - hb)) by lia. apply (HK2 hb hn (a - hb) Hin ltac:(lia) ltac:(lia)).
- exact HGU0. }
assert (HKall : forall a, spZ regs <= a < 2 ^ 64 ->
aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite HKrun2 by lia. rewrite HK1 by lia. apply HKrun; lia. }
assert (Hs0e : getr (ms_regs ms0) 8 = getr regs 8).
{ rewrite Rr8, OLDb by (cbv; lia). rewrite EL by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs [Z_to_bv 64 SB] 8 8%bv eq_refl). }
assert (HCH : achain ly2 (aview SEGS (w_H W2) (ms_mem ms0)) (spZ regs - 112) (s0Z (ms_regs ms0)) ch).
{ unfold s0Z. rewrite Hs0e. change (bv_unsigned (getr regs 8)) with (s0Z regs).
apply (achain_lower ly2 (aview SEGS (w_H W2) (ms_mem ms0)) (spZ regs) (spZ regs - 112)); [|lia].
apply (achain_ly_top ly ly2 (aview SEGS (w_H W2) (ms_mem ms0)) (spZ regs) (s0Z regs) ch);
[first [exact Etop2 | symmetry; exact Etop2] |].
apply (achain_kept ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) (ms_mem ms0)) (spZ regs) (s0Z regs) ch
(spZ regs) Hch ltac:(lia) ltac:(lia)).
intros a Ha. apply HKall. lia. }
assert (Rr2v : getr (ms_regs ms0) 2 = sv_denot Eb (SOff 2 (-112))) by (cbn [sv_denot]; exact Rr2).

eapply SRr_bind.
{ eapply hs_aj_callF with (STK1 := REAC_ARBITRATE_STK) (FP1 := [(h + 444, h + 444 + 32)])
(EV1 := 0) (o := -112);
[ exact HS
| reflexivity
| exact HJ2
| exact Rr2v
| reflexivity
| exact Usp2
| reflexivity
| lia
| unfold REAC_ARBITRATE_STK, ESTACK; lia
| unfold REAC_HUNT_STEP_STK; lia
| rewrite Rr3, OLDb by (cbv; lia); rewrite E3; exact Hgp
| rewrite Rr4, OLDb by (cbv; lia); rewrite E4; exact Htp
| exact Rr1
| apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite unsigned_lit_small by lia; unfold IMG_LO in HBLO; lia
| exact HCH
| intros HPRE1
| intros a Ha; left; split;
[ destruct Ha as (r & Hr & Hr2); cbn [In] in Hr; destruct Hr as [<- | []];
cbn [fst snd] in Hr2; exists (h + 440, h + 476); split; [right; left; reflexivity | cbn; lia]
| exists hb, hn; split; [exact Hin2 |
destruct Ha as (r & Hr & Hr2); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [fst snd] in Hr2; lia] ] ].
cbn [ss_pc setpc]. rewrite pa_sigma_reac_arbitrate. rewrite <- Rr1.
eapply (TARB fx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ ch h (h + 412) 0 0 now (h + 444) hb hn hb hn hb hn
T' (sub Hb 412 6) HPRE1).
- eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ2 | exact HROD].
- rewrite Rr10, OLDb by (cbv; lia). rewrite E10. reflexivity.
- rewrite Rr11. cbn [sv_denot]. rewrite OLDb by (cbv; lia). rewrite E10, unsigned_lit_small by lia. reflexivity.
- exact Rr12.
- exact Rr13.
- rewrite Rr14, OLDb by (cbv; lia). rewrite E11. reflexivity.
- rewrite Rr15. cbn [sv_denot]. rewrite OLDb by (cbv; lia). rewrite E10, unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- lia.
- lia.
- exact Rnow.
- lia.
- exact Hin2.
- lia.
- lia.
- assert (Hm4 : h mod 4 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 4 8 h); [exists 2; reflexivity|].
apply Z.mod_divide; [lia | exact Hh8]. }
rewrite Zplus_mod, Hm4. reflexivity.
- intros _. split; [exact Hin2|]. split; [lia|]. split; [lia|]. split; [exact Hh8|].
split; [exact LT'|]. split; [exact HGT2|]. split; [exact TOK' | lia].
- intros _. split; [exact Hin2|]. split; [lia|]. split; [lia|].
split; [unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity|].
split; [exact HGU2 | lia]. }
cbv beta.
intros W3 c3 Hwle3 (fq3 & ly3 & S3 & regs3 & mem3 & md3 & -> & Hfr3 & Hcs3 & HJ3 & HJc3 & HP3 & Hra3 & HPerm3 & HGA & HGTt & HGP
& HWeq3 & HKARB).
pose proof (proj1 HJ3) as HAR3.
assert (Hin3 : In (hb, hn) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm3|].
eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hin]. }
specialize (HGTt ltac:(lia)). specialize (HGP ltac:(lia)).
subst W3. subst W2.
assert (Hsp2 : spZ (ms_regs ms0) = spZ regs - 112) by (unfold spZ at 1; rewrite Rr2, Usp2; apply unsigned_lit_small; lia).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hin) as Hbimg.
assert (KALL : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - REAC_HUNT_STEP_STK <= x < spZ regs) ->
  ~ (h <= x < h + 400) -> ~ (h + 444 <= x < h + 476) -> aview SEGS (w_H W) mem3 x = aview SEGS (w_H W) mem x).
{ intros x Hx Hs Ht Ha.
  pose proof (HKARB (Z_to_bv 64 x)) as K1. rewrite unsigned_lit_small in K1 by lia. rewrite Hsp2 in K1.
  rewrite K1 by (unfold REAC_ARBITRATE_STK, ESTACK in *; lia).
  rewrite HKrun2 by lia.
  pose proof (HKV (Z_to_bv 64 x)) as K2. rewrite unsigned_lit_small in K2 by lia. rewrite Hsp1 in K2.
  rewrite K2 by (unfold REAC_DISCO_TABLE_AGE_STK, ESTACK in *; lia).
  apply HKrun; lia. }
assert (IMGK : forall x, in_img SEGS x -> aview SEGS (w_H W) mem3 x = aview SEGS (w_H W) mem x).
{ intros x Hx. pose proof (pa_img_range x Hx) as Rx.
  apply KALL; revert Rx Hbimg Hlo Hhi Hrq0 Hrq1 Hslo Hceil Hstk0 C1 C2 C3 C4 C5 WS; clear;
  unfold off_img, IMG_LO, IMG_TOP; intros; lia. }
assert (HRA3 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (VAL (A_OBJ 65)) 12).
{ intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  pose proof (HIMGR (x - VAL (A_OBJ 65)) ltac:(lia)) as Hi.
  replace (VAL (A_OBJ 65) + (x - VAL (A_OBJ 65))) with x in Hi by lia.
  pose proof (pa_img_range x Hi) as Rx.
  rewrite KALL; [exact Hs | | | |];
  revert Rx Hbbapp Hbb4096 Hbbceil Hlo Hhi Hrq0 Hrq1 Hslo Hceil Hstk0 C1 C2 C3 C4 C5 WS; clear;
  unfold shadow_of_addr, SHADOW_OFF, IMG_LO, IMG_TOP, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros;
  Z.div_mod_to_equations; lia. }
assert (HGR3 : garr8 SEGS (mrestrict (w_H W) mem3) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES)).
{ apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3); [|exact HGR].
  intros a Ha. rewrite length_map in Ha. change (length RATES) with 12%nat in Ha. apply IMGK.
  pose proof (HIMGR (a - VAL (A_OBJ 65)) ltac:(change (Z.of_nat 12) with 12 in Ha; lia)) as Hi.
  replace (VAL (A_OBJ 65) + (a - VAL (A_OBJ 65))) with a in Hi by lia. exact Hi. }
assert (HD63 : val_mem SEGS (mrestrict (w_H W) mem3) (VAL (A_HI 97) + -1832) 8 D6000).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3); [|exact HD6].
  intros k Hk. apply IMGK. destruct (HIMG k ltac:(change (Z.of_nat 8) with 8 in Hk; lia)) as [Hi _]. exact Hi. }
assert (HD33 : val_mem SEGS (mrestrict (w_H W) mem3) (VAL (A_HI 96) + -1628) 8 D3837).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem mem3); [|exact HD3].
  intros k Hk. apply IMGK. destruct (HIMG k ltac:(change (Z.of_nat 8) with 8 in Hk; lia)) as [_ Hi]. exact Hi. }
pose proof (st_ok_region_nth Eb _ _ 0 (YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 hs_pro_chunks) HS
  ltac:(vm_compute; reflexivity)) as RS.
unfold region_ok in RS.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem] in RS.
destruct RS as (_ & _ & _ & RC). rewrite Usp2 in RC.
assert (HFR0 : hs_frame regs (mrestrict (w_H W) (ms_mem ms0)) (spZ regs)).
{ apply (hs_frame_of_chunks Eb _ regs (spZ regs)); [|exact RC].
  intros r. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite OLDb by lia. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_reg. }
assert (HFR3 : hs_frame regs (mrestrict (w_H W) mem3) (spZ regs)).
{ apply (hs_frame_kept regs (w_H W) (w_H W) (ms_mem ms0) mem3); [|exact HFR0].
  intros a Ha. pose proof (HKARB (Z_to_bv 64 a)) as K1. rewrite unsigned_lit_small in K1 by lia. rewrite Hsp2 in K1.
  apply K1; unfold REAC_ARBITRATE_STK, ESTACK in *; lia. }
prreg HS (9%bv : bv 5) Ss9. prreg HS (18%bv : bv 5) Ss18. prreg HS (19%bv : bv 5) Ss19.
prreg HS (20%bv : bv 5) Ss20. prreg HS (23%bv : bv 5) Ss23.
assert (HT : hs_table Hb now = T').
{ unfold hs_table. change (sub Hb 0 400) with (firstn 400 Hb). rewrite HAGEM. reflexivity. }
assert (L6b : length (sub Hb 412 6) = 6%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
assert (HA : hs_arb h Hb now = reac_arbitrate_c.arb_model h (h + 412) T' (sub Hb 412 6) 0 0 now)
by (unfold hs_arb; rewrite HT; reflexivity).
assert (LA : length (hs_arb h Hb now) = 32%nat)
by (rewrite HA; apply reac_hunt_step.hs_len_arb; [exact LT' | exact L6b | exact (proj1 TOK')]).
pose proof LA as LA'. rewrite HA in LA'.
assert (LX : length (sub Hb 400 44) = 44%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
assert (LR4 : length (sub Hb 476 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn, LHb; reflexivity).
assert (HIMG3 : garr8 SEGS (mrestrict (w_H W) mem3) h (map (fun b : byte => bv_unsigned b) (hs_img h now Hb))).
{ unfold hs_img. rewrite HT, HA. rewrite !map_app.
  apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact HGTt|].
  rewrite length_map, LT'. change (Z.of_nat 400) with 400.
  apply (proj2 (garr8_app SEGS _ _ _ _)). split.
  - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3).
    + intros a Ha. rewrite length_map, LX in Ha. change (Z.of_nat 44) with 44 in Ha. apply KALL; lia.
    + rewrite hs_map_sub. change (Z.to_nat 400) with 400%nat.
      pose proof (garr8_sub_x SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) Hb) 400 44 HGin
      ltac:(rewrite length_map; lia)) as G. cbn [Z.of_nat] in G. exact G.
  - rewrite length_map, LX. change (Z.of_nat 44) with 44. replace (h + 400 + 44) with (h + 444) by lia.
    apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact HGA|].
    rewrite length_map, LA'. change (Z.of_nat 32) with 32. replace (h + 444 + 32) with (h + 476) by lia.
    apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem3).
    + intros a Ha. rewrite length_map, LR4 in Ha. change (Z.of_nat 4) with 4 in Ha. apply KALL; lia.
    + rewrite hs_map_sub. change (Z.to_nat 476) with 476%nat.
      pose proof (garr8_sub_x SEGS (mrestrict (w_H W) mem) h (map (fun b : byte => bv_unsigned b) Hb) 476 4 HGin
      ltac:(rewrite length_map; lia)) as G. cbn [Z.of_nat] in G. exact G. }
assert (HOKH : hunt_ok (hs_hunt h Hb now)).
{ unfold hs_hunt. rewrite HT, HA. apply reac_hunt_step.hs_hunt_ok; [exact LT' | exact LHb | exact LA' | | exact TOK' | exact LOKb].
  unfold hs_verdict. apply reac_hunt_step.hs_dec_range. exact V0R. }
assert (CS : forall n, acallee_saved n -> getr regs3 (Z_to_bv 5 n) = getr (ms_regs ms0) (Z_to_bv 5 n)) by exact HP3.
apply (hs_tree (fx := fq3) fx ly S W regs mem md ch h now hb hn Hb ly3 S3 W regs3 mem3 md3).
- exact HPRE.
- exact HJ3.
- exact (hs_freg_apost _ _ _ (fun k _ _ _ => eq_refl) Hfr3).
- exact Hcs3.
- eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ3 | exact HROD].
- exact HRA3.
- exact HGR3.
- exact HD63.
- exact HD33.
- transitivity (getr (ms_regs ms0) 2); [exact (CS 2 ltac:(unfold acallee_saved; lia))|].
  rewrite Rr2, Usp2. unfold w64. f_equal; try lia.
- transitivity (getr (ms_regs ms0) 3); [exact (CS 3 ltac:(unfold acallee_saved; lia))|].
  rewrite Rr3, OLDb by (cbv; lia). exact E3.
- transitivity (getr (ms_regs ms0) 4); [exact (CS 4 ltac:(unfold acallee_saved; lia))|].
  rewrite Rr4, OLDb by (cbv; lia). exact E4.
- transitivity (getr (ms_regs ms0) 9); [exact (CS 9 ltac:(unfold acallee_saved; lia))|].
  rewrite Ss9, F10. try reflexivity.
- transitivity (getr (ms_regs ms0) 18); [exact (CS 18 ltac:(unfold acallee_saved; lia))|].
  rewrite Ss18, ?OLDb by (cbv; lia). rewrite ?E11. try reflexivity.
- transitivity (getr (ms_regs ms0) 19); [exact (CS 19 ltac:(unfold acallee_saved; lia))|].
  rewrite Ss19, F10, unsigned_lit_small by lia. try reflexivity.
- transitivity (getr (ms_regs ms0) 20); [exact (CS 20 ltac:(unfold acallee_saved; lia))|].
  rewrite Ss20, F10, unsigned_lit_small by lia. try reflexivity.
- transitivity (getr (ms_regs ms0) 23); [exact (CS 23 ltac:(unfold acallee_saved; lia))|].
  rewrite Ss23, F32. rewrite SB_SHADOW_OFF. reflexivity.
- exact HFR3.
- exact Hh0.
- exact Hh8.
- exact Hin3.
- exact Hlo.
- exact Hhi.
- exact Rnow.
- exact HOK.
- rewrite HT. exact LT'.
- rewrite HT. exact TOK'.
- exact LA.
- exact HIMG3.
- exact HOKH.
- eapply Permutation_trans; [exact HPerm3 | exact HPerm2].
Qed.
End w5.
Theorem pb_reac_hunt_step : treac_hunt_step_spec.
Proof.
unfold treac_hunt_step_spec.
intros fq ly S W regs mem md ch h now hb hn H HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hlo Hhi HOK HG HRA HGR HD6 HD3 HIMG HIMGR.
exact (@hs_spine fq ly S W regs mem md ch h now hb hn H HPRE HROD H10 H11 Rnow Hh0 Hh8 Hin Hlo Hhi HOK HG HRA HGR HD6 HD3
HIMG HIMGR).
Qed.
End h.
End f.
End d.
