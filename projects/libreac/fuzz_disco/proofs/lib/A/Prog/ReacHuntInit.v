(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 902 of its 935 lines of code are new or changed and 36 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI08 YI0n YI0s YI09 YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC1i YC85 DiscoFrame DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableInit ReacDiscoPeerLockInit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
CtrlParsed disco_classify_c disco_table_c hunt_c reac_disco_table_init_c reac_hunt_init_c reac_master_only_cadence_ns_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_init.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis TTABLEINIT : treac_disco_table_init_spec B.
Hypothesis TPEERLOCKINIT : treac_disco_peer_lock_init_spec B.
Definition REAC_HUNT_INIT_STK : Z :=
  48 + Z.max ESTACK (Z.max REAC_DISCO_TABLE_INIT_STK REAC_DISCO_PEER_LOCK_INIT_STK).
Definition treac_hunt_init_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (h our now : Z) (ob : list byte) : world SEGS -> config -> Prop :=
  fun W' c' =>
    apost_base (fx := fq) SEGS B REAC_HUNT_INIT_STK [(h, h + 480)] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         garr8 SEGS (mrestrict (w_H W') mem') h
           (map (fun b : byte => bv_unsigned b) (hunt_init_bytes (if our =? 0 then repeat (Z_to_bv 8 0) 6 else ob) now)) /\
         hunt_ok (hunt_init_bytes (if our =? 0 then repeat (Z_to_bv 8 0) 6 else ob) now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_hunt_init_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (h our now hb hn : Z) (ob : list byte),
  afn_pre SEGS B REAC_HUNT_INIT_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 h -> getr regs 11 = w64 our -> getr regs 12 = w64 now ->
  0 <= our < 2 ^ 64 -> 0 <= now < 2 ^ 64 ->
  0 < h -> h mod 8 = 0 ->
  In (hb, hn) (ablocks B ly S) -> hb <= h -> h + 480 <= hb + req_size hn ->
  (our <> 0 -> afobj SEGS B ly S W mem our 6 /\ length ob = 6%nat /\
     garr8 SEGS (mrestrict (w_H W) mem) our (map (fun b : byte => bv_unsigned b) ob)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_hunt_init) regs mem md)
    (treac_hunt_init_post fq regs ly S W mem md h our now ob).
Lemma hi_getr_s0z : forall regs (r : bv 5) v, r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs r v H. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. apply regupd_other. exact H. Qed.
Definition hi_got : YP09.region := YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 307%nat 0))].
Definition hi_bcell : YP09.region := YP09.mkRegion (Some 307%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32%nat 0))].
Definition hi_regions : smem := [stack_region 48; hi_got; hi_bcell].
Definition hi_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_hi : sstate := mkSS AF_reac_hunt_init sr_atoms hi_regions None hi_facts.
Definition HIBx : sv := SOff 32 0.
Definition HIspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma hi_ra_kept : forall (rd rd' : Z -> option Z) a n,
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
exists s. rewrite (HK x Hx). split; [exact Hs | exact Hok].
Qed.
Lemma hi_shadow_in_frame : forall ly S (W : world SEGS) mem md cid pos p n x,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid -> p <= x < p + n ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S W mem md cid pos p n x HAR Hin Hfp Hpn Hx.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (L1 : f / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (L2 : x / 8 < f / 8 + bs / 8) by (rewrite E8f, E8b; apply Z.div_lt_upper_bound; lia).
unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia.
Qed.
Lemma hi_shadow_off_block : forall ly S (W : world SEGS) mem md cid pos a p n,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  in_app p n -> p + n <= alloc_ceiling -> 0 <= n -> ~ (p <= a < p + n).
Proof.
intros ly S W mem md cid pos a p n HAR Hin Ha Happ Hpc Hn.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
pose proof asan_consts as (CA & _).
unfold in_zr, shadow_addr in Ha. cbn [fst snd] in Ha.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
Lemma hi_shadow_bound : forall ly S (W : world SEGS) mem md cid pos a,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) -> SHADOW_OFF <= a < alloc_ceiling.
Proof.
intros ly S W mem md cid pos a HAR Hin Ha.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (H4096 & Hceil & _).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
pose proof asan_consts as (CA & _).
unfold in_zr, shadow_addr, SHADOW_OFF in *. cbn [fst snd] in Ha. lia.
Qed.
Lemma hi_map_zero : forall n, map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) n) = repeat 0 n.
Proof. induction n as [|n IH]; cbn [map repeat]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma hi_shent_blk : forall ly S (W : world SEGS) mem md Ex Bx (m : nat) p b n lo hi,
  AR SEGS B ly S W mem md -> In (b, n) (ablocks B ly S) ->
  U Ex Bx = SHADOW_OFF -> U Ex (SOff m 0) = p -> b <= p -> 0 <= lo -> lo <= hi -> p + hi <= b + req_size n ->
  shent_ok SEGS Bx Ex (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
intros ly S W mem md Ex Bx m p b n lo hi HAR Hin HB Hm Hbp Hlo Hlh Hhi.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & _ & _ & Happ & _).
split.
- destruct (Z_lt_le_dec lo hi) as [Hlt | Hle]; [|apply range_addressable_nil; lia].
  rewrite <- (aview_rd_of SEGS).
  eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b n (p + lo) (hi - lo) HAR Hin); lia.
- intros a Ha. pose proof asan_consts as (CA & _).
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma hi_lb1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small x 256) by lia. rewrite (Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma hi_garr8_le8 : forall (W : world SEGS) m a v,
  0 <= v < 2 ^ 64 -> val_mem SEGS (mrestrict (w_H W) m) a 8 v ->
  garr8 SEGS (mrestrict (w_H W) m) a (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))).
Proof.
intros W m a v Hv HV j Hj. rewrite length_map, Mem.length_le8 in Hj.
assert (Hr : 0 <= YO0f.le_byte v 8 j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))) 0 = YO0f.le_byte v 8 j).
{ replace (nth j (map (fun b : byte => bv_unsigned b) (Mem.le8 (Z_to_bv 64 v))) 0)
    with (bv_unsigned (nth j (Mem.le8 (Z_to_bv 64 v)) (Z_to_bv 8 0)))
    by (rewrite <- (map_nth (fun b : byte => bv_unsigned b)); reflexivity).
  unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
  rewrite (nth_error_nth _ j (Z_to_bv 8 0) (nth_error_Z_to_le_bytes 8 v j Hj)).
  rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 8))) by (cbn [Z.of_nat Z.mul]; lia). reflexivity. }
rewrite Hnth. split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (HV j Hj). rewrite (hi_lb1 _ Hr). reflexivity.
Qed.
Lemma hi_garr8_z4 : forall (W : world SEGS) m a,
  val_mem SEGS (mrestrict (w_H W) m) a 4 0 -> garr8 SEGS (mrestrict (w_H W) m) a (repeat 0 4).
Proof.
intros W m a HV. apply garr8_zeros. intros x Hx.
specialize (HV (Z.to_nat (x - a)) ltac:(cbn [Z.of_nat] in Hx; lia)).
replace (a + Z.of_nat (Z.to_nat (x - a))) with x in HV by (cbn [Z.of_nat] in Hx; lia).
rewrite HV. f_equal. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity.
Qed.
Lemma hi_fr_out : forall Ex rs (Hh : word -> bool) (m m' : word -> option byte) a,
  frame_of Ex rs (mrestrict Hh m) (mrestrict Hh m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange Ex rs a ->
  aview SEGS Hh m' a = aview SEGS Hh m a.
Proof.
intros Ex rs Hh m m' a HF Ha Hno. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hno.
Qed.
Lemma hi_garr8_tr : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 base l,
  garr8 SEGS (mrestrict (w_H W1) m1) base l ->
  (forall x, base <= x < base + Z.of_nat (length l) -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x) ->
  garr8 SEGS (mrestrict (w_H W2) m2) base l.
Proof.
intros W1 m1 W2 m2 base l HG HK. eapply garr8_frame; [exact HG|].
intros a Ha. apply (mbyte_of_aview SEGS). apply HK. exact Ha.
Qed.
Lemma hi_aview_garr8 : forall (W : world SEGS) m base (l : list Z) j,
  garr8 SEGS (mrestrict (w_H W) m) base l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m base l j HG Hj. destruct (HG j Hj) as [Hv Hr].
unfold aview. rewrite (garr8_mbyte SEGS _ _ _ _ HG Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
Lemma hi_mbyte2 : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a1 a2,
  aview SEGS H2 m2 a2 = aview SEGS H1 m1 a1 -> mbyte SEGS (mrestrict H2 m2) a2 = mbyte SEGS (mrestrict H1 m1) a1.
Proof.
intros H1 H2 m1 m2 a1 a2 E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H2 m2) a2) as [b2|] eqn:E2; destruct (mbyte SEGS (mrestrict H1 m1) a1) as [b1|] eqn:E1;
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma hi_garr8_copy : forall (W1 : world SEGS) m1 (W2 : world SEGS) m2 b1 b2 (l : list Z),
  garr8 SEGS (mrestrict (w_H W1) m1) b1 l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W2) m2 (b2 + Z.of_nat j) = aview SEGS (w_H W1) m1 (b1 + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W2) m2) b2 l.
Proof.
intros W1 m1 W2 m2 b1 b2 l HG HK j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (hi_mbyte2 _ _ _ _ _ _ (HK j Hj)). exact Hv.
Qed.
Lemma hi_garr8_zeros : forall (W : world SEGS) m base n,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) m (base + i) = Some 0) ->
  garr8 SEGS (mrestrict (w_H W) m) base (repeat 0 n).
Proof.
intros W m base n HK. apply garr8_zeros. intros a Ha.
assert (Hv : aview SEGS (w_H W) m a = Some 0) by (replace a with (base + (a - base)) by lia; apply HK; lia).
destruct (aview_byte SEGS (w_H W) m a 0 Hv) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite <- Hbv. reflexivity.
Qed.
Ltac hi_kstep K sp0 AGx Uspx :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msX)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) ->
                 aview SEGS (w_H Wx) (ms_mem msX) a = aview SEGS (w_H Wx) m0 a);
    [ intros a Ha Hns; apply (hi_fr_out Ex rs _ _ _ a HFr Ha);
      intros (rg & Hin & Hrg);
      let rs' := eval vm_compute in rs in change (In rg rs') in Hin; cbn [In] in Hin;
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          rewrite ?(AGx 2%nat ltac:(lia)) in Hrg; rewrite ?Uspx in Hrg; lia | ]);
      destruct Hin
    | ] end.
Ltac hi_zn :=
  repeat match goal with
  | |- context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v
  | H : context [Z.of_nat ?n] |- _ => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H
  end.
Ltac hi_creg HS AGx EEx :=
  lazymatch goal with |- getr _ ?r = getr _ _ =>
    let R := fresh "Rc" in prreg HS r R; rewrite R;
    rewrite ?ew_ewset_other by lia; rewrite AGx by lia; apply EEx; reflexivity end.
Ltac hi_addblk HS AGx E10x E2x E3x Uspx Hin HJx lo hi :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 10%nat) lo hi lo hi []) HS eq_refl
      ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
            rewrite (AGx 10%nat ltac:(lia)), E10x, unsigned_lit_small by lia;
            split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
            intros o Ho; apply (apresent_writable SEGS);
            lazymatch type of Hin with In (?b, ?n) _ =>
              let Hpz := fresh "Hpz" in
              destruct (al_blocks _ _ LAWS _ _ _ _ _ b n (proj1 HJx) Hin) as (_ & _ & _ & _ & Hpz & _);
              lazymatch goal with |- apresent _ _ ?ad => exact (proj1 (Hpz ad ltac:(lia))) end end)
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite ?(AGx 2%nat ltac:(lia)), ?(AGx 10%nat ltac:(lia));
            rewrite ?E10x, ?E2x, ?E3x, ?Uspx;
            rewrite ?unsigned_lit_small by lia;
            repeat split; lia)) as HS3; clear HS; rename HS3 into HS; norm_ss HS end.
Ltac hi_consts HJx Kg Kc :=
  let Kc0 := fresh "Kc0" in let Ku0 := fresh "Ku0" in let Kg0 := fresh "Kg0" in let Kgu0 := fresh "Kgu0" in
  destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc0 & Ku0 & Kg0 & Kgu0);
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg0; rewrite (pal_cell B TL) in Kc0;
  pose proof (val_mem_of_rdword _ _ _ _ _ Kg0) as Kg; pose proof (val_mem_of_rdword _ _ _ _ _ Kc0) as Kc;
  clear Kc0 Ku0 Kg0 Kgu0.
Lemma hi_acall_table : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp t,
  treac_disco_table_init_kept B lyc Sc W memc W2 mem2 sp t -> t + 400 <= alloc_ceiling ->
  acall_kept SEGS B lyc Sc W memc W2 mem2 (sp - REAC_DISCO_TABLE_INIT_STK) sp (fun a => t <= a < t + 400).
Proof.
intros lyc Sc W memc W2 mem2 sp t (K1 & K2 & K3 & K4 & K5 & K6) Ht.
split; [intros a Ha Hw; apply K1; [exact Ha | exact Hw | lia]|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [exact K5 | exact K6].
Qed.
Lemma hi_acall_lock : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp l,
  treac_disco_peer_lock_init_kept B lyc Sc W memc W2 mem2 sp l -> l + 12 <= alloc_ceiling ->
  acall_kept SEGS B lyc Sc W memc W2 mem2 (sp - REAC_DISCO_PEER_LOCK_INIT_STK) sp (fun a => l <= a < l + 12).
Proof.
intros lyc Sc W memc W2 mem2 sp l (K1 & K2 & K3 & K4 & K5 & K6) Hl.
split; [intros a Ha Hw; apply K1; [exact Ha | exact Hw | lia]|].
split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
split; [exact K5 | exact K6].
Qed.
Ltac bvneq := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; cbv in X; discriminate X.
Theorem pb_reac_hunt_init : treac_hunt_init_spec.
Proof.
unfold treac_hunt_init_spec.
intros fq ly S W regs mem md ch h our now hb hn ob HPRE0 H10 H11 H12 Rour Rnow Hh0 Hh8 Hhb Hhlo Hhhi HOUR.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
pose proof (@pa_wx _ _ PI) as Hwx. pose proof (@pa_segs_low _ _ PI) as Hsegs.
assert (Hsp0 : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite hi_getr_s0z by bvneq; reflexivity).
pose proof (ajournal_init SEGS B REAC_HUNT_INIT_STK [(h, h + 480)] ly S W _ mem md ch HPRE0) as HJ.
rewrite Hsp0 in HJ.
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite hi_getr_s0z in Hra, Hgp, Htp by bvneq. unfold raZ in Hra4. rewrite hi_getr_s0z in Hra4 by bvneq. fold (raZ regs) in Hra4.
rewrite Hsp0 in Hstk, Hpres. clear Hch HPRE0.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_HUNT_INIT_STK = 4160) by reflexivity.
assert (WT : REAC_DISCO_TABLE_INIT_STK = 4112) by reflexivity.
assert (WL : REAC_DISCO_PEER_LOCK_INIT_STK = 4112) by reflexivity.
assert (WE : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md hb hn HAR Hhb) as (Hb16 & Hb4096 & Hbceil & Hbh_ia & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ hb hn HAR Hhb) as Hbh_img.
unfold off_img, IMG_LO, IMG_TOP in Hbh_img.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 66 ltac:(cbv; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(cbv; lia)) as HgotR.
pose proof (@pa_B_ok _ _ PI) as HBASE.
pose proof (pa_val_range (A_OBJ 1)) as RV1. pose proof (pa_val_range (A_OBJ 66)) as RV66.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
remember (Eimg (Ereg regs [Z_to_bv 64 SB])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 h) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 our) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 now) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E307 : ew E 307%nat = Z_to_bv 64 (VAL (A_OBJ 66))) by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1))) by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
unfold cfg_at. change (w64 (BASE + AF_reac_hunt_init)) with (Z_to_bv 64 (BASE + AF_reac_hunt_init)).
assert (HS : st_ok_pi SEGS VAL E ss_hi (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_hunt_init)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_hi. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold hi_regions, stack_region, hi_got, hi_bcell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite (VB 242%nat (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 307%nat 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite E307, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + rewrite (VB 307%nat (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 HIBx SB);
      [cbn [sv_denot HIBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold hi_regions, stack_region, hi_got, hi_bcell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 242%nat (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB 307%nat (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. unfold off_img, IMG_LO, IMG_TOP. intros.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [hi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hh8 Hb4096 Hbceil Hbh_ia Hhlo Hhhi Hh0. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    pose proof (req_size_pos hn) as HRS.
    repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS HIBx [] E (mrestrict (w_H W) mem)) by constructor.
paj_run_tok RUN HS HJ SHOK HIspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
hi_kstep K0 (spZ regs) AG Usp. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
hi_consts HJ KgotA KcellA.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
  eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA DS___asan_memset) (AMEMSET fq) W (ms_regs msX) (ms_mem msX)
    REAC_HUNT_INIT_STK (spZ regs) [(h, h + 480)] ly S W mem md [] ly S mdX 0 h 0 480 (-48) _ HJ) end.
  - rewrite Ra0. exact E10.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Rsp, Usp. apply unsigned_lit_small. lia.
  - reflexivity.
  - lia.
  - rewrite WS, WE. lia.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + right. left. split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|].
      exists hb, hn. split; [exact Hhb | lia].
    + unfold ESTACK. lia.
  - eapply (amem_range_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ) | exact Hhb | lia | lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ) | exact Hhb | lia | lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ) | exact Hhb | lia | lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2 & Hsame).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
assert (HZ1 : forall i, 0 <= i < 480 -> aview SEGS (w_H W) mem2 (h + i) = Some 0)
  by (intros i Hi; rewrite (Heff i Hi); reflexivity).
hi_consts HJ2 KgotB KcellB.
reseat HS HJ2 HP2 [0; 1; 2]%nat AG
  ltac:(idtac; first
    [ eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
      | intros a Ha; apply Hfr; unfold ESTACK; lia | exact Hpres2]
    | apply (region_kept_val_at E _ _ 242%nat (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
      [rewrite E242; apply unsigned_lit_small; lia | exact KgotA | exact KgotB | lia]
    | apply (region_kept_val_at E _ _ 307%nat (VAL (A_OBJ 66)) 8 SHADOW_OFF);
      [rewrite E307; apply unsigned_lit_small; lia | exact KcellA | exact KcellB | lia] ]).
assert (SHOK2 : sh_ok SEGS HIBx [] E0 (mrestrict (w_H W) mem2)) by constructor.
paj_run_tok RUN HS HJ2 SHOK2 HIspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp |].
hi_kstep K1 (spZ regs) AG Usp. clear_frames.
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wc ?mc _ _ =>
  assert (HZ2 : forall i, 0 <= i < 480 -> aview SEGS (w_H Wc) mc (h + i) = Some 0) end.
{ intros i Hi. rewrite (K1 (h + i) ltac:(lia) ltac:(lia)). apply HZ1. lia. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (Hspc : spZ (ms_regs ms0) = spZ regs - 48).
{ unfold spZ at 1. rewrite Rsp, (AG 2%nat ltac:(lia)), Usp. apply unsigned_lit_small. lia. }
assert (Hrac : raZ (ms_regs ms0) = BASE + 28444)
  by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
pmkst HS. rewrite pa_sigma_reac_disco_table_init.
hi_consts HJ2 KgotC KcellC.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
  eapply (TTABLEINIT fq REAC_HUNT_INIT_STK (spZ regs) [(h, h + 480)] ly S W mem md [] ly S W (ms_mem msX) mdX 0 (ms_regs msX) h) end.
  - exact HJ2.
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hrac. lia.
  - rewrite Rgp, (AG 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, (AG 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Ra0, (AG 10%nat ltac:(lia)). exact E10.
  - rewrite Hspc, <- Zminus_mod_idemp_l, Hal16. reflexivity.
  - rewrite Hspc, WS, WT. lia.
  - rewrite Hspc. lia.
  - lia.
  - exact Hh8.
  - lia.
  - lia.
  - right. rewrite Hspc, WT. lia.
  - intros a Ha. split.
    + right. left. split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|].
      exists hb, hn. split; [exact Hhb | lia].
    + destruct (al_blocks _ _ LAWS ly S W _ _ hb hn (proj1 HJ2) Hhb) as (_ & _ & _ & _ & Hp & _).
      exact (proj1 (Hp a ltac:(lia))).
  - eapply (amem_range_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ2) | exact Hhb | lia | lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ2) | exact Hhb | lia | lia].
  - eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ hb hn); [exact (proj1 HJ2) | exact Hhb | lia | lia | lia]. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & Hra3 & Hfrs3 & Hperm3 & HKEPT3 & HGARR3 & HTOK3).
rewrite Rra in Hc3. subst c3.
clear Ra0 Rsp Rgp Rtp.
unfold reac_disco_table_init_c.zero_table in HGARR3. rewrite hi_map_zero in HGARR3.
assert (HZ3 : forall i, 0 <= i < 480 -> aview SEGS (w_H W3) mem3 (h + i) = Some 0).
{ intros i Hi. destruct (Z_lt_le_dec i 400) as [Hlt | Hge].
  - replace (h + i) with (h + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (hi_aview_garr8 W3 mem3 h (repeat 0 400) (Z.to_nat i) HGARR3 ltac:(rewrite repeat_length; lia)).
    rewrite nth_repeat by (rewrite repeat_length in *; lia). reflexivity.
  - destruct HKEPT3 as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
    replace (h + i) with (hb + (h + i - hb)) by lia.
    rewrite (KT2 hb hn (h + i - hb) Hhb ltac:(lia) ltac:(lia)).
    replace (hb + (h + i - hb)) with (h + i) by lia. apply HZ2. lia. }
hi_consts HJ3 KgotD KcellD.
reseat HS HJ3 HP3 [0; 1; 2]%nat AG
  ltac:(idtac; first
    [ eapply (region_kept_stack_aj _ _);
      [eapply hi_acall_table; [exact HKEPT3 | lia] | exact HJ3
       | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
       | rewrite Hspc; lia | rewrite WS; lia
       | lia | lia | lia]
    | apply (region_kept_val_at E0 _ _ 242%nat (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
      [rewrite E242; apply unsigned_lit_small; lia | exact KgotC | exact KgotD | lia]
    | apply (region_kept_val_at E0 _ _ 307%nat (VAL (A_OBJ 66)) 8 SHADOW_OFF);
      [rewrite E307; apply unsigned_lit_small; lia | exact KcellC | exact KcellD | lia] ]).
clear Hspc Hrac Rra.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (SHOK3 : sh_ok SEGS HIBx [] Ex (mrestrict (w_H W3) mem3)) by constructor end.
paj_run_tok RUN HS HJ3 SHOK3 HIspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp |].
hi_kstep K2 (spZ regs) AG Usp. clear_frames.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wc ?mc _ _ =>
  assert (HZ4 : forall i, 0 <= i < 480 -> aview SEGS (w_H Wc) mc (h + i) = Some 0) end.
{ intros i Hi. rewrite (K2 (h + i) ltac:(lia) ltac:(lia)). apply HZ3. lia. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (Hhb3 : In (hb, hn) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm3)); exact Hhb).
assert (Hspc : spZ (ms_regs ms1) = spZ regs - 48).
{ unfold spZ at 1. rewrite Rsp, (AG 2%nat ltac:(lia)), Usp. apply unsigned_lit_small. lia. }
assert (Hrac : raZ (ms_regs ms1) = BASE + 28452)
  by (unfold raZ; rewrite Rra; apply unsigned_lit_small; lia).
assert (Hh4 : (h + 400) mod 4 = 0).
{ rewrite Z.mod_divide by lia. rewrite Z.mod_divide in Hh8 by lia. destruct Hh8 as [k Hk]. exists (2 * k + 100). lia. }
pmkst HS. rewrite pa_sigma_reac_disco_peer_lock_init.
hi_consts HJ3 KgotE KcellE.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
  eapply (TPEERLOCKINIT fq REAC_HUNT_INIT_STK (spZ regs) [(h, h + 480)] ly S W mem md [] ly3 S3 W3 (ms_mem msX) mdX 0 (ms_regs msX) (h + 400)) end.
  - exact HJ3.
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hrac. lia.
  - rewrite Rgp, (AG 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, (AG 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Ra0, (AG 10%nat ltac:(lia)), E10, unsigned_lit_small by lia. reflexivity.
  - rewrite Hspc, <- Zminus_mod_idemp_l, Hal16. reflexivity.
  - rewrite Hspc, WS, WL. lia.
  - rewrite Hspc. lia.
  - exact Hh4.
  - lia.
  - lia.
  - right. rewrite Hspc, WL. lia.
  - intros a Ha. split.
    + right. left. split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|].
      exists hb, hn. split; [exact Hhb3 | lia].
    + destruct (al_blocks _ _ LAWS ly3 S3 W3 _ _ hb hn (proj1 HJ3) Hhb3) as (_ & _ & _ & _ & Hp & _).
      exact (proj1 (Hp a ltac:(lia))).
  - eapply (amem_range_of_block SEGS B LAWS ly3 S3 W3 _ _ hb hn); [exact (proj1 HJ3) | exact Hhb3 | lia | lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 _ _ hb hn); [exact (proj1 HJ3) | exact Hhb3 | lia | lia].
  - eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 _ _ hb hn); [exact (proj1 HJ3) | exact Hhb3 | lia | lia | lia]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & Hc4 & HJ4 & HP4 & Hra4' & Hr10' & Hfrs4 & Hperm4 & HKEPT4 & HGARR4 & HLOK4).
rewrite Rra in Hc4. subst c4.
clear Ra0 Rsp Rgp Rtp.
unfold CtrlParsed.zb in HGARR4. rewrite hi_map_zero in HGARR4.
assert (HZ5 : forall i, 0 <= i < 480 -> aview SEGS (w_H W4) mem4 (h + i) = Some 0).
{ destruct HKEPT4 as (KL1 & KL2 & KL3 & KL4 & KL5 & KL6).
  intros i Hi. destruct (Z_lt_le_dec i 400) as [Hlt | Hge].
  - replace (h + i) with (hb + (h + i - hb)) by lia.
    rewrite (KL2 hb hn (h + i - hb) Hhb3 ltac:(lia) ltac:(lia)).
    replace (hb + (h + i - hb)) with (h + i) by lia. apply HZ4. lia.
  - destruct (Z_lt_le_dec i 412) as [Hlt2 | Hge2].
    + replace (h + i) with (h + 400 + Z.of_nat (Z.to_nat (i - 400))) by lia.
      rewrite (hi_aview_garr8 W4 mem4 (h + 400) (repeat 0 12) (Z.to_nat (i - 400)) HGARR4
                 ltac:(rewrite repeat_length; lia)).
      rewrite nth_repeat by (rewrite repeat_length in *; lia). reflexivity.
    + replace (h + i) with (hb + (h + i - hb)) by lia.
      rewrite (KL2 hb hn (h + i - hb) Hhb3 ltac:(lia) ltac:(lia)).
      replace (hb + (h + i - hb)) with (h + i) by lia. apply HZ4. lia. }
hi_consts HJ4 KgotF KcellF.
reseat HS HJ4 HP4 [0; 1; 2]%nat AG
  ltac:(idtac; first
    [ eapply (region_kept_stack_aj _ _);
      [eapply hi_acall_lock; [exact HKEPT4 | lia] | exact HJ4
       | cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
       | rewrite Hspc; lia | rewrite WS; lia | lia | lia | lia]
    | apply (region_kept_val_at _ _ _ 242%nat (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
      [rewrite E242; apply unsigned_lit_small; lia | exact KgotE | exact KgotF | lia]
    | apply (region_kept_val_at _ _ _ 307%nat (VAL (A_OBJ 66)) 8 SHADOW_OFF);
      [rewrite E307; apply unsigned_lit_small; lia | exact KcellE | exact KcellF | lia] ]).
clear Hspc Hrac Rra Hh4.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (SHOK4 : sh_ok SEGS HIBx [] Ex (mrestrict (w_H W4) mem4)) by constructor end.
paj_run_tok RUN HS HJ4 SHOK4 HIspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp |].
hi_kstep K3 (spZ regs) AG Usp. clear_frames.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wc ?mc _ _ =>
  assert (HZ6 : forall i, 0 <= i < 480 -> aview SEGS (w_H Wc) mc (h + i) = Some 0) end.
{ intros i Hi. rewrite (K3 (h + i) ltac:(lia) ltac:(lia)). apply HZ5. lia. }
psrr_branch_tok RUN BR HS SHOK4 HIspan.
- lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (E11x : ew Ex 11 = Z_to_bv 64 our) by (rewrite (AG 11%nat ltac:(lia)); exact E11);
    rewrite branch_eq_U in Hc; rewrite (U_atom Ex 11 our E11x) in Hc by lia end.
  rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (Hhb4 : In (hb, hn) (ablocks B ly4 S4))
    by (apply (Permutation_in _ (Permutation_sym Hperm4)); exact Hhb3).
  hi_addblk HS AG E10 E242 E307 Usp Hhb4 HJ4 424 432.
  hi_addblk HS AG E10 E242 E307 Usp Hhb4 HJ4 440 444.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    assert (E10y : ew Ex 10 = Z_to_bv 64 h) by (rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (SHOKF : sh_ok SEGS HIBx [mkSHE 10 424 432; mkSHE 10 440 444] Ex (mrestrict (w_H W4) (ms_mem msx))) end.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - eapply (hi_shent_blk ly4 S4 W4 _ _ _ HIBx 10%nat h hb hn 424 432 (proj1 HJ4) Hhb4).
      + unfold HIBx. apply (U_atom _ 32%nat SB); [rewrite (AG 32%nat ltac:(lia)); exact E32 | unfold SB; lia].
      + apply (U_atom _ 10%nat h); [exact E10y | lia].
      + lia.
      + lia.
      + lia.
      + lia.
    - eapply (hi_shent_blk ly4 S4 W4 _ _ _ HIBx 10%nat h hb hn 440 444 (proj1 HJ4) Hhb4).
      + unfold HIBx. apply (U_atom _ 32%nat SB); [rewrite (AG 32%nat ltac:(lia)); exact E32 | unfold SB; lia].
      + apply (U_atom _ 10%nat h); [exact E10y | lia].
      + lia.
      + lia.
      + lia.
      + lia. }
  paj_run_tok RUN HS HJ4 SHOKF HIspan.
  { eapply awr_ok_cons_gen with (n := 10%nat) (b := h);
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10y; apply unsigned_lit_small; lia
    | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left;
      split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|];
      exists hb, hn; split; [exact Hhb4 | lia] | ].
    eapply awr_ok_cons_gen with (n := 10%nat) (b := h);
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10y; apply unsigned_lit_small; lia
    | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left;
      split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|];
      exists hb, hn; split; [exact Hhb4 | lia] | ].
    awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp. }
  lazymatch goal with HFx : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msF)) |- _ =>
    assert (E10f : ew Ex 10 = Z_to_bv 64 h) by (rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (HZF : forall i, 0 <= i < 480 -> ~ (424 <= i < 432) -> ~ (440 <= i < 444) ->
      aview SEGS (w_H Wx) (ms_mem msF) (h + i) = Some 0);
    [ intros i Hi Hn1 Hn2; rewrite (hi_fr_out Ex rs _ _ _ (h + i) HFx ltac:(lia));
      [ apply HZ6; lia
      | intros (rg & Hin & Hrg);
        let rs' := eval vm_compute in rs in change (In rg rs') in Hin; cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
            rewrite ?(AG 2%nat ltac:(lia)), ?(AG 10%nat ltac:(lia)) in Hrg;
            rewrite ?Usp, ?E10 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia | ]);
        destruct Hin ]
    | ] end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msF) =>
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H Wx) msF) 0
      (YP09.mkRegion (Some 10%nat) 440 444 440 444 [YP09.mkChunk 440 (CVal 4 (SLit 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR440;
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H Wx) msF) 1
      (YP09.mkRegion (Some 10%nat) 424 432 424 432 [YP09.mkChunk 424 (CVal 8 (SOff 12 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR424;
    assert (E12f : ew Ex 12 = Z_to_bv 64 now)
      by (rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat ltac:(lia)); exact E12);
    assert (E10g : ew Ex 10 = Z_to_bv 64 h)
      by (rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (HBas : bv_unsigned (ew Ex 10) = h) by (rewrite E10g; apply unsigned_lit_small; lia) end.
  cbn [ms_mem restrict] in HR440, HR424.
  pose proof (field_of_region _ _ 10%nat h _ _ _ _ _ 424 8%N (SOff 12 0) now HR424 HBas
    ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E12f, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn [Z.of_N]; lia)) as HVnow.
  pose proof (field_of_region _ _ 10%nat h _ _ _ _ _ 440 4%N (SLit 0) 0 HR440 HBas
    ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity)
    ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn [Z.of_N]; lia)) as HVz.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HVnow, HVz.
  prreg HS (1%bv : bv 5) R1f.
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR. unfold treac_hunt_init_post. apply apost_base_same_fx.
  exists ly4, S4. do 3 eexists.
  split; [cbn [ms_regs ms_mem]; rewrite R1f; rewrite ?ew_ewset_other by lia;
          rewrite (AG 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ4|].
  split.
  { apply aregs_preserved_eqs; hi_creg HS AG EE. }
  cbn [ms_mem].
  split; [|split].
  { rewrite Hc. cbn [Z.eqb]. unfold hunt_init_bytes.
    rewrite !map_app, !hi_map_zero.
    change (map (fun b : byte => bv_unsigned b) (repeat (Z_to_bv 8 0) 6)) with (repeat 0 6).
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 412 + i) with (h + (412 + i)) by lia.
      apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 412 + 6 + i) with (h + (418 + i)) by lia.
      apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { replace (h + 412 + 6 + 6) with (h + 424) by lia. apply hi_garr8_le8; [lia|exact HVnow]. }
    rewrite length_map, Mem.length_le8. hi_zn.
    replace (h + 412 + 6 + 6 + 8) with (h + 432) by lia.
    replace 48%nat with (8 + (4 + 36))%nat by reflexivity.
    rewrite (repeat_app 0 8 (4 + 36)), (repeat_app 0 4 36).
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 432 + i) with (h + (432 + i)) by lia.
      apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { replace (h + 432 + 8) with (h + 440) by lia. apply hi_garr8_z4. exact HVz. }
    rewrite repeat_length. hi_zn.
    apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 432 + 8 + 4 + i) with (h + (444 + i)) by lia.
    apply HZF; lia.
  }
  { rewrite Hc. cbn [Z.eqb]. unfold hunt_ok. split; [reflexivity|].
    split; [rewrite hi_first400; exact HTOK3|].
    split; [rewrite hi_lock12; exact HLOK4|].
    unfold s32_at, u_at, sub, hunt_init_bytes. vm_compute. split; discriminate. }
  { eapply Permutation_trans; [exact Hperm4 | exact Hperm3]. }

- lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (E11x : ew Ex 11 = Z_to_bv 64 our) by (rewrite (AG 11%nat ltac:(lia)); exact E11);
    rewrite branch_eq_U in Hc; rewrite (U_atom Ex 11 our E11x) in Hc by lia end.
  rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (HOUR Hc) as (((cid & pos & Hfin & Hcid0 & Hfal8 & Hfl & Hfh) & HO8 & HORA) & HOLEN & HOGARR).
  assert (Hhb4 : In (hb, hn) (ablocks B ly4 S4))
    by (apply (Permutation_in _ (Permutation_sym Hperm4)); exact Hhb3).
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md hb hn cid pos HAR Hhb Hfin) as Hdbf.
  unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf.
  assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr ly c p).
  { intros c p. pose proof (proj1 (proj2 HJ3)) as HL3. unfold layout_le in HL3.
    destruct HL3 as (_ & _ & _ & _ & _ & HF3 & _). unfold frame_addr. rewrite HF3. reflexivity. }
  assert (HFOUT : forall a, in_zr a (frame_rng ly (cid, pos)) \/
                    in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
                  0 <= a < 2 ^ 64 /\ ~ (spZ regs - 48 <= a < spZ regs) /\ ~ (h <= a < h + 480) /\ a < alloc_ceiling).
  { intros a Ha. destruct Ha as [Ha | Ha].
    - unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
      split; [lia|]. split; [lia|]. split; lia.
    - pose proof (hi_shadow_bound ly S W mem md cid pos a HAR Hfin Ha) as Hsb.
      pose proof (hi_shadow_off_block ly S W mem md cid pos a hb (req_size hn) HAR Hfin Ha
                    Hbh_ia Hbceil ltac:(lia)) as Hnb.
      pose proof asan_consts as (CA & _).
      unfold SHADOW_OFF in Hsb. split; [lia|]. split; [lia|]. split; lia. }
  assert (KF : forall a, in_zr a (frame_rng ly (cid, pos)) \/
                 in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
               aview SEGS (w_H W4) (ms_mem ms2) a = aview SEGS (w_H W) mem a).
  { intros a Ha. destruct (HFOUT a Ha) as (Hr1 & Hr2 & Hr3 & Hr4).
    destruct HKEPT3 as (KT1 & KT2 & KT3 & KT4 & KT5 & KT6).
    destruct HKEPT4 as (KL1 & KL2 & KL3 & KL4 & KL5 & KL6).
    rewrite (K3 a Hr1 Hr2).
    rewrite (KL4 cid pos a ltac:(rewrite Hfrs3; exact Hfin)
               ltac:(destruct Ha as [Ha | Ha]; [left; unfold frame_rng in *; cbn [fst snd] in *; rewrite EFA3; exact Ha
                                               | right; rewrite EFA3; exact Ha]) ltac:(lia)).
    rewrite (K2 a Hr1 Hr2).
    rewrite (KT4 cid pos a Hfin Ha ltac:(lia)).
    rewrite (K1 a Hr1 Hr2).
    rewrite (Hfr a Hr1 ltac:(lia) ltac:(unfold ESTACK; lia)).
    rewrite (K0 a Hr1 Hr2). reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (SHOK5 : sh_ok SEGS HIBx [] Ex (mrestrict (w_H W4) (ms_mem ms2))) by constructor end.
  paj_run_tok RUN HS HJ4 SHOK5 HIspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp |].
  hi_kstep K4 (spZ regs) AG Usp. clear_frames.
  pose proof HJ4 as (_ & HLY4 & _ & _ & _ & HFR4 & _).
  assert (Hfa4 : frame_addr ly4 cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct HLY4 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hfin4 : In (cid, pos) (frames S4)) by (rewrite HFR4; exact Hfin).
  lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc _ _ =>
    assert (KF2 : forall a, in_zr a (frame_rng ly (cid, pos)) \/
                   in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
                 aview SEGS (w_H W4) mc a = aview SEGS (w_H W) mem a)
      by (intros a Ha; destruct (HFOUT a Ha) as (Hr1 & Hr2 & _); rewrite (K4 a Hr1 Hr2); apply KF; exact Ha);
    assert (HZ6c : forall i, 0 <= i < 480 -> aview SEGS (w_H W4) mc (h + i) = Some 0)
      by (intros i Hi; rewrite (K4 (h + i) ltac:(lia) ltac:(lia)); apply HZ6; lia) end.
  assert (HOBV : forall a, our <= a < our + 6 -> aview SEGS (w_H W4) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KF2; left; unfold in_zr, frame_rng; cbn [fst snd]; lia).
  assert (HOBS : forall x, our <= x < our + 6 ->
      aview SEGS (w_H W4) (ms_mem ms3) (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x))
    by (intros x Hx; apply KF2; right; exact (hi_shadow_in_frame ly S W mem md cid pos our 6 x HAR Hfin Hfl Hfh Hx)).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  pmkst HS.
  hi_consts HJ4 KgotG KcellG.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
    eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA DS___asan_memcpy) (AMEMCPY fq) W4 (ms_regs msX) (ms_mem msX)
      REAC_HUNT_INIT_STK (spZ regs) [(h, h + 480)] ly S W mem md [] ly4 S4 mdX 0 (h + 412) our 6 (-48) _ HJ4) end.
    - rewrite Ra0, (AG 10%nat ltac:(lia)), E10, unsigned_lit_small by lia. reflexivity.
    - rewrite Ra1, (AG 11%nat ltac:(lia)). exact E11.
    - exact Ra2.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Rsp, (AG 2%nat ltac:(lia)), Usp. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - rewrite WS, WE. lia.
    - rewrite Rgp, (AG 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rtp, (AG 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right. left. split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists hb, hn. split; [exact Hhb4 | lia].
      + unfold ESTACK. lia.
    - eapply (amem_range_of_block SEGS B LAWS ly4 S4 W4 _ _ hb hn); [exact (proj1 HJ4) | exact Hhb4 | lia | lia].
    - eapply (range_addressable_of_block SEGS B LAWS ly4 S4 W4 _ _ hb hn); [exact (proj1 HJ4) | exact Hhb4 | lia | lia].
    - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 W4 _ _ hb hn); [exact (proj1 HJ4) | exact Hhb4 | lia | lia | lia].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - rewrite (HOBV a Ha). replace a with (our + Z.of_nat (Z.to_nat (a - our))) by lia.
          rewrite (hi_aview_garr8 W mem our _ (Z.to_nat (a - our)) HOGARR) by (rewrite length_map, HOLEN; lia). discriminate.
        - unfold spZ at 1. rewrite Rsp, (AG 2%nat ltac:(lia)), Usp, unsigned_lit_small by lia. unfold ESTACK. lia. }
      split; [lia|]. split.
      { eapply amem_range_sub_app; [exact Hfapp | exact Hfceil | exact Hfl | exact Hfh | lia]. }
      split; [exact (hi_ra_kept _ _ our 6 HOBS HORA)|].
      intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 _ _ cid pos);
        [exact (proj1 HJ4) | exact Hfin4 | rewrite Hfa4; lia | rewrite Hfa4; lia | lia]. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & Hsame5).
  clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
  assert (HZ7 : forall i, 0 <= i < 480 -> ~ (412 <= i < 418) -> aview SEGS (w_H W4) mem5 (h + i) = Some 0).
  { intros i Hi Hni. rewrite (Hfr5 (h + i) ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)). apply HZ6c. lia. }
  assert (HOB7 : forall j, (j < 6)%nat -> aview SEGS (w_H W4) mem5 (h + 412 + Z.of_nat j) = aview SEGS (w_H W) mem (our + Z.of_nat j)).
  { intros j Hj. rewrite (Heff5 (Z.of_nat j) ltac:(lia)). apply HOBV. lia. }
  hi_consts HJ5 KgotH KcellH.
  reseat HS HJ5 HP5 [0; 1; 2]%nat AG
    ltac:(idtac; first
      [ eapply region_kept_aview; [cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp
        | intros a Ha; apply Hfr5; unfold ESTACK; lia | exact Hpres5]
      | apply (region_kept_val_at _ _ _ 242%nat (VAL (A_OBJ 1)) 8 (VAL (A_OBJ 66)));
        [rewrite E242; apply unsigned_lit_small; lia | exact KgotG | exact KgotH | lia]
      | apply (region_kept_val_at _ _ _ 307%nat (VAL (A_OBJ 66)) 8 SHADOW_OFF);
        [rewrite E307; apply unsigned_lit_small; lia | exact KcellG | exact KcellH | lia] ]).
  hi_addblk HS AG E10 E242 E307 Usp Hhb4 HJ5 424 432.
  hi_addblk HS AG E10 E242 E307 Usp Hhb4 HJ5 440 444.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    assert (E10y : ew Ex 10 = Z_to_bv 64 h) by (rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (SHOKF : sh_ok SEGS HIBx [mkSHE 10 424 432; mkSHE 10 440 444] Ex (mrestrict (w_H W4) (ms_mem msx))) end.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - eapply (hi_shent_blk ly4 S4 W4 _ _ _ HIBx 10%nat h hb hn 424 432 (proj1 HJ5) Hhb4).
      + unfold HIBx. apply (U_atom _ 32%nat SB); [rewrite (AG 32%nat ltac:(lia)); exact E32 | unfold SB; lia].
      + apply (U_atom _ 10%nat h); [exact E10y | lia].
      + lia.
      + lia.
      + lia.
      + lia.
    - eapply (hi_shent_blk ly4 S4 W4 _ _ _ HIBx 10%nat h hb hn 440 444 (proj1 HJ5) Hhb4).
      + unfold HIBx. apply (U_atom _ 32%nat SB); [rewrite (AG 32%nat ltac:(lia)); exact E32 | unfold SB; lia].
      + apply (U_atom _ 10%nat h); [exact E10y | lia].
      + lia.
      + lia.
      + lia.
      + lia. }
  paj_run_tok RUN HS HJ5 SHOKF HIspan.
  { eapply awr_ok_cons_gen with (n := 10%nat) (b := h);
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10y; apply unsigned_lit_small; lia
    | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left;
      split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|];
      exists hb, hn; split; [exact Hhb4 | lia] | ].
    eapply awr_ok_cons_gen with (n := 10%nat) (b := h);
    [reflexivity | cbn [ew ewset Nat.eqb]; rewrite E10y; apply unsigned_lit_small; lia
    | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left;
      split; [exists (h, h + 480); split; [left; reflexivity | cbn [fst snd]; lia]|];
      exists hb, hn; split; [exact Hhb4 | lia] | ].
    awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?(AG 2%nat) by lia; exact Usp. }
  lazymatch goal with HFx : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m0) (mrestrict _ (ms_mem ?msF)) |- _ =>
    assert (E10f : ew Ex 10 = Z_to_bv 64 h) by (rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (HFO : forall i, 0 <= i < 480 -> ~ (424 <= i < 432) -> ~ (440 <= i < 444) ->
      aview SEGS (w_H Wx) (ms_mem msF) (h + i) = aview SEGS (w_H Wx) m0 (h + i));
    [ intros i Hi Hn1 Hn2; apply (hi_fr_out Ex rs _ _ _ (h + i) HFx ltac:(lia));
        intros (rg & Hin & Hrg);
        let rs' := eval vm_compute in rs in change (In rg rs') in Hin; cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
            rewrite ?(AG 2%nat ltac:(lia)), ?(AG 10%nat ltac:(lia)) in Hrg;
            rewrite ?Usp, ?E10 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia | ]);
        destruct Hin
    | ] end.
  lazymatch type of HFO with forall i, _ -> _ -> _ -> aview SEGS (w_H ?Wx) ?mF _ = _ =>
    assert (HZF : forall i, 0 <= i < 480 -> ~ (424 <= i < 432) -> ~ (440 <= i < 444) -> ~ (412 <= i < 418) ->
      aview SEGS (w_H Wx) mF (h + i) = Some 0)
      by (intros i Hi Hn1 Hn2 Hn3; rewrite (HFO i Hi Hn1 Hn2); apply HZ7; lia);
    assert (HOBF : forall j, (j < 6)%nat ->
      aview SEGS (w_H Wx) mF (h + 412 + Z.of_nat j) = aview SEGS (w_H W) mem (our + Z.of_nat j))
      by (intros j Hj; replace (h + 412 + Z.of_nat j) with (h + (412 + Z.of_nat j)) by lia;
          rewrite (HFO (412 + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia));
          replace (h + (412 + Z.of_nat j)) with (h + 412 + Z.of_nat j) by lia; apply HOB7; exact Hj) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict (w_H ?Wx) ?msF) =>
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H Wx) msF) 0
      (YP09.mkRegion (Some 10%nat) 440 444 440 444 [YP09.mkChunk 440 (CVal 4 (SLit 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR440;
    pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H Wx) msF) 1
      (YP09.mkRegion (Some 10%nat) 424 432 424 432 [YP09.mkChunk 424 (CVal 8 (SOff 12 0))]) HS
      ltac:(vm_compute; reflexivity)) as HR424;
    assert (E12f : ew Ex 12 = Z_to_bv 64 now)
      by (rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat ltac:(lia)); exact E12);
    assert (E10g : ew Ex 10 = Z_to_bv 64 h)
      by (rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat ltac:(lia)); exact E10);
    assert (HBas : bv_unsigned (ew Ex 10) = h) by (rewrite E10g; apply unsigned_lit_small; lia) end.
  cbn [ms_mem restrict] in HR440, HR424.
  pose proof (field_of_region _ _ 10%nat h _ _ _ _ _ 424 8%N (SOff 12 0) now HR424 HBas
    ltac:(cbn [In]; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E12f, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn [Z.of_N]; lia)) as HVnow.
  pose proof (field_of_region _ _ 10%nat h _ _ _ _ _ 440 4%N (SLit 0) 0 HR440 HBas
    ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity)
    ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn [Z.of_N]; lia)) as HVz.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HVnow, HVz.
  prreg HS (1%bv : bv 5) R1f.
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matR. unfold treac_hunt_init_post. apply apost_base_same_fx.
  exists ly4, S4. do 3 eexists.
  split; [cbn [ms_regs ms_mem]; rewrite R1f; rewrite ?ew_ewset_other by lia;
          rewrite (AG 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ5|].
  split.
  { apply aregs_preserved_eqs; hi_creg HS AG EE. }
  cbn [ms_mem].
  assert (Hc0 : (our =? 0) = false) by (apply Z.eqb_neq; exact Hc).
  split; [|split].
  { rewrite Hc0. unfold hunt_init_bytes.
    rewrite !map_app, !hi_map_zero.
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { apply (hi_garr8_copy W mem W4 _ our (h + 412) _ HOGARR).
      intros j Hj. rewrite length_map, HOLEN in Hj. apply HOBF. exact Hj. }
    rewrite length_map, HOLEN. hi_zn.
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 412 + 6 + i) with (h + (418 + i)) by lia.
      apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { replace (h + 412 + 6 + 6) with (h + 424) by lia. apply hi_garr8_le8; [lia|exact HVnow]. }
    rewrite length_map, Mem.length_le8. hi_zn.
    replace (h + 412 + 6 + 6 + 8) with (h + 432) by lia.
    replace 48%nat with (8 + (4 + 36))%nat by reflexivity.
    rewrite (repeat_app 0 8 (4 + 36)), (repeat_app 0 4 36).
    apply garr8_app. split.
    { apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 432 + i) with (h + (432 + i)) by lia.
      apply HZF; lia. }
    rewrite repeat_length. hi_zn.
    apply garr8_app. split.
    { replace (h + 432 + 8) with (h + 440) by lia. apply hi_garr8_z4. exact HVz. }
    rewrite repeat_length. hi_zn.
    apply hi_garr8_zeros. intros i Hi. hi_zn. replace (h + 432 + 8 + 4 + i) with (h + (444 + i)) by lia.
    apply HZF; lia. }
  { rewrite Hc0. unfold hunt_ok.
    destruct ob as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 ob']]]]]]]; cbn [length] in HOLEN; try discriminate HOLEN.
    split; [reflexivity|].
    split; [rewrite hi_first400; exact HTOK3|].
    split; [rewrite hi_lock12; exact HLOK4|].
    match goal with |- context [s32_at ?H 440] => replace (s32_at H 440) with 0 by (vm_compute; reflexivity) end. lia. }
  { eapply Permutation_trans; [exact Hperm4 | exact Hperm3]. }

Qed.
End h.
End f.
End d.
