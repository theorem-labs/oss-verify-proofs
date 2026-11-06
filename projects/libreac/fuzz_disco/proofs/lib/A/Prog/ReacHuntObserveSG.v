(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 747 of its 778 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacHuntObserveSeg.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma hoG_nth_sub : forall (L : list byte) k n i, 0 <= k -> (i < n)%nat ->
  nth_error (disco_table_c.sub L k n) i = nth_error L (Z.to_nat k + i).
Proof.
intros L k n i Hk Hi. unfold disco_table_c.sub. rewrite nth_error_firstn.
destruct (Nat.ltb_spec i n) as [_|]; [|lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma hoG_mac_bytes : forall (T G : list byte) j, length T = 400%nat -> length G = 24%nat -> 0 <= j < 8 ->
  (disco_table_c.mac_of T j = disco_table_c.s_mac G <->
   forall i, 0 <= i < 6 -> nth_error T (Z.to_nat (48 * j + i)) = nth_error G (Z.to_nat i)).
Proof.
intros T G j LT LG Hj. unfold disco_table_c.mac_of, disco_table_c.s_mac.
assert (L1 : length (disco_table_c.sub T (48 * j) 6) = 6%nat) by (apply HuntObsLib.len_sub; lia).
assert (L2 : length (disco_table_c.sub G 0 6) = 6%nat) by (apply HuntObsLib.len_sub; lia).
split.
- intros E i Hi.
  assert (E' : nth_error (disco_table_c.sub T (48 * j) 6) (Z.to_nat i)
             = nth_error (disco_table_c.sub G 0 6) (Z.to_nat i)) by (rewrite E; reflexivity).
  rewrite !hoG_nth_sub in E' by lia.
  replace (Z.to_nat (48 * j + i)) with (Z.to_nat (48 * j) + Z.to_nat i)%nat by lia.
  rewrite E'. f_equal; lia.
- intros HI. apply nth_error_ext. intros i.
  destruct (Nat.ltb_spec i 6) as [Hi | Hi].
  + rewrite !hoG_nth_sub by lia.
    pose proof (HI (Z.of_nat i) ltac:(lia)) as Hi'. rewrite Nat2Z.id in Hi'.
    replace (Z.to_nat (48 * j) + i)%nat with (Z.to_nat (48 * j + Z.of_nat i)) by lia.
    rewrite Hi'. f_equal; lia.
  + assert (Z1 : nth_error (disco_table_c.sub T (48 * j) 6) i = None) by (apply nth_error_None; lia).
    assert (Z2 : nth_error (disco_table_c.sub G 0 6) i = None) by (apply nth_error_None; lia).
    rewrite Z1, Z2. reflexivity.
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

Definition hoG_E (regs : bvmap 5 word) : env := Eimg (Ereg regs (map (Z_to_bv 64) [SB])).
Definition hoG_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma hoG_regs_ok : forall regs, regs_ok (hoG_E regs) sr_atoms regs.
Proof.
intros regs. unfold hoG_E. apply (regs_ok_agree 32 (Ereg regs (map (Z_to_bv 64) [SB]))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.

Lemma hoG_env_img : forall regs, img_env VAL A_LIM (hoG_E regs).
Proof. intros regs. unfold hoG_E. apply Eimg_env. Qed.

Lemma hoG_env_agree : forall regs, env_agree 32 (Ereg regs (map (Z_to_bv 64) [SB])) (hoG_E regs).
Proof. intros regs. split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma hoG_env_reg : forall regs n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (hoG_E regs) n = getr regs x.
Proof.
intros regs n x Hn. unfold hoG_E. pose proof (u5_range x) as Hx.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n x Hn).
Qed.

Lemma hoG_enter : forall (fq : YK11.FPState) (regs : bvmap 5 word) (W : world SEGS) mem pc,
  st_ok_pi SEGS VAL (hoG_E regs) (hoG_ss pc)
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS HOx [] (hoG_E regs) (mrestrict (w_H W) mem).
Proof.
intros fq regs W mem pc. rewrite restrict_mkst_fx. split.
- unfold hoG_ss. apply pa_entry_st_ok_full.
  + apply hoG_regs_ok.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Lemma hoG_val_kept : forall (W : world SEGS) ma mb a n v,
  (forall i, a <= i < a + Z.of_nat n -> aview SEGS (w_H W) mb i = aview SEGS (w_H W) ma i) ->
  val_mem SEGS (mrestrict (w_H W) ma) a n v -> val_mem SEGS (mrestrict (w_H W) mb) a n v.
Proof.
intros W ma mb a n v HE HV k Hk. rewrite <- (HV k Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Lemma hoG_model_mono : forall (H FB O : list byte) len now out r (H' : list byte) (P Q : list byte -> Prop),
  (forall A, P A -> Q A) ->
  tho_model H FB O len now out r H' P -> tho_model H FB O len now out r H' Q.
Proof.
intros H FB O len now out r H' P Q HPQ (H1 & H2). split.
- intros Hc. destruct (H1 Hc) as (Ha & Hb & Hd). split; [exact Ha|]. split; [exact Hb|].
  intros Ho. apply HPQ. exact (Hd Ho).
- intros Hc. destruct (H2 Hc) as (Tx & cc & Hm & Hrr & Hh & Hd). exists Tx, cc.
  split; [exact Hm|]. split; [exact Hrr|]. split; [exact Hh|].
  intros Ho. destruct (Hd Ho) as (A & Ha1 & Ha2 & Ha3). exists A.
  split; [exact Ha1|]. split; [apply HPQ; exact Ha2 | exact Ha3].
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).

Definition hoG_ctx (c : hoC) (fpos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (md2 : Model) (k2 : Z) (H2 T' G : list byte)
  (regs2 : bvmap 5 word) (sp1 F r nn ii : Z) : Prop :=
  ho_base B c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F /\
  getr regs2 20 = w64 r /\ (r = 0 \/ r = 1) /\
  getr regs2 19 = w64 (48 * nn) /\
  getr regs2 23 = w64 (F + 32) /\ getr regs2 25 = w64 (SB + F / 8) /\
  ho_fsh W2 mem2 F ho_shC /\
  hunt_c.hunt_ok H2 /\ H2 = T' ++ skipn 400 H2 /\ length T' = 400%nat /\
  nn = disco_table_c.n_of T' /\ 0 <= nn <= 8 /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32) (map (fun b : byte => bv_unsigned b) G) /\
  length G = 24%nat /\
  (forall j, 0 <= j < ii -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G) /\
  c_out c <> 0 /\
  rdword (aview SEGS (w_H W2) mem2) (sp1 + 24) = Some (c_out c) /\
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) G) /\
  (forall A, reac_hunt_observe_c.ho_answer T' G A ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = A)).

Lemma hoG_pre_facts : forall c, ho_pre B c ->
  spZ (c_regs c) mod 16 = 0 /\
  c_sp0 c - c_STK c <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\
  spZ (c_regs c) <= c_sp0 c /\ 0 < c_h c /\ c_h c mod 8 = 0 /\
  In (c_hb c, c_hn c) (ablocks B (c_lyc c) (c_Sc c)) /\ c_hb c <= c_h c /\
  c_h c + 480 <= c_hb c + req_size (c_hn c) /\
  getr (c_regs c) 3 = w64 (as_gp B) /\ getr (c_regs c) 4 = w64 (as_tp B) /\
  hunt_c.hunt_ok (c_H c) /\ 0 <= c_out c < 2 ^ 64 /\
  (c_out c <> 0 -> tho_out B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_own c)
     (c_lyc c) (c_Sc c) (c_W c) (c_memc c) (spZ (c_regs c)) (c_out c) (c_O c)) /\
  (exists mdc, ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
     (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc (c_k c)).
Proof. intros c HP. unfold ho_pre in HP. tauto. Qed.

Lemma hoG_band : forall c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base B c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  YM05.alloc_ceiling <= sp1 - 2 * ESTACK /\
  spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= sp1 - 2 * ESTACK /\
  sp1 + 160 <= spZ (c_regs c) /\ spZ (c_regs c) <= c_sp0 c /\
  sp1 mod 32 = 0 /\ c_sp0 c mod 16 = 0 /\
  2 * ESTACK - (sp1 - c_sp0 c) <= c_STK c /\ 4096 <= F /\ F + 128 <= YM05.alloc_ceiling /\
  F mod 32 = 0 /\ c_sp0 c <= 2 ^ 47 /\ in_app F 128.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (HP & HM & HSP & HFA & HRM & HSV).
destruct HM as (HJ & HFrS & HFad & HPerm & HKept & HGH2 & HFlag & HH2l).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct (hoG_pre_facts c HP) as (Hal16 & Hwin & Hsp & _).
destruct HSP as (Hsp1v & Hsp1r & Hsp1al).
assert (Hfr : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HinF : In (1, fpos) (frames S2)) by (rewrite HFrS; left; reflexivity).
destruct (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos HAR2 HinF) as (HF1 & HF2 & HF3).
rewrite HFad in HF1, HF2, HF3. rewrite <- HFA in HF1, HF2, HF3.
assert (HFbytes : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFbytes in HF2, HF3.
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos HAR2 HinF) as (HFal & _).
rewrite HFad in HFal. rewrite <- HFA in HFal.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia | exact HF3].
Qed.

Lemma hoG_out_win : forall c, ho_pre B c -> c_out c <> 0 ->
  (spZ (c_regs c) <= c_out c \/ c_out c + 24 <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK) /\
  c_out c + 24 <= 2 ^ 63.
Proof.
intros c HP Hne.
destruct (hoG_pre_facts c HP) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTO & _).
specialize (HTO Hne). unfold tho_out in HTO. tauto.
Qed.

Lemma hoG_step_mem : forall c fpos ly2 S2 W2 ma mda ka mb mdb H2 T' G ra rb sp1 F r nn ii,
  hoG_ctx c fpos ly2 S2 W2 ma mda ka H2 T' G ra sp1 F r nn ii ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mb mdb ka ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
     aview SEGS (w_H W2) mb a = aview SEGS (w_H W2) ma a) ->
  (forall a, apresent (w_H W2) ma a -> apresent (w_H W2) mb a) ->
  (forall q : bv 5, In q [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv ->
     getr rb q = getr ra q) ->
  hoG_ctx c fpos ly2 S2 W2 mb mdb ka H2 T' G rb sp1 F r nn ii.
Proof.
intros c fpos ly2 S2 W2 ma mda ka mb mdb H2 T' G ra rb sp1 F r nn ii
  (HB & R20 & Hr01 & R19 & R23 & R25 & HFSH & HOK & HT2 & HTl & Hnneq & Hnn8 & HGg & HGl & Hmis
   & Hout0 & Hrd & HGo & HCl) HJb HKeep HPres HRp.
pose proof HB as (HP & HM & HSP & HFA & HRM & HSV).
destruct (hoG_band c fpos ly2 S2 W2 ma mda ka H2 ra sp1 F HB)
  as (KC & KW & KS1 & KS0 & KA32 & KA16 & KSTK & KF1 & KF2 & KF4 & KSP47 & KF3).
destruct (hoG_pre_facts c HP)
  as (Hal16 & Hwin & Hsp & Hh0 & Hh8 & Hin & Hhb & Hhe & Hgp & Htp & HOKH & Hout64 & HTO & HJE).
destruct HJE as (mdc & HJc).
pose proof HJc as (HARc & _).
pose proof asan_consts as (CAC & _).
destruct (hoG_out_win c HP Hout0) as (HOW & HO63).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfr : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (Hsb : SB = 2147450880) by reflexivity.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> (a < sp1 - 2 * ESTACK \/ sp1 <= a) ->
  aview SEGS (w_H W2) mb a = aview SEGS (w_H W2) ma a)
  by (intros a Ha Hd; apply HKeep; [exact Ha | lia]).
destruct (al_blocks _ _ LAWS (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc (c_hb c) (c_hn c) HARc Hin)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
destruct HM as (HJa & HFrS & HFad & HPerm & HKept & HGH2 & HFlag & HH2l).
destruct HKept as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HH2len : length H2 = 480%nat) by (destruct HOK as (HL & _); exact HL).
split.
{ split; [exact HP|]. split.
  { split; [exact HJb|]. split; [exact HFrS|]. split; [exact HFad|]. split; [exact HPerm|].
    split.
    { split.
      { intros a Ha1 Ha2 Ha3.
        assert (HA1 : 0 <= a < 2 ^ 64) by (clear - Hes Ha1 CAC; lia).
        assert (HD1 : a < sp1 - 2 * ESTACK \/ sp1 <= a) by (clear - Hes Ha2 KW KS1; lia).
        rewrite (KEEP a HA1 HD1). exact (K1 a Ha1 Ha2 Ha3). }
      split.
      { intros b m i Hbm Hi Hw.
        destruct (al_blocks _ _ LAWS (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc b m HARc Hbm)
          as (_ & Hq4 & Hqc & _).
        assert (HA2 : 0 <= b + i < 2 ^ 64) by (clear - Hes Hq4 Hqc Hi CAC; lia).
        assert (HD2 : b + i < sp1 - 2 * ESTACK \/ sp1 <= b + i)
          by (clear - Hes Hq4 Hqc Hi CAC KC; lia).
        rewrite (KEEP (b + i) HA2 HD2). exact (K2 b m i Hbm Hi Hw). }
      split.
      { intros a Hi Ho He. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
        assert (HA3 : 0 <= a < 2 ^ 64) by (clear - Hes Hlow; lia).
        assert (HD3 : a < sp1 - 2 * ESTACK \/ sp1 <= a) by (clear - Hes Hlow CAC KC; lia).
        rewrite (KEEP a HA3 HD3). exact (K3 a Hi Ho He). }
      split.
      { intros cid pos a Hf Hzr Hw.
        destruct (frames_bounds _ _ LAWS (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc cid pos HARc Hf)
          as (Hf1 & Hf2 & Hf3).
        pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
        assert (Hain : 0 <= a < sp1 - 2 * ESTACK).
        { destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; clear - Hes Hzr Hf1 Hf2 Hfs0 CAC KC; lia. }
        assert (HA4 : 0 <= a < 2 ^ 64) by (clear - Hes Hain CAC KC KS1 KS0 KSP47; lia).
        assert (HD4 : a < sp1 - 2 * ESTACK \/ sp1 <= a) by (clear - Hes Hain; lia).
        rewrite (KEEP a HA4 HD4). exact (K4 cid pos a Hf Hzr Hw). }
      split.
      { intros a Ha1 Ha2 Hpr. apply HPres. exact (K5 a Ha1 Ha2 Hpr). }
      { intros a Ha. apply HPres. exact (K6 a Ha). } }
    split.
    { apply (ho_garr_kept W2 W2 ma mb (c_h c)); [|exact HGH2].
      intros i Hi. rewrite length_map, HH2len in Hi. apply KEEP;
      [ clear - Hes Hi Hh0 Hhb Hhe Hbceil CAC; lia | clear - Hes Hi Hh0 Hhb Hhe Hbceil CAC KC; lia ]. }
    split.
    { assert (HFB : forall x, F + 120 <= x <= F + 127 ->
        0 <= x < 2 ^ 64 /\ (x < sp1 - 2 * ESTACK \/ sp1 <= x))
        by (intros x Hx; split;
            [clear - Hes Hx KF1 KF2 CAC; lia | clear - Hes Hx KF1 KF2 CAC KC; lia]).
      rewrite <- HFA. unfold rdword.
      rewrite (KEEP (F + 120) (proj1 (HFB (F + 120) ltac:(lia))) (proj2 (HFB (F + 120) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 1) (proj1 (HFB (F + 120 + 1) ltac:(lia))) (proj2 (HFB (F + 120 + 1) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 2) (proj1 (HFB (F + 120 + 2) ltac:(lia))) (proj2 (HFB (F + 120 + 2) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 3) (proj1 (HFB (F + 120 + 3) ltac:(lia))) (proj2 (HFB (F + 120 + 3) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 4) (proj1 (HFB (F + 120 + 4) ltac:(lia))) (proj2 (HFB (F + 120 + 4) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 5) (proj1 (HFB (F + 120 + 5) ltac:(lia))) (proj2 (HFB (F + 120 + 5) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 6) (proj1 (HFB (F + 120 + 6) ltac:(lia))) (proj2 (HFB (F + 120 + 6) ltac:(lia)))).
      rewrite (KEEP (F + 120 + 7) (proj1 (HFB (F + 120 + 7) ltac:(lia))) (proj2 (HFB (F + 120 + 7) ltac:(lia)))).
      rewrite HFA. exact HFlag. }
    exact HH2l. }
  split; [exact HSP|]. split; [exact HFA|]. split.
  { destruct HRM as (M2 & M3 & M4 & M8 & M9 & M18 & M22 & M26 & M27).
    split; [etransitivity; [exact (HRp 2%bv ltac:(cbn [In]; auto 20)) | exact M2]|].
    split; [etransitivity; [exact (HRp 3%bv ltac:(cbn [In]; auto 20)) | exact M3]|].
    split; [etransitivity; [exact (HRp 4%bv ltac:(cbn [In]; auto 20)) | exact M4]|].
    split; [etransitivity; [exact (HRp 8%bv ltac:(cbn [In]; auto 20)) | exact M8]|].
    split; [etransitivity; [exact (HRp 9%bv ltac:(cbn [In]; auto 20)) | exact M9]|].
    split; [etransitivity; [exact (HRp 18%bv ltac:(cbn [In]; auto 20)) | exact M18]|].
    split; [etransitivity; [exact (HRp 22%bv ltac:(cbn [In]; auto 20)) | exact M22]|].
    split; [etransitivity; [exact (HRp 26%bv ltac:(cbn [In]; auto 20)) | exact M26]|].
    etransitivity; [exact (HRp 27%bv ltac:(cbn [In]; auto 20)) | exact M27]. }
  { intros j Hj. apply (hoG_val_kept W2 ma mb); [|exact (HSV j Hj)].
    intros i Hi. apply KEEP;
    [ clear - Hes Hi Hj KS1 KS0 KSP47 KC CAC; lia | clear - Hes Hi Hj KS1; lia ]. } }
split; [etransitivity; [exact (HRp 20%bv ltac:(cbn [In]; auto 20)) | exact R20]|].
split; [exact Hr01|].
split; [etransitivity; [exact (HRp 19%bv ltac:(cbn [In]; auto 20)) | exact R19]|].
split; [etransitivity; [exact (HRp 23%bv ltac:(cbn [In]; auto 20)) | exact R23]|].
split; [etransitivity; [exact (HRp 25%bv ltac:(cbn [In]; auto 20)) | exact R25]|].
split.
{ intros i Hi. apply (eq_trans (KEEP (SB + F / 8 + i)
    ltac:(clear - Hes Hi KF1 KF2 Hsb CAC; lia) ltac:(clear - Hes Hi KF1 KF2 Hsb CAC KC; lia)) (HFSH i Hi)). }
split; [exact HOK|]. split; [exact HT2|]. split; [exact HTl|].
split; [exact Hnneq|]. split; [exact Hnn8|].
split.
{ apply (ho_garr_kept W2 W2 ma mb (F + 32)); [|exact HGg].
  intros i Hi. rewrite length_map, HGl in Hi. apply KEEP;
  [ clear - Hes Hi KF1 KF2 CAC; lia | clear - Hes Hi KF1 KF2 CAC KC; lia ]. }
split; [exact HGl|]. split; [exact Hmis|]. split; [exact Hout0|].
split.
{ assert (HSPB : forall x, sp1 + 24 <= x <= sp1 + 31 ->
    0 <= x < 2 ^ 64 /\ (x < sp1 - 2 * ESTACK \/ sp1 <= x))
    by (intros x Hx; split;
        [clear - Hes Hx KC KS1 KS0 KSP47 CAC; lia | clear - Hes Hx; lia]).
  unfold rdword.
  rewrite (KEEP (sp1 + 24) (proj1 (HSPB (sp1 + 24) ltac:(lia))) (proj2 (HSPB (sp1 + 24) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 1) (proj1 (HSPB (sp1 + 24 + 1) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 1) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 2) (proj1 (HSPB (sp1 + 24 + 2) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 2) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 3) (proj1 (HSPB (sp1 + 24 + 3) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 3) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 4) (proj1 (HSPB (sp1 + 24 + 4) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 4) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 5) (proj1 (HSPB (sp1 + 24 + 5) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 5) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 6) (proj1 (HSPB (sp1 + 24 + 6) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 6) ltac:(lia)))).
  rewrite (KEEP (sp1 + 24 + 7) (proj1 (HSPB (sp1 + 24 + 7) ltac:(lia))) (proj2 (HSPB (sp1 + 24 + 7) ltac:(lia)))).
  exact Hrd. }
split.
{ apply (ho_garr_kept W2 W2 ma mb (c_out c)); [|exact HGo].
  intros i Hi. rewrite length_map, HGl in Hi. apply KEEP;
  [ clear - Hes Hi Hout64 HO63; lia | clear - Hes Hi HOW KW KS1 HO63; lia ]. }
exact HCl.
Qed.

Lemma hoG_hull_sub : forall (rd : Z -> option Z) x n y k, shadow_hull_vis rd x n -> x <= y -> y + k <= x + n ->
  0 < k -> 0 <= x -> shadow_hull_vis rd y k.
Proof.
intros rd x n y k H Hxy Hyk Hk Hx s Hs. apply H. unfold shadow_addr in *.
assert (A1 : x / 8 <= y / 8) by (apply Z.div_le_mono; lia).
assert (A2 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + y / 8) / 8) by (apply Z.div_le_mono; lia).
assert (A3 : (y + k - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (A4 : (SHADOW_OFF + (y + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma hoG_aview_nth : forall (W : world SEGS) m p (L : list byte) k,
  garr8 SEGS (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) L) -> (k < length L)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat k) = option_map (fun b : byte => bv_unsigned b) (nth_error L k).
Proof.
intros W m p L k HG Hk.
unfold aview. rewrite (garr8_mbyte SEGS _ p _ k HG) by (rewrite length_map; exact Hk).
rewrite (nth_error_nth' L (Z_to_bv 8 0) Hk). cbn [option_map].
rewrite (nth_indep (map (fun b : byte => bv_unsigned b) L) 0 (bv_unsigned (Z_to_bv 8 0)))
  by (rewrite length_map; exact Hk).
rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hoG_cmp : forall (W : world SEGS) m x y (H2 T' G : list byte) ii,
  garr8 SEGS (mrestrict (w_H W) m) x (map (fun b : byte => bv_unsigned b) H2) ->
  garr8 SEGS (mrestrict (w_H W) m) y (map (fun b : byte => bv_unsigned b) G) ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat -> length G = 24%nat -> 0 <= ii < 8 ->
  ((forall i, 0 <= i < 6 -> aview SEGS (w_H W) m (x + 48 * ii + i) = aview SEGS (w_H W) m (y + i)) <->
   disco_table_c.mac_of T' ii = disco_table_c.s_mac G).
Proof.
intros W m x y H2 T' G ii HH HG HT HTl HGl Hii.
rewrite (hoG_mac_bytes T' G ii HTl HGl Hii).
assert (HL2 : (400 <= length H2)%nat) by (rewrite HT, length_app; lia).
assert (HN : forall k, (k < 400)%nat -> nth_error H2 k = nth_error T' k).
{ intros k Hk. rewrite HT at 1. apply nth_error_app1. lia. }
assert (E : forall i, 0 <= i < 6 ->
  (aview SEGS (w_H W) m (x + 48 * ii + i) = aview SEGS (w_H W) m (y + i) <->
   nth_error T' (Z.to_nat (48 * ii + i)) = nth_error G (Z.to_nat i))).
{ intros i Hi.
  replace (x + 48 * ii + i) with (x + Z.of_nat (Z.to_nat (48 * ii + i))) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (hoG_aview_nth W m x H2 _ HH) by lia.
  rewrite (hoG_aview_nth W m y G _ HG) by lia.
  assert (K1 : (Z.to_nat (48 * ii + i) < 400)%nat) by lia.
  assert (K2 : (Z.to_nat (48 * ii + i) < length T')%nat) by lia.
  assert (K3 : (Z.to_nat i < length G)%nat) by lia.
  rewrite (HN _ K1).
  rewrite (nth_error_nth' T' (Z_to_bv 8 0) K2), (nth_error_nth' G (Z_to_bv 8 0) K3).
  cbn [option_map].
  split; intros Q; injection Q as Q; [f_equal; apply bv_eq; exact Q | rewrite Q; reflexivity]. }
split; intros HA i Hi; [apply (proj1 (E i Hi)) | apply (proj2 (E i Hi))]; exact (HA i Hi).
Qed.

Lemma hoG_pres_list : forall ra rb, aregs_preserved ra rb ->
  forall q : bv 5, In q [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> getr rb q = getr ra q.
Proof.
intros ra rb HP q Hq. cbn [In] in Hq.
destruct Hq as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]].
- exact (HP 2 ltac:(unfold acallee_saved; lia)).
- exact (HP 3 ltac:(unfold acallee_saved; lia)).
- exact (HP 4 ltac:(unfold acallee_saved; lia)).
- exact (HP 8 ltac:(unfold acallee_saved; lia)).
- exact (HP 9 ltac:(unfold acallee_saved; lia)).
- exact (HP 18 ltac:(unfold acallee_saved; lia)).
- exact (HP 19 ltac:(unfold acallee_saved; lia)).
- exact (HP 20 ltac:(unfold acallee_saved; lia)).
- exact (HP 22 ltac:(unfold acallee_saved; lia)).
- exact (HP 23 ltac:(unfold acallee_saved; lia)).
- exact (HP 25 ltac:(unfold acallee_saved; lia)).
- exact (HP 26 ltac:(unfold acallee_saved; lia)).
- exact (HP 27 ltac:(unfold acallee_saved; lia)).
Qed.

Lemma hoG_garr_some : forall (W : world SEGS) m p l a,
  garr8 SEGS (mrestrict (w_H W) m) p l -> p <= a < p + Z.of_nat (length l) ->
  aview SEGS (w_H W) m a <> None.
Proof.
intros W m p l a HG Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
unfold aview. rewrite (garr8_mbyte SEGS _ p l (Z.to_nat (a - p)) HG ltac:(lia)). discriminate.
Qed.

Definition hoG_at (ii : Z) : Prop :=
  forall c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn,
  hoG_ctx c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn ii ->
  getr regs2 24 = w64 (48 * ii) -> 0 <= ii < nn ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7294) (ho_post B c).

Definition hoG_after (ii : Z) : Prop :=
  forall c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn (v : word),
  hoG_ctx c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn ii ->
  getr regs2 24 = w64 (48 * ii) -> getr regs2 21 = w64 (c_h c + 48 * ii) ->
  getr regs2 10 = v ->
  (v = w64 0 <-> disco_table_c.mac_of T' ii = disco_table_c.s_mac G) ->
  0 <= ii < nn ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x72a8) (ho_post B c).

Lemma hoG_call : forall ii, hoG_after ii -> hoG_at ii.
Proof.
intros ii HK c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn HC H24 Hii.
pose proof HC as (HB & R20 & Hr01 & R19 & R23 & R25 & HFSH & HOK & HT2 & HTl & Hnneq & Hnn8
  & HGg & HGl & Hmis & Hout0 & Hrd & HGo & HCl).
pose proof HB as (HP & HM & HSP & HFA & HRM & HSV).
pose proof HM as (HJ & HFrS & HFad & HPerm & HKept & HGH2 & HFlag & HH2l).
pose proof HRM as (M2 & M3 & M4 & M8 & M9 & M18 & M22 & M26 & M27).
destruct (hoG_band c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB)
  as (KC & KW & KS1 & KS0 & KA32 & KA16 & KSTK & KF1 & KF2 & KF4 & KSP47 & KF3).
destruct (hoG_pre_facts c HP)
  as (Hal16 & Hwin & Hsp & Hh0 & Hh8 & Hin & Hhb & Hhe & Hgp & Htp & HOKH & Hout64 & HTO & HJE).
pose proof asan_consts as (CAC & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HH2len : length H2 = 480%nat) by (destruct HOK as (HL & _); exact HL).
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (hoG_E regs2) n = getr regs2 x)
  by (intros; apply hoG_env_reg; assumption).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite HFrS; left; reflexivity).
assert (HFeq : frame_addr ly2 1 fpos = F) by (rewrite HFad; symmetry; exact HFA).
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
pose proof (paj_run (fx := c_fq c) B LAWS) as RUN.
unfold ho_cfg.
destruct (hoG_enter (c_fq c) regs2 W2 mem2 0x7294) as [HS SHOK].
pose proof (hoG_env_img regs2) as HEI.
paj_run_tok RUN HS HJ SHOK HOspan.
{ apply awr_ok_nil. }
pmkst HS.
prreg HS (10%bv : bv 5) QA0. prreg HS (11%bv : bv 5) QA1. prreg HS (12%bv : bv 5) QA2.
prreg HS (1%bv : bv 5) QRA. prreg HS (21%bv : bv 5) Q21.
pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
  [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv HS (hoG_env_agree regs2)
  ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict mkst] in HKR.
assert (RA0 : getr (ms_regs ms) 10 = w64 (c_h c + 48 * ii)).
{ rewrite QA0, (EE 22%nat 22%bv eq_refl), M22, (EE 24%nat 24%bv eq_refl), H24.
  unfold w64. rewrite alu64_add_lit. reflexivity. }
assert (R21 : getr (ms_regs ms) 21 = w64 (c_h c + 48 * ii)).
{ rewrite Q21, (EE 22%nat 22%bv eq_refl), M22, (EE 24%nat 24%bv eq_refl), H24.
  unfold w64. rewrite alu64_add_lit. reflexivity. }
assert (RA1 : getr (ms_regs ms) 11 = w64 (F + 32))
  by (rewrite QA1, (EE 23%nat 23%bv eq_refl); exact R23).
assert (RSP : spZ (ms_regs ms) = sp1).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbn [In]; auto 20)), M2. unfold w64.
  apply unsigned_lit_small. clear - Hes KC CAC KS1 KS0 KSP47; lia. }
assert (CTX1 : hoG_ctx c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
  H2 T' G (ms_regs ms) sp1 F r nn ii).
{ apply (hoG_step_mem c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms)
    (with_vm_backing (m_vm_lazy md2) mat md2) H2 T' G regs2 (ms_regs ms) sp1 F r nn ii HC HJ).
  - intros a Ha Hb.
    apply (ho_aview_frame (hoG_E regs2) (ss_mem (hoG_ss 0x7294)) W2 mem2 (ms_mem ms) a HFr Ha).
    intros (rg & Hrg & _). unfold hoG_ss in Hrg. cbn [ss_mem] in Hrg. destruct Hrg.
  - intros a Hpr. eapply apresent_grows; [exact HG | exact Hpr].
  - exact HKR. }
pose proof CTX1 as (HB1 & R20a & _ & R19a & R23a & R25a & HFSHa & _ & _ & _ & _ & _
  & HGga & _ & _ & _ & Hrda & HGoa & _).
pose proof HJ as (HARr & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms) _ (c_hb c) (c_hn c) HARr Hin2)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
destruct (al_shadow _ _ LAWS ly2 S2 W2 (ms_mem ms) _ (c_hb c) (c_hn c) HARr Hin2) as (Hbsh & Hbhull).
assert (HraG : range_addressable (aview SEGS (w_H W2) (ms_mem ms)) SHADOW_OFF (F + 32) 6).
{ eapply range_addressable_sub with (a := F + 32) (len := 8); [| lia | lia].
  apply zero_shadow_range; [clear - KF4; lia | reflexivity |].
  intros i Hi. change (8 / 8) with 1 in Hi.
  replace (shadow_of_addr SHADOW_OFF (F + 32) + i) with (SB + F / 8 + 4)
    by (unfold shadow_of_addr, SHADOW_OFF, SB; clear - KF4 Hi; lia).
  exact (HFSHa 4 ltac:(lia)). }
assert (HhullG : shadow_hull_vis (aview SEGS (w_H W2) (ms_mem ms)) (F + 32) 6).
{ apply (shadow_hull_vis_of_frame _ _ LAWS ly2 S2 W2 (ms_mem ms) _ 1 fpos (F + 32) 6 HARr HinF).
  - rewrite HFeq. lia.
  - rewrite HFeq. change (fs_frame_bytes 1) with 128. lia.
  - lia. }
assert (SRCX : src_ok SEGS W2 (ms_regs ms) (ms_mem ms) (c_h c + 48 * ii) 6).
{ intros a Ha. split.
  - apply (aview_some_of_apresent SEGS). apply (proj1 (Hbpres a ltac:(clear - Ha Hhb Hhe Hii Hnn8; lia))).
  - rewrite RSP. clear - Hes Ha Hhb Hhe Hii Hnn8 Hbceil CAC KC; lia. }
assert (SRCY : src_ok SEGS W2 (ms_regs ms) (ms_mem ms) (F + 32) 6).
{ intros a Ha. split.
  - apply (hoG_garr_some W2 (ms_mem ms) (F + 32) _ a HGga).
    rewrite length_map, HGl. clear - Ha; lia.
  - rewrite RSP. clear - Hes Ha KF1 KF2 CAC KC; lia. }
pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
  [24]%bv HS (hoG_env_agree regs2) ltac:(vm_compute; reflexivity)) as HK24.
cbn [ms_regs restrict mkst] in HK24.
pose proof HB1 as (_ & HM1 & _).
pose proof HM1 as (_ & _ & _ & _ & _ & HGH2a & _).
assert (HCMP := hoG_cmp W2 (ms_mem ms) (c_h c) (F + 32) H2 T' G ii HGH2a HGga HT2 HTl HGl
  ltac:(clear - Hii Hnn8; lia)).
eapply SRr_bind.
{ eapply (aj_bcmp_at (fx := c_fq c) SEGS B LAWS pa_segs_low _ (ABCMP (c_fq c)) W2 (ms_regs ms) (ms_mem ms)
    (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) ((1, fpos) :: c_own c)
    ly2 S2 _ k2 (c_h c + 48 * ii) (F + 32) 6 (sp1 - c_sp0 c) (Z_to_bv 64 (BASE + 29352)) HJ RA0 RA1 QA2).
  - lia.
  - clear - Hh0 Hii Hnn8; lia.
  - clear - Hhb Hhe Hbceil CAC Hii Hnn8; lia.
  - clear - KF1; lia.
  - clear - KF2 CAC; lia.
  - rewrite RSP. lia.
  - clear - KA32 KA16; lia.
  - clear - KS1 KS0; lia.
  - exact KSTK.
  - rewrite (HKR 3%bv ltac:(cbn [In]; auto 20)). exact M3.
  - rewrite (HKR 4%bv ltac:(cbn [In]; auto 20)). exact M4.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact SRCX.
  - exact SRCY.
  - intros a Ha. clear - Hes Ha Hhb Hhe Hbceil CAC KC Hii Hnn8; lia.
  - intros a Ha. clear - Hes Ha KF1 KF2 CAC KC; lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    clear - Hbapp Hhb Hhe Hii Hnn8 CAC Hbceil; lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in KF3.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    clear - KF3 KF2 CAC; lia.
  - apply (range_addressable_of_block _ _ LAWS ly2 S2 W2 (ms_mem ms) _ (c_hb c) (c_hn c)
      (c_h c + 48 * ii) 6 HARr Hin2); clear - Hhb Hhe Hii Hnn8; lia.
  - intros _. apply (hoG_hull_sub _ (c_hb c) (req_size (c_hn c))); [exact Hbhull | | | |];
    clear - Hhb Hhe Hii Hnn8 Hb4096; lia.
  - exact HraG.
  - intros _. exact HhullG. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpr3).
assert (CTX2 : hoG_ctx c fpos ly2 S2 W2 mem3 md3 k2 H2 T' G regs3 sp1 F r nn ii).
{ apply (hoG_step_mem c fpos ly2 S2 W2 (ms_mem ms) _ k2 mem3 md3 H2 T' G (ms_regs ms) regs3
    sp1 F r nn ii CTX1 HJ3).
  - intros a Ha Hb. apply Hfr3; [exact Ha | clear - Hb; lia].
  - exact Hpr3.
  - exact (hoG_pres_list _ _ HP3). }
apply (HK c fpos ly2 S2 W2 mem3 md3 k2 H2 T' G regs3 sp1 F r nn v CTX2).
- etransitivity; [exact (HP3 24 ltac:(unfold acallee_saved; lia)) |].
  etransitivity; [exact (HK24 24%bv ltac:(cbn [In]; auto)) | exact H24].
- etransitivity; [exact (HP3 21 ltac:(unfold acallee_saved; lia)) | exact R21].
- exact Hv.
- exact (iff_trans Hcmp HCMP).
- exact Hii.
Qed.

Definition hoG_tail (ii : Z) : Prop :=
  forall c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn,
  hoG_ctx c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn (ii + 1) ->
  getr regs2 24 = w64 (48 * (ii + 1)) -> 0 <= ii < nn ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x72b0) (ho_post B c).

Lemma hoG_branch : forall ii, ho_seg_H_stmt B -> hoG_tail ii -> hoG_after ii.
Proof.
intros ii HH HTl0 c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn v HC H24 H21 H10 Hcmp Hii.
pose proof HC as (HB & R20 & Hr01 & R19 & R23 & R25 & HFSH & HOK & HT2 & HTl & Hnneq & Hnn8
  & HGg & HGl & Hmis & Hout0 & Hrd & HGo & HCl).
pose proof HB as (HP & HM & HSP & HFA & HRM & HSV).
pose proof HM as (HJ & HFrS & HFad & HPerm & HKept & HGH2 & HFlag & HH2l).
pose proof HRM as (M2 & M3 & M4 & M8 & M9 & M18 & M22 & M26 & M27).
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (hoG_E regs2) n = getr regs2 x)
  by (intros; apply hoG_env_reg; assumption).
pose proof (paj_run (fx := c_fq c) B LAWS) as RUN.
pose proof (paj_run_to (fx := c_fq c) B LAWS) as RUNTO.
pose proof (paj_branch (fx := c_fq c) (PI := PI)) as BR.
unfold ho_cfg.
destruct (hoG_enter (c_fq c) regs2 W2 mem2 0x72a8) as [HS SHOK].
pose proof (hoG_env_img regs2) as HEI.
assert (U10 : U (hoG_E regs2) (SOff 10 0) = bv_unsigned v)
  by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl), H10; symmetry; apply Z_to_bv_bv_unsigned
                    | apply bv_unsigned_in_range]).
assert (U0 : U (hoG_E regs2) (SLit 0) = 0) by (apply U_lit; lia).
psrr_branch_tok RUN BR HS SHOK HOspan.
- rewrite branch_eq_U, U10, U0 in Hc. apply Z.eqb_eq in Hc.
  assert (Hv0 : v = w64 0)
    by (apply bv_eq; rewrite Hc; unfold w64; rewrite unsigned_lit_small by (cbn; lia); reflexivity).
  pose proof (proj1 Hcmp Hv0) as Hhit.
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x732c.
  { apply awr_ok_nil. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (hoG_env_agree regs2)
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict mkst] in HKR.
  assert (CTX1 : hoG_ctx c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn ii).
  { apply (hoG_step_mem c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms)
      (with_vm_backing (m_vm_lazy md2) mat md2) H2 T' G regs2 (ms_regs ms) sp1 F r nn ii HC HJ).
    - intros a Ha Hb.
      apply (ho_aview_frame (hoG_E regs2) (ss_mem (hoG_ss 0x72a8)) W2 mem2 (ms_mem ms) a HFr Ha).
      intros (rg & Hrg & _). unfold hoG_ss in Hrg. cbn [ss_mem] in Hrg. destruct Hrg.
    - intros a Hpr. eapply apresent_grows; [exact HG | exact Hpr].
    - intros q Hq. apply HKR. cbn [In] in Hq. cbn [In]. tauto. }
  pose proof CTX1 as (HB1 & R20a & _ & _ & R23a & R25a & HFSHa & _ & _ & _ & _ & _
    & HGga & _ & _ & _ & Hrda & HGoa & _).
  apply (HH c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    (ms_regs ms) sp1 F H2 T' G r ii HB1 R20a Hr01).
  + etransitivity; [exact (HKR 21%bv ltac:(cbn [In]; auto 20)) | exact H21].
  + exact R23a.
  + exact R25a.
  + exact HFSHa.
  + exact HOK.
  + exact HT2.
  + exact HTl.
  + clear - Hii Hnneq; lia.
  + exact Hhit.
  + exact Hmis.
  + exact HGga.
  + exact HGl.
  + exact Hout0.
  + exact Hrda.
  + exact HGoa.
  + intros A HA. subst A. apply HCl. exists ii. split.
    * right. split; [clear - Hii Hnneq; lia | split; [exact Hhit | exact Hmis]].
    * replace (ii <? 0) with false by (symmetry; apply Z.ltb_nlt; lia). reflexivity.
- rewrite branch_eq_U, U10, U0 in Hc. apply Z.eqb_neq in Hc.
  assert (Hvn : v <> w64 0)
    by (intros Hx; apply Hc; rewrite Hx; unfold w64; apply unsigned_lit_small; cbn; lia).
  assert (Hmiss : disco_table_c.mac_of T' ii <> disco_table_c.s_mac G)
    by (intros Hx; apply Hvn; exact (proj2 Hcmp Hx)).
  paj_run_tok RUN HS HJ SHOK HOspan.
  { apply awr_ok_nil. }
  pmkst HS.
  prreg HS (24%bv : bv 5) Q24.
  pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv HS (hoG_env_agree regs2)
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict mkst] in HKR.
  assert (CTX1 : hoG_ctx c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn (ii + 1)).
  { apply (hoG_step_mem c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms)
      (with_vm_backing (m_vm_lazy md2) mat md2) H2 T' G regs2 (ms_regs ms) sp1 F r nn (ii + 1)).
    - pose proof HC as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14
        & X15 & X16 & X17 & X18 & X19).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
      split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
      split; [exact X9|]. split; [exact X10|]. split; [exact X11|]. split; [exact X12|].
      split; [exact X13|]. split; [exact X14|]. split.
      { intros j Hj. destruct (Z.eq_dec j ii) as [-> | Hne];
        [exact Hmiss | apply X15; clear - Hj Hne; lia]. }
      split; [exact X16|]. split; [exact X17|]. split; [exact X18 | exact X19].
    - exact HJ.
    - intros a Ha Hb.
      apply (ho_aview_frame (hoG_E regs2) (ss_mem (hoG_ss 0x72a8)) W2 mem2 (ms_mem ms) a HFr Ha).
      intros (rg & Hrg & _). unfold hoG_ss in Hrg. cbn [ss_mem] in Hrg. destruct Hrg.
    - intros a Hpr. eapply apresent_grows; [exact HG | exact Hpr].
    - exact HKR. }
  apply (HTl0 c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn CTX1); [|exact Hii].
  rewrite Q24, (EE 24%nat 24%bv eq_refl), H24. unfold w64.
  rewrite unsigned_lit_small by (clear - Hii Hnn8; lia). f_equal. clear - Hii Hnn8; lia.
Qed.

Lemma hoG_back : forall ii, ho_seg_T_stmt B -> hoG_at (ii + 1) -> hoG_tail ii.
Proof.
intros ii HTs HA c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn HC H24 Hii.
pose proof HC as (HB & R20 & Hr01 & R19 & R23 & R25 & HFSH & HOK & HT2 & HTl & Hnneq & Hnn8
  & HGg & HGl & Hmis & Hout0 & Hrd & HGo & HCl).
pose proof HB as (HP & HM & HSP & HFA & HRM & HSV).
pose proof HM as (HJ & HFrS & HFad & HPerm & HKept & HGH2 & HFlag & HH2l).
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (hoG_E regs2) n = getr regs2 x)
  by (intros; apply hoG_env_reg; assumption).
pose proof (paj_run_to (fx := c_fq c) B LAWS) as RUNTO.
pose proof (paj_run (fx := c_fq c) B LAWS) as RUN.
pose proof (paj_branch (fx := c_fq c) (PI := PI)) as BR.
unfold ho_cfg.
destruct (hoG_enter (c_fq c) regs2 W2 mem2 0x72b0) as [HS SHOK].
pose proof (hoG_env_img regs2) as HEI.
assert (U19 : U (hoG_E regs2) (SOff 19 0) = 48 * nn)
  by (apply U_atom; [rewrite (EE 19%nat 19%bv eq_refl); exact R19 | clear - Hnn8; lia]).
assert (U24 : U (hoG_E regs2) (SOff 24 0) = 48 * (ii + 1))
  by (apply U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact H24 | clear - Hii Hnn8; lia]).
psrr_branch_tok RUN BR HS SHOK HOspan.
- rewrite branch_eq_U, U19, U24 in Hc. apply Z.eqb_eq in Hc.
  assert (Hend : ii + 1 = nn) by (clear - Hc; lia).
  assert (Hnone : forall j, 0 <= j < disco_table_c.n_of T' -> disco_table_c.mac_of T' j <> disco_table_c.s_mac G)
    by (intros j Hj; apply Hmis; clear - Hj Hnneq Hend; lia).
  assert (HAns : reac_hunt_observe_c.ho_answer T' G G).
  { exists (-1). split; [left; split; [reflexivity | exact Hnone] | reflexivity]. }
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x71a0.
  { apply awr_ok_nil. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv HS (hoG_env_agree regs2)
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict mkst] in HKR.
  assert (CTX1 : hoG_ctx c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn (ii + 1)).
  { apply (hoG_step_mem c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms)
      (with_vm_backing (m_vm_lazy md2) mat md2) H2 T' G regs2 (ms_regs ms) sp1 F r nn (ii + 1)
      HC HJ).
    - intros a Ha Hb.
      apply (ho_aview_frame (hoG_E regs2) (ss_mem (hoG_ss 0x72b0)) W2 mem2 (ms_mem ms) a HFr Ha).
      intros (rg & Hrg & _). unfold hoG_ss in Hrg. cbn [ss_mem] in Hrg. destruct Hrg.
    - intros a Hpr. eapply apresent_grows; [exact HG | exact Hpr].
    - exact HKR. }
  pose proof CTX1 as (HB1 & R20a & _ & _ & R23a & R25a & HFSHa & _ & _ & _ & _ & _
    & HGga & _ & _ & _ & Hrda & HGoa & HCla).
  apply (HTs c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    (ms_regs ms) sp1 F H2 r HB1 R20a ltac:(right; exact Hr01) R25a HFSHa HOK).
  apply (hoG_model_mono (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
    (fun A' => A' = G)
    (fun A => garr8 SEGS (mrestrict (w_H W2) (ms_mem ms)) (c_out c)
       (map (fun b : byte => bv_unsigned b) A))).
  + intros A HAG. subst A. exact HGoa.
  + exact (HCla G HAns).
- rewrite branch_eq_U, U19, U24 in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x7294.
  { apply awr_ok_nil. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok SEGS (hoG_E regs2) _ _ regs2 (map (Z_to_bv 64) [SB])
    [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS (hoG_env_agree regs2)
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict mkst] in HKR.
  assert (CTX1 : hoG_ctx c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn (ii + 1)).
  { apply (hoG_step_mem c fpos ly2 S2 W2 mem2 md2 k2 (ms_mem ms)
      (with_vm_backing (m_vm_lazy md2) mat md2) H2 T' G regs2 (ms_regs ms) sp1 F r nn (ii + 1)
      HC HJ).
    - intros a Ha Hb.
      apply (ho_aview_frame (hoG_E regs2) (ss_mem (hoG_ss 0x72b0)) W2 mem2 (ms_mem ms) a HFr Ha).
      intros (rg & Hrg & _). unfold hoG_ss in Hrg. cbn [ss_mem] in Hrg. destruct Hrg.
    - intros a Hpr. eapply apresent_grows; [exact HG | exact Hpr].
    - intros q Hq. apply HKR. cbn [In] in Hq. cbn [In]. tauto. }
  apply (HA c fpos ly2 S2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k2
    H2 T' G (ms_regs ms) sp1 F r nn CTX1).
  + etransitivity; [exact (HKR 24%bv ltac:(cbn [In]; auto 20)) | exact H24].
  + clear - Hc Hii; lia.
Qed.

Lemma hoG_loop : ho_seg_H_stmt B -> ho_seg_T_stmt B -> forall ii, hoG_at ii.
Proof.
intros HH HTs.
assert (Hk : forall k : nat, forall ii, Z.of_nat k = 8 - ii -> hoG_at ii).
{ induction k as [|k IH]; intros ii Hik.
  - intros c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn HC H24 Hii.
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnn8 & _).
    exfalso. clear - Hik Hii Hnn8. cbn [Z.of_nat] in Hik. lia.
  - apply hoG_call. apply hoG_branch; [exact HH|].
    apply hoG_back; [exact HTs|]. apply IH. clear - Hik. lia. }
intros ii c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn HC H24 Hii.
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnn8 & _).
exact (Hk (Z.to_nat (8 - ii)) ii ltac:(clear - Hii Hnn8; lia)
  c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn HC H24 Hii).
Qed.

Lemma ho_seg_G : ho_seg_H_stmt B -> ho_seg_T_stmt B -> ho_seg_G_stmt B.
Proof.
intros HH HTs. unfold ho_seg_G_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r nn ii HB H20 Hr01 H19 H24 H23 H25
  HFSH HOK HT2 HTl Hnneq Hii Hnn8 HGg HGl Hmis Hout0 Hrd HGo HCl.
apply (hoG_loop HH HTs ii c fpos ly2 S2 W2 mem2 md2 k2 H2 T' G regs2 sp1 F r nn);
  [| exact H24 | exact Hii].
split; [exact HB|]. split; [exact H20|]. split; [exact Hr01|]. split; [exact H19|].
split; [exact H23|]. split; [exact H25|]. split; [exact HFSH|]. split; [exact HOK|].
split; [exact HT2|]. split; [exact HTl|]. split; [exact Hnneq|]. split; [exact Hnn8|].
split; [exact HGg|]. split; [exact HGl|]. split; [exact Hmis|]. split; [exact Hout0|].
split; [exact Hrd|]. split; [exact HGo|].
intros A HAns. exact (HCl A HAns HGo).
Qed.

End h.
End f.
End d.
