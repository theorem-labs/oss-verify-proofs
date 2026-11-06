(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths, module names and numbers changed; 452 of its 506 lines of code are new or changed and 3286 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition TSB_CH_STK : Z := 16 + ESTACK.
Definition tsb_ch_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= a < sp) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TSB_CH_STK <= a < sp) -> apresent (w_H W) memc a ->
     apresent (w_H W2) mem2 a) /\
  (forall a, sp - TSB_CH_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition tsb_ch_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (s c p cap n : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    ((cap <= n + 1 /\
      val_mem SEGS (mrestrict (w_H W2) mem2) (s + 24) 4 1 /\
      tsb_ch_kept lyc Sc W memc W2 mem2 (spZ regs) (fun a => s + 24 <= a < s + 28)) \/
     (n + 1 < cap /\
      val_mem SEGS (mrestrict (w_H W2) mem2) (s + 16) 8 (n + 1) /\
      val_mem SEGS (mrestrict (w_H W2) mem2) (p + n) 1 (c mod 256) /\
      tsb_ch_kept lyc Sc W memc W2 mem2 (spZ regs) (fun a => s + 16 <= a < s + 24 \/ a = p + n))).
Definition tsb_ch_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s c p cap n : Z) ch,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z (regupd regs 8 (Z_to_bv 64 0))) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TSB_CH_STK -> spZ regs <= sp0 ->
  0 <= c < 2 ^ 64 ->
  0 < s -> s mod 8 = 0 -> s + 28 <= 2 ^ 63 -> amem_range s 28 ->
  (spZ regs <= s \/ s + 28 <= spZ regs - TSB_CH_STK) ->
  off_img s 28 ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n <= 2 ^ 64 - 2 ->
  val_mem SEGS (mrestrict (w_H W) memc) s 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 16) 8 n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 28 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) s 28 ->
  (forall a, s + 16 <= a < s + 28 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a) ->
  (n + 1 < cap ->
     0 < p /\ p + n + 1 <= 2 ^ 63 /\ amem_range (p + n) 1 /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) 1 /\
     shadow_hull_vis (aview SEGS (w_H W) memc) (p + n) 1 /\
     (spZ regs <= p + n \/ p + n + 1 <= spZ regs - TSB_CH_STK) /\
     off_img (p + n) 1 /\
     (p + n + 1 <= s \/ s + 28 <= p + n) /\
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (p + n) /\
     apresent (w_H W) memc (p + n)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs memc mdc)
    (tsb_ch_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s c p cap n).

#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition SBV : Z := 0x7fff8000.
Definition SbBx : sv := SOff 35 0.
Definition SbBspan : Z * Z := (SBV, SBV + 2 ^ 44 - 1).
Definition sb_rec (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 28 wlo whi
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition sbA_regions : smem :=
  [stack_region 16; got_regionP; bcell_regionP 35; sb_rec 16 24; YP09.mkRegion (Some 36%nat) 0 1 0 1 []].
Definition sbA_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 29) 3); (32%nat, mkAF 1 (2 ^ 47 - 2) 0);
           (34%nat, mkAF 0 (2 ^ 47 - 3) 0); (35%nat, mkAF SBV SBV 0); (36%nat, mkAF 1 (2 ^ 47 - 2) 0)] []
          [(SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 36 0)].
Definition ss_sbA : sstate := mkSS AF_both3_sb_ch sr_atoms sbA_regions None sbA_facts.
Definition sbA_SH : list shent := [mkSHE 10 0 28; mkSHE 36 0 1].
Definition sb_extra (p cap n : Z) : list word := map (Z_to_bv 64) [p; cap; n; SBV; p + n].

Definition sbB_regions : smem := [stack_region 16; got_regionP; bcell_regionP 35; sb_rec 24 28].
Definition sbB_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 29) 3); (35%nat, mkAF SBV SBV 0)] [] [].
Definition ss_sbB : sstate := mkSS AF_both3_sb_ch sr_atoms sbB_regions None sbB_facts.
Definition sbB_SH : list shent := [mkSHE 10 0 28].

Ltac sb_awr_tac Usp E10 E36 Hwr Hpnwr p n :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
    first [ exfalso; lia
          | left; rewrite Usp in Ha; lia
          | rewrite E10, unsigned_lit_small in Ha by lia; exact (proj1 (Hwr aw ltac:(lia)))
          | rewrite E36, unsigned_lit_small in Ha by lia; replace aw with (p + n) by lia; exact Hpnwr
          | idtac "AWR-FAIL"; match goal with H : _ |- ?g => idtac g H end; fail ] | ]); try destruct Hin.

Ltac sb_awr_tacB Usp E10 Hwr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
    first [ exfalso; lia
          | left; rewrite Usp in Ha; lia
          | rewrite E10, unsigned_lit_small in Ha by lia; exact (proj1 (Hwr aw ltac:(lia)))
          | idtac "AWR-FAIL"; match goal with H : _ |- ?g => idtac g H end; fail ] | ]); try destruct Hin.

Lemma tsb_ch_kept_refl : forall lyc Sc W m sp (Er : Z -> Prop),
  (forall a, sp - TSB_CH_STK <= a < sp -> apresent (w_H W) m a) -> tsb_ch_kept lyc Sc W m W m sp Er.
Proof.
intros lyc Sc W m sp Er Hp. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ H; exact H | exact Hp].
Qed.
Lemma tsb_ch_kept_step : forall lyc Sc W memc mdc m1 m2 sp (Er : Z -> Prop) Ex rs,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= sp - TSB_CH_STK ->
  tsb_ch_kept lyc Sc W memc W m1 sp Er ->
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange Ex rs a -> Er a \/ (sp - TSB_CH_STK <= a < sp)) ->
  (forall a, Er a -> off_img a 1) ->
  tsb_ch_kept lyc Sc W memc W m2 sp Er.
Proof.
intros lyc Sc W memc mdc m1 m2 sp Er Ex rs HAR Hceil (K1 & K2 & K3 & K4 & K5 & K6) HF HG Hwr HEr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ Er a -> ~ (sp - TSB_CH_STK <= a < sp) ->
  aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a).
{ intros a Ha He Hs. apply (aview_eq_of SEGS). apply HF. rewrite unsigned_lit_small by lia.
  intros Hw. destruct (Hwr a Hw) as [X | X]; [exact (He X) | exact (Hs X)]. }
split.
{ intros a Ha Hs He. rewrite (KO a Ha He Hs). exact (K1 a Ha Hs He). }
split.
{ intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
  rewrite (KO (b + i) ltac:(lia) Hn ltac:(lia)). exact (K2 b m i Hb Hi Hn). }
split.
{ intros a Him Hns Herr. pose proof (pa_segs_low a Him) as Hl. pose proof (pa_img_range a Him) as Hl2.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, kLowMemEnd in Hl, Hl2.
  assert (HnE : ~ Er a) by (intros He; pose proof (HEr a He) as He2; unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in He2; lia).
  rewrite (KO a ltac:(lia) HnE ltac:(lia)). exact (K3 a Him Hns Herr). }
split.
{ intros cid pos a Hf Hz Hn. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hf) as (Hf4096 & Hfceil & Hfhigh).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (Z.mul_div_le (frame_addr lyc cid pos) 8 ltac:(lia)) as D1.
  pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
  pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
  pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hz; cbn [fst snd] in Hz; lia. }
  rewrite (KO a ltac:(lia) Hn ltac:(lia)). exact (K4 cid pos a Hf Hz Hn). }
split.
{ intros a Ha Hs Hp. eapply apresent_grows; [exact HG | exact (K5 a Ha Hs Hp)]. }
intros a Ha. eapply apresent_grows; [exact HG | exact (K6 a Ha)].
Qed.
Ltac sb_wr Usp E10 E36 :=
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rw rs1) in Hin end;
  cbn [In] in Hin; cbv beta;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
     first [ exfalso; lia
           | right; rewrite Usp in Ha; lia
           | left; rewrite E10, unsigned_lit_small in Ha by lia; lia
           | left; rewrite E36, unsigned_lit_small in Ha by lia; lia
           | idtac "WR-FAIL"; match goal with |- ?g => idtac g end; fail ] | ]); try destruct Hin.

Lemma sb_caseA : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s c p cap n : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TSB_CH_STK -> spZ regs <= sp0 ->
  0 <= c < 2 ^ 64 ->
  0 < s -> s mod 8 = 0 -> s + 28 <= 2 ^ 63 -> amem_range s 28 ->
  (spZ regs <= s \/ s + 28 <= spZ regs - TSB_CH_STK) ->
  off_img s 28 ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n <= 2 ^ 64 - 2 ->
  val_mem SEGS (mrestrict (w_H W) memc) s 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 16) 8 n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 28 ->
  (forall a, s + 16 <= a < s + 28 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a) ->
  n + 1 < cap -> 0 < p -> p + n + 1 <= 2 ^ 63 -> amem_range (p + n) 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + n) 1 ->
  (spZ regs <= p + n \/ p + n + 1 <= spZ regs - TSB_CH_STK) -> off_img (p + n) 1 ->
  (p + n + 1 <= s \/ s + 28 <= p + n) ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (p + n) -> apresent (w_H W) memc (p + n) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs memc mdc)
    (tsb_ch_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s c p cap n).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s c p cap n
  HJc HROD Hra0 Hra4 Hgp Htp G10 G11 Hal16 Hwlo Hwhi Hcr Hs0 Hs8 Hs63 Hsam Hsside Hsimg Hp Hcap Hn
  Vp Vcap Vn Hsra Hwr Hlt Hp0 Hpn63 Hpnam Hpnra Hpnside Hpnimg Hpns Hpnwr Hpnpres.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
remember (Eimg (Ereg regs (sb_extra p cap n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (sb_extra p cap n)) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SBV) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (p + n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall kk v, ew E kk = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some kk) = v).
{ intros kk v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp. fold (spZ regs) in Rsp.
assert (HS : st_ok_pi SEGS VAL E ss_sbA (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_sb_ch)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sbA. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sbA_regions, sb_rec, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpresc. lia.
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 SbBx SBV);
      [cbn [sv_denot SbBx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBV; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite (VB 10%nat s E10) by lia. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (Hwr (s + o)). lia.
      * constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (chunk_ok_val SEGS E _ s 0 8 _ p); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vp].
        -- apply (chunk_ok_val SEGS E _ s 8 8 _ cap); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcap].
        -- apply (chunk_ok_val SEGS E _ s 16 8 _ n); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
    + rewrite (VB 36%nat (p + n) E36) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (p + n + o) with (p + n) by lia. exact Hpnpres.
  - apply pairwise_disjoint_of_extents. unfold sbA_regions, sb_rec, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat s E10), (VB 36%nat (p + n) E36) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [sbA_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E32, E34, E35, E36, !unsigned_lit_small by (unfold SBV; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SBV in *. repeat match goal with |- _ /\ _ => split end; lia.
    + cbn [sbA_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 32 p E32), (U_atom E 34 n E34), (U_atom E 36 (p + n) E36) by lia.
      apply zcanon_id. unfold M64. lia. }
assert (SHOK : sh_ok SEGS SbBx sbA_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, sbA_SH. constructor; [|constructor; [|constructor]].
  - eapply shent_ok_of_range; [exact Hsra | unfold SbBx; rewrite (U_atom E 35 SBV E35) by (unfold SBV; lia); reflexivity
    | rewrite (U_atom E 10 s E10) by lia; reflexivity | lia | lia | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia].
  - eapply shent_ok_of_range; [exact Hpnra | unfold SbBx; rewrite (U_atom E 35 SBV E35) by (unfold SBV; lia); reflexivity
    | rewrite (U_atom E 36 (p + n) E36) by lia; reflexivity | lia | lia | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia]. }
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_sb_ch)) with (Z_to_bv 64 (BASE + AF_both3_sb_ch)).
pose (RUN := paj_run (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)). pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
pose proof HJc as HJ.
assert (Hceil2 : alloc_ceiling <= spZ regs - TSB_CH_STK) by lia.
assert (Hwin : forall a, spZ regs - TSB_CH_STK <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpresc; lia).
pose proof (tsb_ch_kept_refl lyc Sc W memc (spZ regs) (fun a => s + 16 <= a < s + 24 \/ a = p + n) Hwin) as K0.
assert (HEr : forall a, (fun a => s + 16 <= a < s + 24 \/ a = p + n) a -> off_img a 1) by (cbv beta; intros a Ha; unfold off_img in *; lia).
paj_run_tok RUN HS HJ SHOK SbBspan; [sb_awr_tac Usp E10 E36 Hwr Hpnwr p n |].
pose proof (tsb_ch_kept_step lyc Sc W memc mdc memc _ (spZ regs) _ _ _ HARc Hceil2 K0 HFr HG ltac:(sb_wr Usp E10 E36) HEr) as K1.
clear HF HFr HG K0.
psrr_branch_tok RUN BR HS SHOK SbBspan.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  assert (F33 : ew Ex 33 = Z_to_bv 64 cap) by (cbn [ew ewset Nat.eqb]; exact E33);
  assert (F34 : ew Ex 34 = Z_to_bv 64 n) by (cbn [ew ewset Nat.eqb]; exact E34);
  rewrite branch_geu_U, (U_atom_off Ex 34 n 1 F34 ltac:(lia) ltac:(lia)), (U_atom Ex 33 cap F33 ltac:(lia)) in Hc end.
  apply negb_true_iff, Z.ltb_ge in Hc. lia. }
paj_run_tok RUN HS HJ SHOK SbBspan; [sb_awr_tac Usp E10 E36 Hwr Hpnwr p n |].
pose proof (tsb_ch_kept_step lyc Sc W memc mdc _ _ (spZ regs) _ _ _ HARc Hceil2 K1 HFr HG ltac:(sb_wr Usp E10 E36) HEr) as K2.
clear HF HFr HG K1.
psrr_branch_tok RUN BR HS SHOK SbBspan.
{ exfalso. lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  assert (F32 : ew Ex 32 = Z_to_bv 64 p) by (cbn [ew ewset Nat.eqb]; exact E32);
  assert (F36 : ew Ex 36 = Z_to_bv 64 (p + n)) by (cbn [ew ewset Nat.eqb]; exact E36);
  rewrite branch_ltu_U, (U_atom Ex 36 (p + n) F36 ltac:(lia)), (U_atom Ex 32 p F32 ltac:(lia)) in Hc0 end.
  apply Z.ltb_lt in Hc0. lia. }
paj_run_tok RUN HS HJ SHOK SbBspan; [sb_awr_tac Usp E10 E36 Hwr Hpnwr p n |].
pose proof (tsb_ch_kept_step lyc Sc W memc mdc _ _ (spZ regs) _ _ _ HARc Hceil2 K2 HFr HG ltac:(sb_wr Usp E10 E36) HEr) as K3.
clear HF HFr HG K2.
prreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r3 := eval vm_compute in (nth 3 rs got_regionP) in
  let r4 := eval vm_compute in (nth 4 rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4;
  cbn [ms_mem restrict] in HR3, HR4;
  assert (F10 : ew Ex 10 = Z_to_bv 64 s) by (cbn [ew ewset Nat.eqb]; exact E10);
  assert (F11 : ew Ex 11 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb]; exact E11);
  assert (F34 : ew Ex 34 = Z_to_bv 64 n) by (cbn [ew ewset Nat.eqb]; exact E34);
  assert (F36 : ew Ex 36 = Z_to_bv 64 (p + n)) by (cbn [ew ewset Nat.eqb]; exact E36);
  pose proof (field_of_region Ex _ 10 s _ _ _ _ _ 16 8 (SOff 34 1) (n + 1) HR3
    ltac:(rewrite F10; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
    ltac:(rewrite denot_lit_U, (U_atom_off Ex 34 n 1 F34) by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V16;
  pose proof (field_of_region_any Ex _ 36 (p + n) _ _ _ _ _ 0 1 (SOff 11 0) HR4
    ltac:(rewrite F36; apply unsigned_lit_small; lia) ltac:(cbn; tauto) ltac:(cbn; lia)) as V0;
  change (bv_unsigned (sv_denot Ex (SOff 11 0))) with (U Ex (SOff 11 0)) in V0;
  rewrite (U_atom Ex 11 c F11 Hcr), Z.add_0_r in V0; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul] in V16, V0
end.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tsb_ch_post.
eexists lyc, Sc, _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra0; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sb_extra p cap n) HS); [env_agree_chain HAE | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|].
right. split; [lia|]. split; [exact V16|]. split; [exact V0|]. exact K3.
Qed.

Lemma sb_caseB : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s c p cap n : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 c ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TSB_CH_STK -> spZ regs <= sp0 ->
  0 <= c < 2 ^ 64 ->
  0 < s -> s mod 8 = 0 -> s + 28 <= 2 ^ 63 -> amem_range s 28 ->
  (spZ regs <= s \/ s + 28 <= spZ regs - TSB_CH_STK) ->
  off_img s 28 ->
  0 <= p < 2 ^ 64 -> 0 <= cap < 2 ^ 64 -> 0 <= n <= 2 ^ 64 - 2 ->
  val_mem SEGS (mrestrict (w_H W) memc) s 8 p ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 8) 8 cap ->
  val_mem SEGS (mrestrict (w_H W) memc) (s + 16) 8 n ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s 28 ->
  (forall a, s + 16 <= a < s + 28 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a) ->
  cap <= n + 1 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs memc mdc)
    (tsb_ch_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s c p cap n).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s c p cap n
  HJc HROD Hra0 Hra4 Hgp Htp G10 G11 Hal16 Hwlo Hwhi Hcr Hs0 Hs8 Hs63 Hsam Hsside Hsimg Hp Hcap Hn
  Vp Vcap Vn Hsra Hwr Hge.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
remember (Eimg (Ereg regs (sb_extra p cap n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (sb_extra p cap n)) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SBV) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall kk v, ew E kk = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some kk) = v).
{ intros kk v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp. fold (spZ regs) in Rsp.
assert (HS : st_ok_pi SEGS VAL E ss_sbB (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_sb_ch)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_sbB. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold sbB_regions, sb_rec, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpresc. lia.
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 SbBx SBV);
      [cbn [sv_denot SbBx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBV; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite (VB 10%nat s E10) by lia. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (Hwr (s + o)). lia.
      * constructor; [|constructor; [|constructor; [|constructor]]].
        -- apply (chunk_ok_val SEGS E _ s 0 8 _ p); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vp].
        -- apply (chunk_ok_val SEGS E _ s 8 8 _ cap); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcap].
        -- apply (chunk_ok_val SEGS E _ s 16 8 _ n); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
  - apply pairwise_disjoint_of_extents. unfold sbB_regions, sb_rec, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat s E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [sbB_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E35, !unsigned_lit_small by (unfold SBV; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SBV in *. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok SEGS SbBx sbB_SH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, sbB_SH. constructor; [|constructor].
  eapply shent_ok_of_range; [exact Hsra | unfold SbBx; rewrite (U_atom E 35 SBV E35) by (unfold SBV; lia); reflexivity
    | rewrite (U_atom E 10 s E10) by lia; reflexivity | lia | lia | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia]. }
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_sb_ch)) with (Z_to_bv 64 (BASE + AF_both3_sb_ch)).
pose (RUN := paj_run (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)). pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
pose proof HJc as HJ.
assert (Hceil2 : alloc_ceiling <= spZ regs - TSB_CH_STK) by lia.
assert (Hwin : forall a, spZ regs - TSB_CH_STK <= a < spZ regs -> apresent (w_H W) memc a) by (intros a Ha; apply Hpresc; lia).
pose proof (tsb_ch_kept_refl lyc Sc W memc (spZ regs) (fun a => s + 24 <= a < s + 28) Hwin) as K0.
assert (HEr : forall a, (fun a => s + 24 <= a < s + 28) a -> off_img a 1) by (cbv beta; intros a Ha; unfold off_img in *; lia).
paj_run_tok RUN HS HJ SHOK SbBspan; [sb_awr_tacB Usp E10 Hwr |].
pose proof (tsb_ch_kept_step lyc Sc W memc mdc memc _ (spZ regs) _ _ _ HARc Hceil2 K0 HFr HG ltac:(sb_wr Usp E10 E10) HEr) as K1.
clear HF HFr HG K0.
psrr_branch_tok RUN BR HS SHOK SbBspan.
2: { exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  assert (F33 : ew Ex 33 = Z_to_bv 64 cap) by (cbn [ew ewset Nat.eqb]; exact E33);
  assert (F34 : ew Ex 34 = Z_to_bv 64 n) by (cbn [ew ewset Nat.eqb]; exact E34);
  rewrite branch_geu_U, (U_atom_off Ex 34 n 1 F34 ltac:(lia) ltac:(lia)), (U_atom Ex 33 cap F33 ltac:(lia)) in Hc end.
  apply negb_false_iff, Z.ltb_lt in Hc. lia. }
paj_run_tok RUN HS HJ SHOK SbBspan; [sb_awr_tacB Usp E10 Hwr |].
pose proof (tsb_ch_kept_step lyc Sc W memc mdc _ _ (spZ regs) _ _ _ HARc Hceil2 K1 HFr HG ltac:(sb_wr Usp E10 E10) HEr) as K2.
clear HF HFr HG K1.
prreg HS (1%bv : bv 5) R1.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r3 := eval vm_compute in (nth 3 rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3;
  cbn [ms_mem restrict] in HR3;
  assert (F10 : ew Ex 10 = Z_to_bv 64 s) by (cbn [ew ewset Nat.eqb]; exact E10);
  pose proof (field_of_region Ex _ 10 s _ _ _ _ _ 24 4 (SLit 1) 1 HR3
    ltac:(rewrite F10; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
    ltac:(rewrite denot_lit_U, U_lit by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V24;
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul] in V24
end.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold tsb_ch_post.
eexists lyc, Sc, _, _, _.
split; [cbn [ms_regs]; rewrite R1, E1, Hra0; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sb_extra p cap n) HS); [env_agree_chain HAE | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|].
left. split; [lia|]. split; [exact V24|]. exact K2.
Qed.

Theorem pb_sb_ch : tsb_ch_spec.
Proof.
unfold tsb_ch_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s c p cap n ch
  HJc HROD Hra0 Hra4 Hgp Htp G10 G11 Hch Hal16 Hwlo Hwhi Hcr Hs0 Hs8 Hs63 Hsam Hsside Hsimg Hp Hcap Hn
  Vp Vcap Vn Hsra Hshv Hwr HPN.
destruct (Z_lt_ge_dec (n + 1) cap) as [Hlt | Hge].
- destruct (HPN Hlt) as (Hp0 & Hpn63 & Hpnam & Hpnra & Hpnshv & Hpnside & Hpnimg & Hpns & Hpnwr & Hpnpres).
  exact (sb_caseA fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s c p cap n
    HJc HROD Hra0 Hra4 Hgp Htp G10 G11 Hal16 Hwlo Hwhi Hcr Hs0 Hs8 Hs63 Hsam Hsside Hsimg Hp Hcap Hn
    Vp Vcap Vn Hsra Hwr Hlt Hp0 Hpn63 Hpnam Hpnra Hpnside Hpnimg Hpns Hpnwr Hpnpres).
- exact (sb_caseB fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s c p cap n
    HJc HROD Hra0 Hra4 Hgp Htp G10 G11 Hal16 Hwlo Hwhi Hcr Hs0 Hs8 Hs63 Hsam Hsside Hsimg Hp Hcap Hn
    Vp Vcap Vn Hsra Hwr ltac:(lia)).
Qed.

End h.
End f.
End d.
