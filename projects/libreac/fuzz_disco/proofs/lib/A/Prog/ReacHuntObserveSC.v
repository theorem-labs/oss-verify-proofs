(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 903 of its 933 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacHuntObserveSeg.
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
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.

Lemma hc_pres_hi : forall (Wa Wb : world SEGS) ma mb a,
  YM05.alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H Wb) mb a = aview SEGS (w_H Wa) ma a -> apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a.
Proof.
intros Wa Wb ma mb a Ha HE Hp.
pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha D1; lia).
assert (Hni : ~ in_img SEGS a)
by (intros Him; pose proof (pa_segs_low a Him) as Hl; clear - Hl Ha D1 D5; unfold kLowMemEnd in *; lia).
exact (apresent_transfer SEGS (w_H Wa) (w_H Wb) ma mb a Hb Hni HE Hp).
Qed.
Lemma ho_firstn_app : forall (A R : list byte) n, length A = n -> firstn n (A ++ R) = A.
Proof. intros A R n <-. induction A as [|x A IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma ho_skipn_app2 : forall (A R : list byte) n, length A = n -> skipn n (A ++ R) = R.
Proof. intros A R n <-. induction A as [|x A IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma ho_skipn_app3 : forall (A R : list byte) n m, length A = n -> skipn (n + m) (A ++ R) = skipn m R.
Proof. intros A R n m <-. induction A as [|x A IH]; cbn; [reflexivity|]. exact IH. Qed.
Lemma ho_sub_tail : forall (A1 A2 A3 : list byte) n m k, length A1 = n -> length A2 = m ->
  skipn (n + m + k) (A1 ++ A2 ++ A3) = skipn k A3.
Proof.
intros A1 A2 A3 n m k HA HB. rewrite <- Nat.add_assoc.
rewrite (ho_skipn_app3 A1 _ n (m + k) HA). exact (ho_skipn_app3 A2 A3 m k HB).
Qed.
Lemma ho_map_skipn : forall (f : byte -> Z) a l, map f (skipn a l) = skipn a (map f l).
Proof. induction a as [|a IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma ho_map_firstn : forall (f : byte -> Z) n l, map f (firstn n l) = firstn n (map f l).
Proof. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma ho_map_sub : forall l k n, map (fun b : byte => bv_unsigned b) (disco_table_c.sub l k n)
  = firstn n (skipn (Z.to_nat k) (map (fun b : byte => bv_unsigned b) l)).
Proof. intros. unfold disco_table_c.sub. rewrite ho_map_firstn, ho_map_skipn. reflexivity. Qed.
Lemma ho_garr8_bytes : forall m a l, garr8 SEGS m a l -> Forall (fun b => 0 <= b < 256) l.
Proof.
intros m a l H. apply Forall_forall. intros v Hv.
apply In_nth with (d := 0) in Hv as (j & Hj & <-). exact (proj2 (H j Hj)).
Qed.
Lemma ho_map_byte_id : forall l : list Z, Forall (fun b => 0 <= b < 256) l ->
  map (fun b : byte => bv_unsigned b) (map (Z_to_bv 8) l) = l.
Proof.
induction 1 as [|x l Hx Hl IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small; exact Hx.
Qed.
Lemma hc_val_kept : forall (Wa Wb : world SEGS) ma mb a (n : nat) v,
  (forall i, a <= i < a + Z.of_nat n -> aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb a n v HE Hv k Hk. rewrite <- (Hv k Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.

Definition ho_setfq (c : hoC) (fx : YK11.FPState) : hoC :=
  mkHoC fx (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) (c_own c)
    (c_lyc c) (c_Sc c) (c_W c) (c_memc c) (c_k c) (c_regs c) (c_h c) (c_f c) (c_len c) (c_now c)
    (c_out c) (c_hb c) (c_hn c) (c_H c) (c_FB c) (c_O c).

Lemma ho_base_setfq : forall c fx fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base B c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_base B (ho_setfq c fx) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F.
Proof. intros c fx fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB. exact HB. Qed.

Lemma ho_SRr_setfq : forall c (fx : YK11.FPState) (Wx : world SEGS) cf,
  (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx) k = Sem.reg_get (@YK11.fp_regs (c_fq c)) k) ->
  (@YK11.fp_csr fx = @YK11.fp_csr (c_fq c) \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx)) 5) 7 = 0) ->
  SRr SEGS Wx cf (ho_post B (ho_setfq c fx)) -> SRr SEGS Wx cf (ho_post B c).
Proof.
intros c fx Wx cf Hfr Hcs HR. eapply SRr_mono; [exact HR|].
intros W5 c5 _ HP. unfold ho_post, treac_hunt_observe_post in HP |- *.
destruct HP as (fx' & ly5 & S5 & regs5 & mem5 & md5 & r5 & H5 & Hc5 & Hfr5 & Hcs5 & HR5).
exists fx', ly5, S5, regs5, mem5, md5, r5, H5. split; [exact Hc5|]. split.
- intros kk Hk. rewrite (Hfr5 kk Hk). exact (Hfr kk Hk).
- split; [|exact HR5]. destruct Hcs5 as [Hcs5|Hcs5]; [rewrite Hcs5; exact Hcs | right; exact Hcs5].
Qed.

Lemma ho_cl_callF : forall (fx : YK11.FPState) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  STK1 FP1 EV1 (o : Z) raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
     (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
        c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
        (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
        (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
        ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
        aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fx') k = Sem.reg_get (@YK11.fp_regs fx) k) /\
       (@YK11.fp_csr fx' = @YK11.fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx')) 5) 7 = 0) /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
       ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
       aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros fx W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr & Hcs & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hfr|]. split; [exact Hcs|].
rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma ho_seg_C : ho_seg_D_stmt B -> ho_seg_E_stmt B -> ho_seg_C_stmt B.
Proof.
unfold ho_seg_C_stmt, ho_seg_D_stmt, ho_seg_E_stmt.
intros HD HE0 c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F Hbase H19 H20 H21 H24 H23 H25 Hfsh HchC HoutC.
pose proof (SRr_run_to_pi_AJ (fx := c_fq c) B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ (fx := c_fq c) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := c_fq c) B LAWS) as RUNC.
unfold ho_base in Hbase.
destruct Hbase as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HMID as (HJ & Hfrs2 & Hfa2 & Hperm & HKEPT & HGh & Hflag120 & HlenH & Hk2le).
destruct HSP1 as (Hsp1eq & Hsp1win & Hsp1mod).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk &
  HcA & HcB & HcC & HcD & HcE & Hpres2 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin2 : In (1%Z, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof HPRE as (HPJ & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin1 & Hwin2 & Hdepth & Hlen & Hnow & Hout & Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hfr50 & Houtp & HKM & HKT & Hchain).
assert (HFaddr : frame_addr ly2 1 fpos = F) by (rewrite Hfa2; symmetry; exact HFeq).
rewrite HFaddr in HFal, HFpres, HFSpres, HF4096, HFceil, HFhigh.
assert (HFR : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HFR in Hwin1.
assert (HfsF : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HfsF in HFceil, HFpres, HFhigh.
pose proof HFhigh as HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HspZhi : spZ (c_regs c) <= 2 ^ 47) by (clear - Hwin2 Hshi H47; lia).
assert (Hsp1lo : 0 <= sp1) by (clear - Hsp1win Hwin1 Hslo Hceil C1; lia).
assert (Hsp1hi : sp1 < 2 ^ 63) by (clear - Hsp1win HspZhi; lia).
assert (HdisjF : F + 128 <= sp1) by (clear - Hsp1win Hwin1 Hslo Hceil HFceil; lia).
assert (HFzero : 0 <= F) by (clear - HF4096; lia).
assert (HFlt : F + 24 <= 2 ^ 64) by (clear - HFceil C1; lia).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E9 : ew E 9 = w64 sp1) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 F) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; clear - Hsp1lo Hsp1hi; lia).
assert (U26 : bv_unsigned (ew E 26) = F) by (rewrite E26; apply unsigned_lit_small; clear - HFzero HFlt C1; lia).
unfold ho_cfg.
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E
  (mkSS 29048 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 29048)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - exact I.
  - split; [exact I|]. split; exact I. }
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
assert (Em : ms_mem ms = mem2)
  by (apply functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
cbn [setpc ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3.
prreg HS (4%bv : bv 5) N4. prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10.
prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
prreg HS (20%bv : bv 5) N20. prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22.
prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25.
prreg HS (26%bv : bv 5) N26. prreg HS (27%bv : bv 5) N27.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pmkst HS. rewrite Em. rewrite Em in HJ.
assert (Hsig : SIGMA DS_reac_frame_clean_len = BASE + AF_reac_frame_clean_len)
  by (apply pa_xcalls; cbn [In disco_xcalls]; repeat (first [left; reflexivity | right])).
rewrite Hsig.
destruct HchC as (ch0 & HCH0).
assert (Usp2 : spZ (ms_regs ms) = sp1)
  by (unfold spZ; rewrite N2, (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - Hsp1lo Hsp1hi; lia).
assert (Us02 : s0Z (ms_regs ms) = spZ (c_regs c))
  by (unfold s0Z; rewrite N8, (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small;
      clear - HspZhi Hwin1 Hslo Hceil C1; lia).
assert (Hsp1m16 : sp1 mod 16 = 0) by (clear - Hsp1mod; lia).
assert (HRFC : REAC_FRAME_CLEAN_LEN_STK = 4096) by reflexivity.
pose proof (@pa_B_ok _ _ PI) as HBok. pose proof (@pa_base_lo _ _ PL_disco PI) as HBlo.
unfold IMG_LO in HBlo.
eapply SRr_bind.
{ eapply (ho_cl_callF (c_fq c)) with (STK1 := REAC_FRAME_CLEAN_LEN_STK)
    (FP1 := @nil (Z * Z)) (EV1 := 0) (o := sp1 - c_sp0 c) (ch1 := ch0).
  - exact HJ.
  - rewrite Usp2. clear; lia.
  - rewrite Zminus_mod, Hsp1m16, Hsp0al. reflexivity.
  - clear - Hsp1win Hwin2; lia.
  - rewrite HRFC; clear; lia.
  - rewrite HRFC; clear - Hwin1 Hsp1win; lia.
  - rewrite N3, (EE 3%nat 3%bv eq_refl); exact R3.
  - rewrite N4, (EE 4%nat 4%bv eq_refl); exact R4.
  - exact N1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBok; lia). clear - HBlo; lia.
  - rewrite Us02. replace (c_sp0 c + (sp1 - c_sp0 c)) with sp1 by (clear; lia).
    apply (achain_lower ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) sp1
             (spZ (c_regs c)) ch0 HCH0). clear - Hsp1win; lia.
  - intros HFN.
    pose proof HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
    assert (HROD2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2))
      by (apply (ho_rod_kept B (c_W c) W2 (c_memc c) mem2 HROD); exact K3).
    assert (G1 : getr (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) 1 = getr (ms_regs ms) 1)
      by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
    assert (G2 : getr (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) 2 = getr (ms_regs ms) 2)
      by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
    assert (G3 : getr (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) 3 = getr (ms_regs ms) 3)
      by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
    assert (G4 : getr (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) 4 = getr (ms_regs ms) 4)
      by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
    assert (G8 : s0Z (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = 0)
      by (unfold s0Z, getr; cbn; rewrite regupd_same; apply unsigned_lit_small; clear; lia).
    assert (Hin63 : In (VAL (A_OBJ 63), 8) disco_ro_ranges)
      by (rewrite (pa_obj_val 63%nat ltac:(unfold disco_nobj; lia)); cbn [disco_obj];
          unfold disco_ro_ranges; apply in_or_app; right; cbn [In]; do 8 right; left; reflexivity).
    assert (Hin64 : In (VAL (A_OBJ 64), 8) disco_ro_ranges)
      by (rewrite (pa_obj_val 64%nat ltac:(unfold disco_nobj; lia)); cbn [disco_obj];
          unfold disco_ro_ranges; apply in_or_app; right; cbn [In]; do 9 right; left; reflexivity).
    eapply SRr_mono.
    { apply (pb_reac_frame_clean_len B LAWS (c_fq c) ly2 S2 W2 (ms_regs ms) mem2 _ [] (c_len c)).
      - destruct HFN as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
        split; [exact A1|]. split; [rewrite G1; exact A2|].
        split; [unfold raZ; rewrite G1; exact A3|].
        split; [rewrite G3; exact A4|]. split; [rewrite G4; exact A5|].
        split; [unfold spZ; rewrite G2; exact A6|].
        split; [unfold spZ; rewrite G2; exact A7|].
        split; [|exact A9].
        rewrite G8. apply achain_low. clear - C1; lia.
      - exact HROD2.
      - rewrite N10, (EE 24%nat 24%bv eq_refl); exact H24.
      - exact Hlen.
      - apply (ho_ro_keep_val B DRO (c_W c) W2 (c_memc c) mem2 (VAL (A_OBJ 63)) 8
                 (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM HROD HROD2 Hin63
                 ltac:(clear; lia) ltac:(cbn [Z.of_nat]; clear; lia) HKM).
      - apply (ho_ro_keep_val B DRO (c_W c) W2 (c_memc c) mem2 (VAL (A_OBJ 64)) 8
                 (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT HROD HROD2 Hin64
                 ltac:(clear; lia) ltac:(cbn [Z.of_nat]; clear; lia) HKT). }
    cbv beta. intros W3 c3 _ HP3.
    unfold treac_frame_clean_len_post, apost_base in HP3. rewrite N1 in HP3. exact HP3.
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (fx' & ly3 & S3 & regs3 & mem3 & md3 & -> & Hfr3 & Hcs3 & HJ3 & HJ3c & HP3 & HK3).
clear RUNTOP RUNP RUNC.
pose proof (SRr_run_to_pi_AJ (fx := fx') B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ (fx := fx') B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fx') B LAWS) as RUNC.
destruct HK3 as (HL3 & HPerm3).
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS3 : st_ok_pi (fx := fx') SEGS VAL E3
  (mkSS 29056 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst (fx := fx') regs3 (Z_to_bv 64 (BASE + 29056)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE3. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - exact I.
  - split; [exact I|]. split; exact I. }
paj_run_shc RUNP RUNC HS3 HJ3.
{ apply awr_ok_nil. }
assert (Em3 : ms_mem ms0 = mem3)
  by (apply functional_extensionality; intros x; apply HF0; intros (r & Hr & _); destruct Hr).
cbn [setpc ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
prreg HS3 (1%bv : bv 5) M1. prreg HS3 (2%bv : bv 5) M2. prreg HS3 (3%bv : bv 5) M3.
prreg HS3 (4%bv : bv 5) M4. prreg HS3 (8%bv : bv 5) M8.
prreg HS3 (10%bv : bv 5) M10. prreg HS3 (11%bv : bv 5) M11. prreg HS3 (12%bv : bv 5) M12.
prreg HS3 (13%bv : bv 5) M13. prreg HS3 (14%bv : bv 5) M14.
prreg HS3 (19%bv : bv 5) M19. prreg HS3 (20%bv : bv 5) M20. prreg HS3 (25%bv : bv 5) M25.
prreg HS3 (23%bv : bv 5) M23.
prreg HS3 (9%bv : bv 5) M9. prreg HS3 (18%bv : bv 5) M18. prreg HS3 (22%bv : bv 5) M22.
prreg HS3 (26%bv : bv 5) M26. prreg HS3 (27%bv : bv 5) M27.
pmkst HS3. rewrite Em3. rewrite Em3 in HJ3.
assert (Hsig2 : SIGMA DS_reac_disco_classify_on_segment = BASE + AF_reac_disco_classify_on_segment)
  by (apply pa_xcalls; cbn [In disco_xcalls]; repeat (first [left; reflexivity | right])).
rewrite Hsig2.
unfold treac_disco_classify_on_segment_spec, tcls_entry in TCOS.
assert (T2 : getr regs3 2 = w64 sp1).
{ pose proof (HP3 2 ltac:(unfold acallee_saved; lia)) as X2. replace (Z_to_bv 5 2) with (2%bv : bv 5) in X2 by (apply bv_eq; reflexivity).
  rewrite X2, N2, (EE 2%nat 2%bv eq_refl); exact R2. }
assert (T3 : getr regs3 3 = w64 (as_gp B)).
{ pose proof (HP3 3 ltac:(unfold acallee_saved; lia)) as X3. replace (Z_to_bv 5 3) with (3%bv : bv 5) in X3 by (apply bv_eq; reflexivity).
  rewrite X3, N3, (EE 3%nat 3%bv eq_refl); exact R3. }
assert (T4 : getr regs3 4 = w64 (as_tp B)).
{ pose proof (HP3 4 ltac:(unfold acallee_saved; lia)) as X4. replace (Z_to_bv 5 4) with (4%bv : bv 5) in X4 by (apply bv_eq; reflexivity).
  rewrite X4, N4, (EE 4%nat 4%bv eq_refl); exact R4. }
assert (T8 : getr regs3 8 = w64 (spZ (c_regs c))).
{ pose proof (HP3 8 ltac:(unfold acallee_saved; lia)) as X8. replace (Z_to_bv 5 8) with (8%bv : bv 5) in X8 by (apply bv_eq; reflexivity).
  rewrite X8, N8, (EE 8%nat 8%bv eq_refl); exact R8. }
assert (T21 : getr regs3 21 = w64 (c_f c)).
{ pose proof (HP3 21 ltac:(unfold acallee_saved; lia)) as X21. replace (Z_to_bv 5 21) with (21%bv : bv 5) in X21 by (apply bv_eq; reflexivity).
  rewrite X21, N21, (EE 21%nat 21%bv eq_refl); exact H21. }
assert (T22 : getr regs3 22 = w64 (c_h c)).
{ pose proof (HP3 22 ltac:(unfold acallee_saved; lia)) as X22. replace (Z_to_bv 5 22) with (22%bv : bv 5) in X22 by (apply bv_eq; reflexivity).
  rewrite X22, N22, (EE 22%nat 22%bv eq_refl); exact R22. }
assert (T23 : getr regs3 23 = w64 (F + 32)).
{ pose proof (HP3 23 ltac:(unfold acallee_saved; lia)) as X23. replace (Z_to_bv 5 23) with (23%bv : bv 5) in X23 by (apply bv_eq; reflexivity).
  rewrite X23, N23, (EE 23%nat 23%bv eq_refl); exact H23. }
assert (T19 : getr regs3 19 = w64 (c_out c)).
{ pose proof (HP3 19 ltac:(unfold acallee_saved; lia)) as X19. replace (Z_to_bv 5 19) with (19%bv : bv 5) in X19 by (apply bv_eq; reflexivity).
  rewrite X19, N19, (EE 19%nat 19%bv eq_refl); exact H19. }
assert (T20 : getr regs3 20 = w64 (c_now c)).
{ pose proof (HP3 20 ltac:(unfold acallee_saved; lia)) as X20. replace (Z_to_bv 5 20) with (20%bv : bv 5) in X20 by (apply bv_eq; reflexivity).
  rewrite X20, N20, (EE 20%nat 20%bv eq_refl); exact H20. }
assert (T25 : getr regs3 25 = w64 (SB + F / 8)).
{ pose proof (HP3 25 ltac:(unfold acallee_saved; lia)) as X25. replace (Z_to_bv 5 25) with (25%bv : bv 5) in X25 by (apply bv_eq; reflexivity).
  rewrite X25, N25, (EE 25%nat 25%bv eq_refl); exact H25. }
assert (T9 : getr regs3 9 = w64 sp1).
{ pose proof (HP3 9 ltac:(unfold acallee_saved; lia)) as X9. replace (Z_to_bv 5 9) with (9%bv : bv 5) in X9 by (apply bv_eq; reflexivity).
  rewrite X9, N9, (EE 9%nat 9%bv eq_refl); exact R9. }
assert (T18 : getr regs3 18 = w64 F).
{ pose proof (HP3 18 ltac:(unfold acallee_saved; lia)) as X18. replace (Z_to_bv 5 18) with (18%bv : bv 5) in X18 by (apply bv_eq; reflexivity).
  rewrite X18, N18, (EE 18%nat 18%bv eq_refl); exact R18. }
assert (T26 : getr regs3 26 = w64 F).
{ pose proof (HP3 26 ltac:(unfold acallee_saved; lia)) as X26. replace (Z_to_bv 5 26) with (26%bv : bv 5) in X26 by (apply bv_eq; reflexivity).
  rewrite X26, N26, (EE 26%nat 26%bv eq_refl); exact R26. }
assert (T27 : getr regs3 27 = w64 SB).
{ pose proof (HP3 27 ltac:(unfold acallee_saved; lia)) as X27. replace (Z_to_bv 5 27) with (27%bv : bv 5) in X27 by (apply bv_eq; reflexivity).
  rewrite X27, N27, (EE 27%nat 27%bv eq_refl); exact R27. }
pose proof HJ3c as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & Kc1 & Kc2 & Kc3 & Kc4 & Kc5 & _ & _ & _ & _).
pose proof (proj1 HJ3) as HAR3.
pose proof Hlyc as (_ & _ & _ & _ & _ & HlyF3 & _ & _ & Hlytop3 & Hlystklo3 & Hlystkhi3 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop2 & Hlystklo2 & Hlystkhi2 & _).
assert (Hfa3 : forall cid p, frame_addr ly3 cid p = frame_addr ly2 cid p)
  by (intros; unfold frame_addr; rewrite HlyF3; reflexivity).
assert (Hfrs3 : frames S3 = (1%Z, fpos) :: frames (c_Sc c)) by (rewrite Hfrsc; cbn [app]; exact Hfrs2).
assert (Hfin3 : In (1%Z, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hin3 : In (c_hb c, c_hn c) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm3)); apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
assert (HCH3 : achain ly3 (aview SEGS (w_H W3) mem3) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch0).
{ apply (achain_ly_top ly2 ly3 _ _ _ _ Hlytop3).
  apply (achain_kept ly2 (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) mem3)
           (spZ (c_regs c) - 16) (spZ (c_regs c)) ch0 (spZ (c_regs c) - 16) HCH0
           ltac:(clear; lia) ltac:(rewrite Hlytop2; clear - Htop H47; lia)).
  intros a Ha. apply Kc1.
  - clear - Ha Hwin1 Hslo Hceil C1; lia.
  - try rewrite HRFC. clear - Ha Hsp1win; lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) HAR3 Hin3) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (blk_off_imgP _ _ _ _ _ _ (c_hb c) (c_hn c) HAR3 Hin3) as Hbimg.
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
assert (HGh3 : garr8 SEGS (mrestrict (w_H W3) mem3) (c_h c) (map (fun b : byte => bv_unsigned b) (c_H c))).
{ apply (ho_garr_kept W2 W3 mem2 mem3 (c_h c) _); [|exact HGh].
  intros i Hi. rewrite length_map in Hi. pose proof HOK as (HL & _ & _ & _).
  replace i with (c_hb c + (i - c_hb c)) by (clear; lia).
  apply (Kc2 (c_hb c) (c_hn c) (i - c_hb c) Hin2 Hin3);
  [clear - Hi HL Hhb Hhe; lia | apply inFP_nil]. }
assert (HFSH3 : ho_fsh W3 mem3 F ho_shC).
{ intros i Hi. rewrite (Kc4 1 fpos (SB + F / 8 + i) Hfin2); [apply Hfsh; exact Hi | | apply inFP_nil].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFaddr, <- SB_SHADOW_OFF.
  change (fs_frame_bytes 1 / 8) with 16. clear - Hi; lia. }
assert (Hfa3F : frame_addr ly3 1 fpos = F) by (rewrite Hfa3; exact HFaddr).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal3 & _ & HFpres3 & HFSpres3).
rewrite Hfa3F in HFal3, HFpres3, HFSpres3. rewrite HfsF in HFpres3.
destruct (garr8_of_present SEGS (mrestrict (w_H W3) mem3) (F + 32) 24)
  as (OBz & HOBl & HOBg).
{ intros a Ha. destruct (proj1 (HFpres3 a ltac:(cbn [Z.of_nat] in Ha; clear - Ha; lia))) as [Hw [bb Hb]].
  exists bb. unfold mrestrict. rewrite Hw. exact Hb. }
pose proof HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HROD2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2))
  by (apply (ho_rod_kept B (c_W c) W2 (c_memc c) mem2 HROD); exact K3).
assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3))
  by (apply (ho_rod_kept B W2 W3 mem2 mem3 HROD2); intros a Hi Ho He;
      exact (Kc3 a Hi Ho He ltac:(apply fp_spares_closed; intros (r & Hr & _); destruct Hr))).
assert (Usp3 : spZ (ms_regs ms0) = sp1)
  by (unfold spZ; rewrite M2, (EE3 2%nat 2%bv eq_refl), T2; apply unsigned_lit_small; clear - Hsp1lo Hsp1hi; lia).
assert (Us03 : s0Z (ms_regs ms0) = spZ (c_regs c))
  by (unfold s0Z; rewrite M8, (EE3 8%nat 8%bv eq_refl), T8; apply unsigned_lit_small;
      clear - HspZhi Hwin1 Hslo Hceil C1; lia).
assert (Hhr : 0 <= c_h c /\ c_h c + 480 <= 2 ^ 63) by (clear - Hh0 Hhb Hhe Hbceil C1; lia).
pose proof Hbapp as Hbapp2. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp2.
assert (Hdh3 : zdisjoint (c_hb c, req_size (c_hn c)) (F, 128)).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 _ (c_hb c) (c_hn c) 1 fpos HAR3 Hin3 Hfin3) as Hd.
  unfold zdisjoint in Hd |- *. cbn [fst snd] in Hd |- *. rewrite Hfa3F, HfsF in Hd. exact Hd. }
assert (Hawr3 : forall a, awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B (c_lyc c) (c_Sc c)) (c_lyc c) (c_own c) a ->
  awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
    (ablocks B ly3 S3) ly3 ((1%Z, fpos) :: c_own c) a).
{ intros a [Hx|[Hx|[Hx|Hx]]].
  - left; exact Hx.
  - right; left. destruct Hx as (Hfp & b & n & Hb & Hr). split; [exact Hfp|]. exists b, n.
    split; [apply (Permutation_in _ (Permutation_sym HPerm3)); apply (Permutation_in _ (Permutation_sym Hperm)); exact Hb | exact Hr].
  - right; right; left. destruct Hx as (b & n & Hb1 & Hb2 & Hr). exists b, n.
    split; [apply (Permutation_in _ (Permutation_sym HPerm3)); apply (Permutation_in _ (Permutation_sym Hperm)); exact Hb1|].
    split; [exact Hb2 | exact Hr].
  - right; right; right. destruct Hx as (cid & pos & Hown3 & Hr). exists cid, pos.
    split; [right; exact Hown3|]. rewrite (Hfa3 cid pos), (Hfa2 cid pos). exact Hr. }
eapply SRr_bind.
{ eapply (TCOS fx' (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
          ((1%Z, fpos) :: c_own c) ly3 S3 W3 mem3 _ _ (ms_regs ms0) ch0
          (c_h c + 400) (c_f c) (ho_L c) (c_h c + 412) (F + 32)
          (c_FB c) (ho_U c) (map (Z_to_bv 8) OBz) (ho_Lk c)).
  1: exact HJ3.
  1: exact HROD3.
  1: rewrite M1; apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  1: unfold raZ; rewrite M1, unsigned_lit_small by (clear - HBok; lia); clear - HBlo; lia.
  1: rewrite M3, (EE3 3%nat 3%bv eq_refl); exact T3.
  1: rewrite M4, (EE3 4%nat 4%bv eq_refl); exact T4.
  1: rewrite M10, (EE3 22%nat 22%bv eq_refl), T22, unsigned_lit_small by (clear - Hhr; lia); reflexivity.
  1: rewrite M11, (EE3 21%nat 21%bv eq_refl); exact T21.
  1: rewrite M12, (EE3 10%nat 10%bv eq_refl); exact HL3.
  1: rewrite M13, (EE3 22%nat 22%bv eq_refl), T22, unsigned_lit_small by (clear - Hhr; lia); reflexivity.
  1: rewrite M14, (EE3 23%nat 23%bv eq_refl); exact T23.
  1: rewrite Usp3, Us03; apply (achain_lower ly3 _ (spZ (c_regs c) - 16) sp1 _ ch0 HCH3); clear - Hsp1win; lia.
  1: rewrite Usp3; exact Hsp1m16.
  1: rewrite Usp3; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; clear - Hwin1 Hsp1win; lia.
  1: rewrite Usp3; clear - Hsp1win Hwin2; lia.
  1: rewrite Usp3, Hlytop3, Hlytop2; clear - Hsp1win Hwin2 Htop2; lia.
  1: rewrite Hfrs3; cbn [length]; unfold REAC_HUNT_OBSERVE_DEPTH, CLS_DEPTH in Hdepth; unfold CLS_DEPTH; clear - Hdepth; lia.
  1: unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model;
     destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)) eqn:EL;
     [apply andb_prop in EL as [EL1 _]; apply Z.leb_le in EL1; clear - Hlen EL1; lia
     | clear - Hlen; lia].
  1: exact LFB.
  1: unfold ho_U; apply HuntObsLib.len_sub; [clear; lia|]; pose proof HOK as (HL & _); rewrite HL; clear; cbn; lia.
  1: rewrite length_map; exact HOBl.
  1: { intros HLf. assert (Hlf : 50 <= c_len c) by (clear - HLf; unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model in HLf;
         destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)); lia).
       destruct (Hfr50 Hlf) as (Hf0 & (fb & fn & Hfb & Hfb1 & Hfb2) & Hfh & Hfg).
       assert (Hfb2a : In (fb, fn) (ablocks B ly2 S2))
         by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hfb).
       assert (Hfb3 : In (fb, fn) (ablocks B ly3 S3))
         by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hfb2a).
       destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fn HAR3 Hfb3) as (_ & Gf4096 & Gfceil & Gfapp & Gfpres & _).
       pose proof Gfapp as Gfapp2. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gfapp2.
       split; [exact Hf0|]. split; [|split].
       - split; [clear - Hf0; lia|]. split; [clear - Hfb1 Hfb2 Gfceil C1; lia|].
         split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - Hfb1 Hfb2 Gfapp2 Gfceil C1; lia|].
         split; [rewrite Usp3; right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK;
                 clear - Hfb1 Hfb2 Gfceil Hsp1win Hwin1 Hslo Hceil; lia|].
         split; [intros a Ha; exact (proj1 (Gfpres a ltac:(clear - Ha Hfb1 Hfb2; lia)))|].
         split; [apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ fb fn (c_f c) 50 HAR3 Hfb3 Hfb1 Hfb2)|].
         apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ fb fn (c_f c) 50 HAR3 Hfb3 Hfb1 Hfb2); clear; lia.
       - right; left. exists fb, fn. split; [exact Hfb3|]. split; [exact Hfb1 | exact Hfb2].
       - apply (ho_garr_kept W2 W3 mem2 mem3 (c_f c) _).
         + intros i Hi. unfold cls_bytes in Hi. rewrite length_map in Hi.
           replace i with (fb + (i - fb)) by (clear; lia).
           apply (Kc2 fb fn (i - fb) Hfb2a Hfb3); [clear - Hi Hfb1 Hfb2 LFB; rewrite LFB in Hi; lia | apply inFP_nil].
         + apply (ho_garr_kept (c_W c) W2 (c_memc c) mem2 (c_f c) _); [|exact Hfg].
           intros i Hi. unfold cls_bytes in Hi. rewrite length_map in Hi. rewrite LFB in Hi.
           replace i with (fb + (i - fb)) by (clear; lia).
           apply (K2 fb fn (i - fb) Hfb); [clear - Hi Hfb1 Hfb2; lia|].
           intros [Hw|(Ho0 & Hw)]; [clear - Hi Hfb1 Hfh Hw; lia|].
           destruct (Houtp Ho0) as (_ & _ & Hof). pose proof (Hof Hlf) as Hof2. clear - Hi Hfb1 Hw Hof2; lia. }
  1: { split; [clear - Hh0 Hhb; lia|]. split; [clear - Hhb Hhe Hbceil C1; lia|].
       split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - Hhb Hhe Hbapp2 Hbceil C1; lia|].
       split; [rewrite Usp3; right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK;
               clear - Hhb Hhe Hbceil Hsp1win Hwin1 Hslo Hceil; lia|].
       split; [intros a Ha; exact (proj1 (Hbpres a ltac:(clear - Ha Hhb Hhe; lia)))|].
       split; [apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) (c_h c + 412) 6 HAR3 Hin3
                        ltac:(clear - Hhb; lia) ltac:(clear - Hhe; lia))|].
       apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) (c_h c + 412) 6 HAR3 Hin3
                ltac:(clear - Hhb; lia) ltac:(clear - Hhe; lia)); clear; lia. }
  1: { right; left. exists (c_hb c), (c_hn c). split; [exact Hin3|]. split; [clear - Hhb; lia | clear - Hhe; lia]. }
  1: { unfold cls_bytes, ho_U. rewrite ho_map_sub. change (Z.to_nat 412) with 412%nat.
       replace (c_h c + 412) with (c_h c + Z.of_nat 412) by (clear; cbn; lia).
       apply (garr8_sub_x _ _ _ _ 412%nat 6%nat HGh3). rewrite length_map.
       pose proof HOK as (HL & _). rewrite HL. clear; cbn; lia. }
  1: clear - HF4096; lia.
  1: clear - HFal; lia.
  1: { split; [clear - HF4096; lia|]. split; [clear - HFceil C1; lia|].
       split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - HFapp HFceil C1; lia|].
       split; [rewrite Usp3; right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK;
               clear - HFceil Hsp1win Hwin1 Hslo Hceil; lia|].
       split; [intros a Ha; apply (proj1 (HFpres3 a ltac:(clear - Ha; lia)))|].
       split.
       - apply (zero_shadow_range _ _ (F + 32) 24 ltac:(clear - HFal; lia) ltac:(clear; lia)).
         intros i Hi. unfold shadow_of_addr.
         replace (SHADOW_OFF + (F + 32) / 8 + i) with (SB + F / 8 + (4 + i))
           by (rewrite <- SB_SHADOW_OFF; clear - HFal; lia).
         rewrite (HFSH3 (4 + i) ltac:(clear - Hi; lia)).
         destruct (Z.eq_dec i 0) as [->|Hi0]; [reflexivity|].
         destruct (Z.eq_dec i 1) as [->|Hi1]; [reflexivity|].
         replace i with 2 by (clear - Hi Hi0 Hi1; lia). reflexivity.
       - apply (shadow_hull_vis_of_frame _ _ LAWS _ _ _ _ _ 1 fpos (F + 32) 24 HAR3 Hfin3
                  ltac:(rewrite Hfa3F; clear; lia) ltac:(rewrite Hfa3F, HfsF; clear; lia)); clear; lia. }
  1: { unfold cls_bytes. rewrite (ho_map_byte_id OBz (ho_garr8_bytes _ _ _ HOBg)). exact HOBg. }
  1: { intros a Ha. right; right; right. exists 1%Z, fpos. split; [left; reflexivity|].
       left. unfold in_zr. cbn [fst snd]. rewrite Hfa3F. change (fs_frame_bytes 1) with 128.
       clear - Ha; lia. }
  1: { left. rewrite Hlystklo3, Hlystklo2. clear - HFceil Hceil C1; lia. }
  1: { unfold ho_Lk. split; [clear - Hh0 Hhb; lia|]. split; [clear - Hh8; lia|].
       split; [apply HuntObsLib.len_sub; [clear; lia|]; pose proof HOK as (HL & _); rewrite HL; clear; cbn; lia|].
       split.
       - split; [clear - Hh0 Hhb; lia|]. split; [clear - Hhb Hhe Hbceil C1; lia|].
         split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; clear - Hhb Hhe Hbapp2 Hbceil C1; lia|].
         split; [rewrite Usp3; right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK;
                 clear - Hhb Hhe Hbceil Hsp1win Hwin1 Hslo Hceil; lia|].
         split; [intros a Ha; exact (proj1 (Hbpres a ltac:(clear - Ha Hhb Hhe; lia)))|].
         split; [apply (range_addressable_of_block _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) (c_h c + 400) 12 HAR3 Hin3
                          ltac:(clear - Hhb; lia) ltac:(clear - Hhe; lia))|].
         apply (shadow_hull_vis_of_block _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) (c_h c + 400) 12 HAR3 Hin3
                  ltac:(clear - Hhb; lia) ltac:(clear - Hhe; lia)); clear; lia.
       - split.
         + unfold cls_bytes. rewrite ho_map_sub. change (Z.to_nat 400) with 400%nat.
           replace (c_h c + 400) with (c_h c + Z.of_nat 400) by (clear; cbn; lia).
           apply (garr8_sub_x _ _ _ _ 400%nat 12%nat HGh3). rewrite length_map.
           pose proof HOK as (HL & _). rewrite HL. clear; cbn; lia.
         + split; [intros a Ha; apply Hawr3; apply Hwr; clear - Ha Hhb Hhe; lia|].
           left. rewrite Hlystklo3, Hlystklo2. clear - Hhb Hhe Hbceil Hceil C1; lia. }
  1: { clear - Hdh3 Hhb Hhe HfsF; unfold zdisjoint in Hdh3; cbn [fst snd] in Hdh3; lia. }
  1: { intros HLf. assert (Hlf : 50 <= c_len c) by (clear - HLf; unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model in HLf;
         destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)); lia).
       destruct (Hfr50 Hlf) as (Hf0 & (fb & fn & Hfb & Hfb1 & Hfb2) & _ & _).
       assert (Hfb3 : In (fb, fn) (ablocks B ly3 S3))
         by (apply (Permutation_in _ (Permutation_sym HPerm3)); apply (Permutation_in _ (Permutation_sym Hperm)); exact Hfb).
       assert (Hdf : zdisjoint (fb, req_size fn) (frame_addr ly3 1 fpos, fs_frame_bytes 1))
         by (apply (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 _ fb fn 1 fpos HAR3 Hfb3 Hfin3)).
       unfold zdisjoint in Hdf; cbn [fst snd] in Hdf; rewrite Hfa3F, HfsF in Hdf.
       clear - Hdf Hfb1 Hfb2; lia. }
  1: { unfold ho_Lk. split; [clear - Hdh3 Hhb Hhe HfsF; unfold zdisjoint in Hdh3; cbn [fst snd] in Hdh3; lia|].
       split; [left; clear; lia|].
       intros HLf. assert (Hlf : 50 <= c_len c) by (clear - HLf; unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model in HLf;
         destruct ((54 <=? c_len c) && ((c_len c - 52) mod 36 =? 2)); lia).
       destruct (Hfr50 Hlf) as (_ & _ & Hfh & _). clear - Hfh Hhb Hhe; lia. } }
cbv beta. intros W4 c4 Hwle4 (fx'' & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfr4 & Hcs4 & HJ4 & HP4 & Hfrs4 & HPerm4 & Hret4 & HOut4 & HLock4 & HKc4).
assert (Hfr4c : forall kk : bv 5, bv_unsigned kk <> 10 ->
    Sem.reg_get (@YK11.fp_regs fx'') kk = Sem.reg_get (@YK11.fp_regs (c_fq c)) kk)
  by (intros kk Hkk; rewrite (Hfr4 kk Hkk); exact (Hfr3 kk Hkk)).
assert (Hcs4c : @YK11.fp_csr fx'' = @YK11.fp_csr (c_fq c) \/
    Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fx'')) 5) 7 = 0)
  by (destruct Hcs4 as [Hcs4|Hcs4]; [rewrite Hcs4; exact Hcs3 | right; exact Hcs4]).
apply (ho_SRr_setfq c fx'' _ _ Hfr4c Hcs4c).
clear RUNTOP RUNP RUNC.
pose proof (SRr_run_to_pi_AJ (fx := fx'') B LAWS) as RUNTOP.
destruct HKc4 as (Kd1 & Kd2 & Kd3 & Kd4 & Kd5 & Kd6).
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & Hly4 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & HlyF4 & _ & _ & Hlytop4 & Hlystklo4 & Hlystkhi4 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF2 & _).
assert (Hfa4 : forall cid p, frame_addr ly4 cid p = frame_addr ly2 cid p)
  by (intros; unfold frame_addr; rewrite HlyF4, HlyF2; reflexivity).
assert (Hfrs4b : frames S4 = (1%Z, fpos) :: frames (c_Sc c)) by (rewrite Hfrs4; exact Hfrs3).
assert (Hfin4 : In (1%Z, fpos) (frames S4)) by (rewrite Hfrs4b; left; reflexivity).
assert (Hfa4F : frame_addr ly4 1 fpos = F) by (rewrite Hfa4; exact HFaddr).
assert (Hperm4 : Permutation (ablocks B ly4 S4) (ablocks B (c_lyc c) (c_Sc c)))
  by (apply (Permutation_trans HPerm4); apply (Permutation_trans HPerm3); exact Hperm).
assert (Hin4 : In (c_hb c, c_hn c) (ablocks B ly4 S4))
  by (apply (Permutation_in _ (Permutation_sym Hperm4)); exact Hin).
assert (HnoW : forall a, ~ (c_h c + 400 <= a < c_h c + 412) -> ~ (F + 32 <= a < F + 32 + 24) ->
  ~ cls_wr (c_h c + 400) (F + 32) (ho_Lk c) a)
  by (intros a Ha1 Ha2 [Hw|Hw]; [clear - Ha2 Hw; lia | unfold ho_Lk in Hw; clear - Ha1 Hw; lia]).
assert (HUN4 : forall a, c_h c <= a < c_h c + 400 \/ c_h c + 412 <= a < c_h c + 480 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. replace a with (c_hb c + (a - c_hb c)) by (clear; lia).
  apply (Kd2 (c_hb c) (c_hn c) (a - c_hb c) Hin3); [clear - Ha Hhb Hhe; lia|].
  apply HnoW; [clear - Ha; lia | clear - Ha Hhb Hhe Hdh3 HfsF; unfold zdisjoint in Hdh3; cbn [fst snd] in Hdh3; lia]. }
pose proof HOK as (HLen & HTab & HLok & HS32).
assert (HsubL : disco_table_c.sub (c_H c) 400 12 = firstn 12 (skipn 400 (c_H c)))
  by (unfold disco_table_c.sub; reflexivity).
destruct (HuntObsLib.cm_lock_some (c_FB c) (ho_L c) (ho_U c) (disco_table_c.sub (c_H c) 400 12)) as (Lb' & HLb').
assert (HLk'eq : ho_Lk' c = Lb') by (unfold ho_Lk', ho_Lk; rewrite HLb'; reflexivity).
assert (HlokLb : disco_classify_c.lock_ok Lb').
{ apply (HuntObsLib.cm_lock_ok (c_FB c) (ho_L c) (ho_U c) (disco_table_c.sub (c_H c) 400 12) Lb'
           ltac:(intros _; exact LFB) ltac:(rewrite HsubL; exact HLok) HLb'). }
assert (HlenLk : length (ho_Lk' c) = 12%nat) by (rewrite HLk'eq; exact (proj1 HlokLb)).
assert (Hlen400 : length (disco_table_c.sub (c_H c) 0 400) = 400%nat)
  by (apply HuntObsLib.len_sub; [clear; lia | rewrite HLen; clear; cbn; lia]).
assert (Hlenskip : length (skipn 412 (c_H c)) = 68%nat) by (rewrite length_skipn, HLen; reflexivity).
assert (HlenHcls : length (ho_Hcls c) = 480%nat)
  by (unfold ho_Hcls; rewrite !length_app, Hlen400, HlenLk, Hlenskip; reflexivity).
assert (Hfirst400 : firstn 400 (ho_Hcls c) = disco_table_c.sub (c_H c) 0 400)
  by (unfold ho_Hcls; apply (ho_firstn_app _ _ _ Hlen400)).
assert (Hmid12 : firstn 12 (skipn 400 (ho_Hcls c)) = ho_Lk' c)
  by (unfold ho_Hcls; rewrite (ho_skipn_app2 _ _ _ Hlen400); apply (ho_firstn_app _ _ _ HlenLk)).
assert (Hsub440 : disco_table_c.sub (ho_Hcls c) 440 4 = disco_table_c.sub (c_H c) 440 4).
{ unfold disco_table_c.sub. cbn [Z.to_nat]. unfold ho_Hcls.
  replace 440%nat with (400 + 12 + 28)%nat by reflexivity.
  rewrite (ho_sub_tail _ _ _ 400 12 28 Hlen400 HlenLk).
  rewrite skipn_skipn. reflexivity. }
assert (Hhunt4 : hunt_c.hunt_ok (ho_Hcls c)).
{ unfold hunt_c.hunt_ok. split; [exact HlenHcls|]. split.
  - rewrite Hfirst400. unfold disco_table_c.sub. cbn [Z.to_nat]. rewrite skipn_O. exact HTab.
  - split; [rewrite Hmid12, HLk'eq; exact HlokLb|].
    unfold disco_table_c.s32_at, disco_table_c.u_at. rewrite Hsub440. exact HS32. }
assert (HmapH : map (fun b : byte => bv_unsigned b) (ho_Hcls c)
  = firstn 400 (map (fun b : byte => bv_unsigned b) (c_H c))
    ++ map (fun b : byte => bv_unsigned b) (ho_Lk' c)
    ++ skipn 412 (map (fun b : byte => bv_unsigned b) (c_H c))).
{ unfold ho_Hcls. rewrite !map_app. f_equal.
  - rewrite ho_map_sub. cbn [Z.to_nat]. rewrite skipn_O. reflexivity.
  - f_equal. apply ho_map_skipn. }
pose proof HGh3 as HGa. rewrite <- (firstn_skipn 400 (map (fun b : byte => bv_unsigned b) (c_H c))) in HGa.
apply (proj1 (garr8_app _ _ _ _ _)) in HGa. destruct HGa as (HGpre & HGrest).
rewrite length_firstn, length_map, HLen in HGrest. cbn [Nat.min] in HGrest.
pose proof HGrest as HGb. rewrite <- (firstn_skipn 12 (skipn 400 (map (fun b : byte => bv_unsigned b) (c_H c)))) in HGb.
apply (proj1 (garr8_app _ _ _ _ _)) in HGb. destruct HGb as (_ & HGsuf).
rewrite length_firstn, length_skipn, length_map, HLen in HGsuf. cbn [Nat.min Nat.sub] in HGsuf.
rewrite skipn_skipn in HGsuf.
assert (HGH4 : garr8 SEGS (mrestrict (w_H W4) mem4) (c_h c)
  (map (fun b : byte => bv_unsigned b) (ho_Hcls c))).
{ rewrite HmapH. apply (proj2 (garr8_app _ _ _ _ _)). split.
  - apply (garr8_aview_kept _ (w_H W3) (w_H W4) mem3 mem4 (c_h c) _); [|exact HGpre].
    intros a Ha. rewrite length_firstn, length_map, HLen in Ha. cbn [Nat.min] in Ha.
    apply HUN4. left. clear - Ha; lia.
  - rewrite length_firstn, length_map, HLen. cbn [Nat.min]. apply (proj2 (garr8_app _ _ _ _ _)). split.
    + rewrite HLk'eq. exact (HLock4 Lb' ltac:(unfold ho_Lk; exact HLb')).
    + rewrite length_map, HlenLk.
      apply (garr8_aview_kept _ (w_H W3) (w_H W4) mem3 mem4 _ _).
      * intros a Ha. rewrite length_skipn, length_map, HLen in Ha. cbn [Nat.sub] in Ha.
        apply HUN4. right. clear - Ha; lia.
      * replace (c_h c + Z.of_nat 400 + Z.of_nat 12) with (c_h c + 400 + Z.of_nat 12) by (clear; cbn; lia).
        exact HGsuf. }
assert (HCLS : CLS_STK = 8512) by reflexivity.
assert (HshHi : SB + F / 8 + 16 <= kHighMemBeg)
  by (unfold kHighMemBeg, SB; clear - HF4096 HFceil C1; lia).
assert (HnoWsh : forall i, 0 <= i < 16 -> ~ cls_wr (c_h c + 400) (F + 32) (ho_Lk c) (SB + F / 8 + i)).
{ intros i Hi. apply HnoW.
  - clear - Hi HshHi Hhb Hhe Hbapp2 HF4096; unfold SB in *; unfold kHighMemBeg in HshHi; lia.
  - clear - Hi HshHi HFapp HF4096; unfold SB in *; unfold kHighMemBeg in HshHi; lia. }
assert (HFSH4 : ho_fsh W4 mem4 F ho_shC).
{ intros i Hi. rewrite (Kd4 1 fpos (SB + F / 8 + i) Hfin3).
  - apply HFSH3; exact Hi.
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hfa3F, <- SB_SHADOW_OFF.
    change (fs_frame_bytes 1 / 8) with 16. clear - Hi; lia.
  - exact (HnoWsh i Hi). }
assert (HFLG3 : rdword (aview SEGS (w_H W3) mem3) (frame_addr (c_lyc c) 1 fpos + 120)
  = Some (flag_addr (c_lyc c) 1 fpos)).
{ rewrite <- Hflag120. apply rdword_ext. intros kk Hkk. rewrite <- HFeq.
  apply (Kc4 1 fpos (F + 120 + kk) Hfin2); [|apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr, HfsF. clear - Hkk; lia. }
assert (HFLG4 : rdword (aview SEGS (w_H W4) mem4) (frame_addr (c_lyc c) 1 fpos + 120)
  = Some (flag_addr (c_lyc c) 1 fpos)).
{ rewrite <- HFLG3. apply rdword_ext. intros kk Hkk. rewrite <- HFeq.
  apply (Kd4 1 fpos (F + 120 + kk) Hfin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa3F, HfsF. clear - Hkk; lia.
  - apply HnoW; [clear - Hkk Hdh3 Hhb Hhe HfsF; unfold zdisjoint in Hdh3; cbn [fst snd] in Hdh3; lia
                | clear - Hkk; lia]. }
assert (HSAVED4 : ho_saved c W4 mem4).
{ intros j Hj. apply (hc_val_kept W3 W4 mem3 mem4).
  - intros i Hi. cbn [Z.of_nat] in Hi. apply Kd1.
    + clear - Hi Hj Hwin1 Hslo Hceil C1 HspZhi; lia.
    + rewrite Usp3, HCLS. clear - Hi Hj Hsp1win; lia.
    + apply HnoW; [clear - Hi Hj Hhb Hhe Hbceil Hwin1 Hslo Hceil; lia
                  | clear - Hi Hj HFceil Hwin1 Hslo Hceil; lia].
  - apply (hc_val_kept W2 W3 mem2 mem3).
    + intros i Hi. cbn [Z.of_nat] in Hi. apply Kc1; [clear - Hi Hj Hwin1 Hslo Hceil C1 HspZhi; lia|].
      rewrite HRFC. clear - Hi Hj Hsp1win; lia.
    + exact (HSAVED j Hj). }
assert (U19 : getr regs4 19 = w64 (c_out c)).
{ pose proof (HP4 19 ltac:(unfold acallee_saved; lia)) as Y19.
  replace (Z_to_bv 5 19) with (19%bv : bv 5) in Y19 by (apply bv_eq; reflexivity).
  rewrite Y19, M19, (EE3 19%nat 19%bv eq_refl). exact T19. }
assert (U20 : getr regs4 20 = w64 (c_now c)).
{ pose proof (HP4 20 ltac:(unfold acallee_saved; lia)) as Y20.
  replace (Z_to_bv 5 20) with (20%bv : bv 5) in Y20 by (apply bv_eq; reflexivity).
  rewrite Y20, M20, (EE3 20%nat 20%bv eq_refl). exact T20. }
assert (U23 : getr regs4 23 = w64 (F + 32)).
{ pose proof (HP4 23 ltac:(unfold acallee_saved; lia)) as Y23.
  replace (Z_to_bv 5 23) with (23%bv : bv 5) in Y23 by (apply bv_eq; reflexivity).
  rewrite Y23, M23, (EE3 23%nat 23%bv eq_refl). exact T23. }
assert (U25 : getr regs4 25 = w64 (SB + F / 8)).
{ pose proof (HP4 25 ltac:(unfold acallee_saved; lia)) as Y25.
  replace (Z_to_bv 5 25) with (25%bv : bv 5) in Y25 by (apply bv_eq; reflexivity).
  rewrite Y25, M25, (EE3 25%nat 25%bv eq_refl). exact T25. }
assert (HKEPT4 : treac_hunt_observe_kept B (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W4 mem4
  (spZ (c_regs c)) (c_h c) (c_out c)).
{ pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jpres4 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hnw Hw. rewrite HFR in Hnw.
    rewrite (Kd1 a Ha ltac:(rewrite Usp3, HCLS; clear - Hnw Hsp1win; lia)
               ltac:(apply HnoW; [clear - Ha Hhb Hhe Hbceil C1; lia | clear - Ha HFceil C1; lia])).
    rewrite (Kc1 a Ha ltac:(rewrite HRFC; clear - Hnw Hsp1win; lia)).
    exact (K1 a Ha ltac:(rewrite HFR; exact Hnw) Hw).
  - intros b m i Hbl Hi Hw.
    assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbl).
    assert (Hb3 : In (b, m) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hb2).
    assert (Hbd : zdisjoint (b, req_size m) (F, 128)).
    { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 _ b m 1 fpos HAR3 Hb3 Hfin3) as Hd.
      unfold zdisjoint in Hd |- *. cbn [fst snd] in Hd |- *. rewrite Hfa3F, HfsF in Hd. exact Hd. }
    rewrite (Kd2 b m i Hb3 Hi ltac:(apply HnoW;
              [clear - Hw Hi; intros X; apply Hw; left; lia
              | clear - Hi Hbd; unfold zdisjoint in Hbd; cbn [fst snd] in Hbd; lia])).
    rewrite (Kc2 b m i Hb2 Hb3 Hi ltac:(apply inFP_nil)).
    exact (K2 b m i Hbl Hi Hw).
  - intros a Hia Ho He.
    rewrite (Kd3 a Hia Ho He).
    rewrite (Kc3 a Hia Ho He ltac:(apply fp_spares_closed; intros (r & Hr & _); destruct Hr)).
    exact (K3 a Hia Ho He).
  - intros cid pos a Hf Hr Hw.
    assert (Hf3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hf).
    assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hf).
    destruct (in_split _ _ Hf) as (l2 & l3 & Hsplit).
    assert (Hdf : zdisjoint (frame_rng ly3 (1%Z, fpos)) (frame_rng ly3 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 _ (1%Z, fpos) (cid, pos) [] l2 l3 HAR3);
          rewrite Hfrs3, Hsplit; reflexivity).
    unfold zdisjoint, frame_rng in Hdf. cbn [fst snd] in Hdf. rewrite Hfa3F, HfsF, (Hfa3 cid pos), (Hfa2 cid pos) in Hdf.
    assert (Hdb : zdisjoint (c_hb c, req_size (c_hn c)) (frame_addr (c_lyc c) cid pos, fs_frame_bytes cid)).
    { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 _ (c_hb c) (c_hn c) cid pos HAR3 Hin3 Hf3) as Hd.
      rewrite (Hfa3 cid pos), (Hfa2 cid pos) in Hd. exact Hd. }
    unfold zdisjoint in Hdb. cbn [fst snd] in Hdb.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hf3) as (G1 & G2 & G3).
    rewrite (Hfa3 cid pos), (Hfa2 cid pos) in G1, G2, G3.
    pose proof (fs_frame_bytes_nonneg cid) as Gn.
    pose proof G3 as G3u. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G3u.
    pose proof Hr as Hru. unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hru. cbn [fst snd] in Hru.
    assert (Hnc : ~ cls_wr (c_h c + 400) (F + 32) (ho_Lk c) a).
    { apply HnoW.
      - clear - Hru Hdb G1 G2 G3u Gn Hhb Hhe Hbapp2 HF4096 HFceil C1 HshHi;
        unfold kHighMemBeg in HshHi; unfold SB in *; lia.
      - clear - Hru Hdf Gn G1 G2 G3u HFapp HF4096 HFceil C1 HshHi;
        unfold kHighMemBeg in HshHi; unfold SB in *; lia. }
    pose proof Hr as Hr2. unfold in_zr, frame_rng in Hr2. cbn [fst snd] in Hr2.
    rewrite <- (Hfa2 cid pos) in Hr2.
    pose proof Hr2 as Hr3. rewrite <- (Hfa3 cid pos) in Hr3.
    rewrite (Kd4 cid pos a Hf3 ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Hr3) Hnc).
    rewrite (Kc4 cid pos a Hf2 ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Hr2) ltac:(apply inFP_nil)).
    exact (K4 cid pos a Hf Hr Hw).
  - intros a Ha Hnw Hp. rewrite HFR in Hnw.
    apply (Kd5 a Ha ltac:(rewrite Usp3, HCLS; clear - Hnw Hsp1win; lia)).
    apply (hc_pres_hi W2 W3 mem2 mem3 a Ha).
    + exact (Kc1 a Ha ltac:(rewrite HRFC; clear - Hnw Hsp1win; lia)).
    + exact (K5 a Ha ltac:(rewrite HFR; exact Hnw) Hp).
  - intros a Ha. rewrite HFR in Ha. apply Jpres4. clear - Ha Hwin1 Hwin2; lia. }
assert (HOUT4 : c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W4) mem4) (c_out c)
  (map (fun b : byte => bv_unsigned b) (c_O c))).
{ intros Ho0. apply (ho_garr_kept W2 W4 mem2 mem4 (c_out c) _); [|exact (HoutC Ho0)].
  intros i Hi. rewrite length_map in Hi.
  destruct (Houtp Ho0) as (Htout & Houth & _).
  pose proof Htout as (_ & _ & _ & _ & _ & _ & _ & _ & HOl & _ & Hofr).
  rewrite HOl in Hi.
  destruct Hofr as [(cid & pos & Hfo & Ho1 & Ho2) | (b & m & Hbo & Ho1 & Ho2)].
  - assert (Hf3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfo).
    assert (Hf2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfo).
    destruct (in_split _ _ Hfo) as (l2 & l3 & Hsplit).
    assert (Hdf : zdisjoint (frame_rng ly3 (1%Z, fpos)) (frame_rng ly3 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 _ (1%Z, fpos) (cid, pos) [] l2 l3 HAR3);
          rewrite Hfrs3, Hsplit; reflexivity).
    unfold zdisjoint, frame_rng in Hdf. cbn [fst snd] in Hdf.
    rewrite Hfa3F, HfsF, (Hfa3 cid pos), (Hfa2 cid pos) in Hdf.
    rewrite (Kd4 cid pos i Hf3).
    + apply (Kc4 cid pos i Hf2); [|apply inFP_nil].
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa2 cid pos). clear - Hi Ho1 Ho2; lia.
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite (Hfa3 cid pos), (Hfa2 cid pos). clear - Hi Ho1 Ho2; lia.
    + apply HnoW; [clear - Hi Houth; lia | clear - Hi Ho1 Ho2 Hdf; lia].
  - assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbo).
    assert (Hb3 : In (b, m) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hb2).
    assert (Hbd : zdisjoint (b, req_size m) (F, 128)).
    { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 _ b m 1 fpos HAR3 Hb3 Hfin3) as Hd.
      unfold zdisjoint in Hd |- *. cbn [fst snd] in Hd |- *. rewrite Hfa3F, HfsF in Hd. exact Hd. }
    unfold zdisjoint in Hbd. cbn [fst snd] in Hbd.
    replace i with (b + (i - b)) by (clear; lia).
    rewrite (Kd2 b m (i - b) Hb3 ltac:(clear - Hi Ho1 Ho2; lia)
              ltac:(apply HnoW; clear - Hi Ho1 Ho2 Houth Hbd; lia)).
    exact (Kc2 b m (i - b) Hb2 Hb3 ltac:(clear - Hi Ho1 Ho2; lia) ltac:(apply inFP_nil)). }
assert (Hlen4 : length (ho_Hcls c) = length (c_H c)) by (rewrite HlenHcls, HLen; reflexivity).
remember (Eimg (Ereg regs4 [])) as E4 eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs4 r)
  by (intros n r Hn; rewrite HE4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E4 10 = Z_to_bv 64 (disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c)))
  by (rewrite (EE4 10%nat 10%bv eq_refl); exact Hret4).
assert (Q2 : getr regs4 2 = w64 sp1).
{ pose proof (HP4 2 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 2) with (2%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M2, (EE3 2%nat 2%bv eq_refl). exact T2. }
assert (Q3 : getr regs4 3 = w64 (as_gp B)).
{ pose proof (HP4 3 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 3) with (3%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M3, (EE3 3%nat 3%bv eq_refl). exact T3. }
assert (Q4 : getr regs4 4 = w64 (as_tp B)).
{ pose proof (HP4 4 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 4) with (4%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M4, (EE3 4%nat 4%bv eq_refl). exact T4. }
assert (Q8 : getr regs4 8 = w64 (spZ (c_regs c))).
{ pose proof (HP4 8 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 8) with (8%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M8, (EE3 8%nat 8%bv eq_refl). exact T8. }
assert (Q9 : getr regs4 9 = w64 sp1).
{ pose proof (HP4 9 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 9) with (9%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M9, (EE3 9%nat 9%bv eq_refl). exact T9. }
assert (Q18 : getr regs4 18 = w64 F).
{ pose proof (HP4 18 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 18) with (18%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M18, (EE3 18%nat 18%bv eq_refl). exact T18. }
assert (Q22 : getr regs4 22 = w64 (c_h c)).
{ pose proof (HP4 22 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 22) with (22%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M22, (EE3 22%nat 22%bv eq_refl). exact T22. }
assert (Q26 : getr regs4 26 = w64 F).
{ pose proof (HP4 26 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 26) with (26%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M26, (EE3 26%nat 26%bv eq_refl). exact T26. }
assert (Q27 : getr regs4 27 = w64 SB).
{ pose proof (HP4 27 ltac:(unfold acallee_saved; lia)) as Y. replace (Z_to_bv 5 27) with (27%bv : bv 5) in Y by (apply bv_eq; reflexivity).
  rewrite Y, M27, (EE3 27%nat 27%bv eq_refl). exact T27. }
rewrite M1.
assert (HKB : k2 + 0 + EV_CLS <= c_k c) by (unfold EV_CLS; clear - Hk2le; lia).
destruct (HuntObsLib.cm_ret_cases (c_FB c) (ho_L c) (ho_U c) (ho_Lk c)) as [Hr0 | Hr1].
- assert (HS4 : st_ok_pi (fx := fx'') SEGS VAL E4
    (mkSS 29080 sr_atoms [] None (mkFacts [] [mkAC BC_EQ (SOff 10 0) (SLit 0)] []))
    (restrict (w_H W4) (mkst (fx := fx'') regs4 (Z_to_bv 64 (BASE + 29080)) mem4 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE4. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I|]. split; [|exact I]. split; [|exact I].
      apply (YI0m.cond_eq_lit E4 10%nat 0 0); [rewrite E10, Hr0; reflexivity | clear; lia | clear; lia | reflexivity]. }
  paj_run_to_shc RUNTOP HS4 HJ4 0x7210.
  { apply awr_ok_nil. }
  assert (Em5 : ms_mem ms1 = mem4)
    by (apply functional_extensionality; intros x; apply HF1; intros (r & Hr & _); destruct Hr).
  prreg HS4 (2%bv : bv 5) V2. prreg HS4 (3%bv : bv 5) V3. prreg HS4 (4%bv : bv 5) V4.
  prreg HS4 (8%bv : bv 5) V8. prreg HS4 (9%bv : bv 5) V9. prreg HS4 (18%bv : bv 5) V18.
  prreg HS4 (19%bv : bv 5) V19. prreg HS4 (20%bv : bv 5) V20. prreg HS4 (22%bv : bv 5) V22.
  prreg HS4 (23%bv : bv 5) V23. prreg HS4 (25%bv : bv 5) V25. prreg HS4 (26%bv : bv 5) V26.
  prreg HS4 (27%bv : bv 5) V27.
  pmkst HS4. rewrite Em5. rewrite Em5 in HJ4.
  eapply (HE0 (ho_setfq c fx'') fpos ly4 S4 W4 _ _ _ _ sp1 F).
  2: rewrite V19, (EE4 19%nat 19%bv eq_refl); exact U19.
  2: rewrite V20, (EE4 20%nat 20%bv eq_refl); exact U20.
  2: rewrite V23, (EE4 23%nat 23%bv eq_refl); exact U23.
  2: rewrite V25, (EE4 25%nat 25%bv eq_refl); exact U25.
  2: exact HFSH4.
  2: exact Hr0.
  2: exact Hhunt4.
  2: { pose proof HOut4 as HO. change (ho_Lk c) with (Some (disco_table_c.sub (c_H c) 400 12)) in HO.
       rewrite (HuntObsLib.cm_out_ok (c_FB c) (ho_L c) (ho_U c) (disco_table_c.sub (c_H c) 400 12) _ Hr0) in HO.
       exact HO. }
  2: exact HOUT4.
  apply ho_base_setfq.
  unfold ho_base, ho_mid, ho_sp1, ho_regs_mid.
  split; [exact HPRE|].
  split.
  { split; [exact HJ4|]. split; [exact Hfrs4b|]. split; [intros cid p; rewrite Hfa4; apply Hfa2|].
    split; [exact Hperm4|]. split; [exact HKEPT4|]. split; [exact HGH4|].
    split; [exact HFLG4|]. split; [exact Hlen4 | exact HKB]. }
  split; [split; [exact Hsp1eq|]; split; [exact Hsp1win | exact Hsp1mod]|].
  split; [exact HFeq|].
  split; [|exact HSAVED4].
  split; [rewrite V2, (EE4 2%nat 2%bv eq_refl); exact Q2|].
  split; [rewrite V3, (EE4 3%nat 3%bv eq_refl); exact Q3|].
  split; [rewrite V4, (EE4 4%nat 4%bv eq_refl); exact Q4|].
  split; [rewrite V8, (EE4 8%nat 8%bv eq_refl); exact Q8|].
  split; [rewrite V9, (EE4 9%nat 9%bv eq_refl); exact Q9|].
  split; [rewrite V18, (EE4 18%nat 18%bv eq_refl); exact Q18|].
  split; [rewrite V22, (EE4 22%nat 22%bv eq_refl); exact Q22|].
  split; [rewrite V26, (EE4 26%nat 26%bv eq_refl); exact Q26
         | rewrite V27, (EE4 27%nat 27%bv eq_refl); exact Q27].
- assert (HS4 : st_ok_pi (fx := fx'') SEGS VAL E4
    (mkSS 29080 sr_atoms [] None (mkFacts [] [mkAC BC_NE (SOff 10 0) (SLit 0)] []))
    (restrict (w_H W4) (mkst (fx := fx'') regs4 (Z_to_bv 64 (BASE + 29080)) mem4 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE4. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I|]. split; [|exact I]. split; [|exact I].
      apply (YI0m.cond_ne_lit E4 10%nat (2 ^ 64 - 1) 0);
      [rewrite E10, Hr1; apply bv_eq; vm_compute; reflexivity | clear; lia | clear; lia | clear; lia]. }
  paj_run_to_shc RUNTOP HS4 HJ4 0x719c.
  { apply awr_ok_nil. }
  assert (Em5 : ms_mem ms1 = mem4)
    by (apply functional_extensionality; intros x; apply HF1; intros (r & Hr & _); destruct Hr).
  prreg HS4 (2%bv : bv 5) V2. prreg HS4 (3%bv : bv 5) V3. prreg HS4 (4%bv : bv 5) V4.
  prreg HS4 (8%bv : bv 5) V8. prreg HS4 (9%bv : bv 5) V9. prreg HS4 (18%bv : bv 5) V18.
  prreg HS4 (19%bv : bv 5) V19. prreg HS4 (22%bv : bv 5) V22.
  prreg HS4 (23%bv : bv 5) V23. prreg HS4 (25%bv : bv 5) V25. prreg HS4 (26%bv : bv 5) V26.
  prreg HS4 (27%bv : bv 5) V27.
  pmkst HS4. rewrite Em5. rewrite Em5 in HJ4.
  eapply (HD (ho_setfq c fx'') fpos ly4 S4 W4 _ _ _ _ sp1 F).
  2: rewrite V19, (EE4 19%nat 19%bv eq_refl); exact U19.
  2: rewrite V23, (EE4 23%nat 23%bv eq_refl); exact U23.
  2: rewrite V25, (EE4 25%nat 25%bv eq_refl); exact U25.
  2: exact HFSH4.
  2: change (disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) <> 0); rewrite Hr1; clear; lia.
  2: exact Hhunt4.
  2: exact HOUT4.
  apply ho_base_setfq.
  unfold ho_base, ho_mid, ho_sp1, ho_regs_mid.
  split; [exact HPRE|].
  split.
  { split; [exact HJ4|]. split; [exact Hfrs4b|]. split; [intros cid p; rewrite Hfa4; apply Hfa2|].
    split; [exact Hperm4|]. split; [exact HKEPT4|]. split; [exact HGH4|].
    split; [exact HFLG4|]. split; [exact Hlen4 | exact HKB]. }
  split; [split; [exact Hsp1eq|]; split; [exact Hsp1win | exact Hsp1mod]|].
  split; [exact HFeq|].
  split; [|exact HSAVED4].
  split; [rewrite V2, (EE4 2%nat 2%bv eq_refl); exact Q2|].
  split; [rewrite V3, (EE4 3%nat 3%bv eq_refl); exact Q3|].
  split; [rewrite V4, (EE4 4%nat 4%bv eq_refl); exact Q4|].
  split; [rewrite V8, (EE4 8%nat 8%bv eq_refl); exact Q8|].
  split; [rewrite V9, (EE4 9%nat 9%bv eq_refl); exact Q9|].
  split; [rewrite V18, (EE4 18%nat 18%bv eq_refl); exact Q18|].
  split; [rewrite V22, (EE4 22%nat 22%bv eq_refl); exact Q22|].
  split; [rewrite V26, (EE4 26%nat 26%bv eq_refl); exact Q26
         | rewrite V27, (EE4 27%nat 27%bv eq_refl); exact Q27].
Qed.

End h.
End f.
End d.
