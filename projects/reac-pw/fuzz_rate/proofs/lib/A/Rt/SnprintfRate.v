(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a): the snprintf wrapper's contract at
   reac_rate_drivable_csv's call (lib/A/Rt/SnprintfRateDef.v rate_snprintf_sd_realizes), from the port of fuzz_disco's
   released ASan snprintf walk. New file, in the form of fuzz_disco's lib/A/FMsnprintfDiscoR1.v (the instance at the
   unit's pieces) and lib/A/FMsnprintfDiscoSnp.v (the instance at the unit's call) at origin/ossv/recipes 2d2ff01bb6f2.
   Rule 24: no function is proved here beyond the ported walk; this file instantiates it.
   - rate's pieces pf_rate_piece = %s and %d (the format "%s%d" parses to [Ps; Pd]), each with its four arms, taken by
     path: %s FMgxaSeamPf.v seam_*_arm_ps and RT_pf_sh.v pcom_pcx_arm_ps; %d FMpfArmPdSeam.v seam_*_arm_pd and
     RT_pf_d.v pcom_pcx_arm_Pd (disco's %02x / %llu arms are not ported: rate's format has neither);
   - rate_snprintf_gxa_AR: FMsnprintfFmI.fm_snprintf_gxaP at those pieces, at the window SNP_STK = 2 * ESTACK (the walk
     needs fm_glue_img + GXA_VF_DEPTH = 8160), on [IMG_LO, IMG_TOP) = [0x10000, 0x5fa000) (GXA's GLOBALS_TOP on IImgAG
     is 0x5fa000), in the AR form;
   - rate_snprintf_sd: the call-site lemma. It gives the shared contract's premises from the call's: the read-only
     constants over FMsnprintfCr.fm_cr from snp_rom_kept and AR (FMsnprintfRomO.fm_cr_consts_view_AR), the
     stack-protector GOT cell from AR (AE22.v got_canary_of_AR) and the value word from the image (its 8 bytes lie in
     a segment, so every view reads them), the format family from snp_cstr of the format and the separator (the rest
     of the separator's NUL word lies in the image too), the destination facts over the written part from those over
     the cell's 16 bytes. The text the walk prints is sep ++ PfFacts.pf_dec v = SnprintfRateDef.snp_text sep v
     (pf_dec and RateCsv.csv_dec have the same body: pf_dec_csv). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI04 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YImgTop YG0q YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v AF0m FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AD2l AE22 AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison PfFacts SnShared SnSx SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require FMgxaSeamPf RT_pf_sh FMsnprintfFm FMsnprintfCr
  FMsnprintfFmI FMsnprintfRomO FMgxaSeam FMpfArmPdSeam RT_pf_d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import SnprintfRateDef.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module SPf := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.FMgxaSeamPf.
Module RTS := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.RT_pf_sh.
Module FmI := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.FMsnprintfFmI.

(* ---- rate's pieces and their four arms ---- *)
Definition pf_rate_piece (p : pf_piece) : Prop :=
  match p with Pd | Ps => True | _ => False end.

Lemma rate_text_arms : forall p, pf_rate_piece p -> SPf.seam_text_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- exact FMpfArmPdSeam.seam_text_arm_pd.
- exact SPf.seam_text_arm_ps.
Qed.
Lemma rate_pargs_arms : forall p, pf_rate_piece p -> SPf.seam_pargs_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- exact FMpfArmPdSeam.seam_pargs_arm_pd.
- exact SPf.seam_pargs_arm_ps.
Qed.
Lemma rate_bytes_arms : forall p, pf_rate_piece p -> SPf.seam_bytes_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- exact FMpfArmPdSeam.seam_bytes_arm_pd.
- exact SPf.seam_bytes_arm_ps.
Qed.
Lemma rate_pcx_arms : forall p, pf_rate_piece p -> RTS.pcom_pcx_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- exact RT_pf_d.pcom_pcx_arm_Pd.
- exact RTS.pcom_pcx_arm_ps.
Qed.

(* ---- rate's snprintf on the GXA route, at rate's pieces, its image and the call's window ---- *)
#[local] Existing Instance N_img_asan_vf.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem rate_snprintf_gxa_AR : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  sh_asnprintf_realizes tfibsegs B (FmI.FF_fmP pf_rate_piece) SNP_STK FM_GOT_canary FM_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB. apply (sh_asnprintf_of_U tfibsegs B).
apply (FmI.fm_snprintf_gxaP B LAWS TB pf_rate_piece rate_text_arms rate_pargs_arms rate_bytes_arms rate_pcx_arms).
- lia.
- rewrite FMgxaSeam.sa_globals_top. lia.
- rewrite FMsnprintfFm.fm_K_min_gxa. unfold SNP_STK, ESTACK. lia.
Qed.
End f.

(* ---- the printf model's "%d" and RateCsv's have the same body ---- *)
Lemma pf_digits_csv : forall fuel x acc, pf_digits fuel x acc = RateCsv.csv_digits fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|]. cbn [pf_digits RateCsv.csv_digits].
destruct (x <? 10); [reflexivity | apply IH].
Qed.
Lemma pf_dec_csv : forall v, pf_dec v = RateCsv.csv_dec v.
Proof. intros v. unfold pf_dec, RateCsv.csv_dec. destruct (v <? 0); rewrite pf_digits_csv; reflexivity. Qed.
Lemma csv_digits_length : forall fuel x acc, (length (RateCsv.csv_digits fuel x acc) <= S fuel + length acc)%nat.
Proof.
induction fuel as [|f IH]; intros x acc; cbn [RateCsv.csv_digits]; [lia|].
destruct (x <? 10); [cbn [length]; lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.
Lemma csv_dec_length : forall v, (length (RateCsv.csv_dec v) <= 13)%nat.
Proof.
intros v. unfold RateCsv.csv_dec. destruct (v <? 0).
- cbn [length]. pose proof (csv_digits_length 11 (- v) []) as H. cbn [length] in H. lia.
- pose proof (csv_digits_length 11 v []) as H. cbn [length] in H. lia.
Qed.

(* ---- image bytes: every view reads a byte of a segment ---- *)
Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma img_vis : forall (H : word -> bool) (m : word -> option byte) a,
  YP08.img_byte_ok tfibsegs a = true -> aview tfibsegs H m a <> None.
Proof.
intros H m a Hi. unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|].
- cbn [option_map]. discriminate.
- unfold YP08.img_byte_ok, img_byte in Hi. destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; [|discriminate Hi].
  cbn [option_map]. discriminate.
Qed.
Lemma img_range_vis : forall (H : word -> bool) (m : word -> option byte) lo n,
  YP08.zallb (YP08.img_byte_ok tfibsegs) lo n = true ->
  forall a, lo <= a < lo + Z.of_nat n -> aview tfibsegs H m a <> None.
Proof. intros H m lo n Hz a Ha. apply img_vis. exact (YP08.zallb_sound _ n lo a Hz Ha). Qed.
Lemma rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
destruct (rd a) eqn:E0; [|exfalso; apply (H 0); [lia | rewrite Z.add_0_r; exact E0]].
destruct (rd (a + 1)) eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.
End v.

(* ---- the call's regions ---- *)
Lemma img_out_disj : forall ly sp d len p q, kHighMemBeg <= ly_stk_lo ly -> ly_stk_lo ly + SNP_STK <= sp ->
  (d + SNP_SIZE <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= d) -> len <= SNP_SIZE ->
  YImgTop.IMG_LO <= p -> p + q <= YImgTop.IMG_TOP ->
  Forall (zdisjoint (p, q)) (snp_out SNP_STK sp d len).
Proof.
intros ly sp d len p q Hk Hs Hd Hl Hp Hpq. unfold snp_out.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd].
- left. unfold kHighMemBeg in Hk. lia.
- unfold SNP_SIZE in *. lia.
Qed.

Lemma cstr_bytes : forall segs (H : word -> bool) mem a s, snp_cstr segs H mem a s ->
  forall i, 0 <= i <= Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0).
Proof.
intros segs H mem a s (HB & HN & _) i Hi.
destruct (Z.eq_dec i (Z.of_nat (length s))) as [->|Hne].
- rewrite HN. rewrite app_nth2 by lia. replace (Z.to_nat (Z.of_nat (length s)) - length s)%nat with 0%nat by lia.
  reflexivity.
- rewrite app_nth1 by lia. apply HB. lia.
Qed.

Lemma shadow_hull_vis_sub : forall (rd : reader) x n n', 1 <= n' <= n ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn H s Hs. apply H. split; [lia|].
assert (shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8); [|lia].
apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* ---- the call-site lemma ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem rate_snprintf_sd : rate_snprintf_sd_realizes tfibsegs AD2l.TfibB SNP_TRAMP.
Proof.
pose proof (rate_snprintf_gxa_AR AD2l.TfibB (YG0q.AR_laws_ok tfibsegs AD2l.TfibB) AD2l.TfibB_syms) as TOP.
unfold sh_asnprintf_realizes in TOP. unfold rate_snprintf_sd_realizes.
intros ly S W regs mem md d x v sep HE HK HP R10 R11 R12 R13 HX Hv R14 HF HS HRO Hd0 Hd1 DOK AMR RA SHV HW HIMG FRM.
set (T := snp_text sep v).
set (rd := aview tfibsegs (w_H W) mem).
set (len := sn_len (SNP_SIZE - 1) T).
pose proof HE as (HAR & _ & _ & _ & HSPhi & _).
pose proof HAR as (M & _). apply am_layout in M. apply lo_top in M.
assert (HSTK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (clear - M; repeat match goal with H : _ /\ _ |- _ => destruct H end; split; assumption).
destruct HSTK as [HSTKlo HSTKhi]. clear M.
assert (Hlen : 1 <= len <= SNP_SIZE).
{ unfold len, sn_len, sn_bytes. rewrite length_app, length_firstn. cbn [length]. unfold SNP_SIZE. lia. }
assert (HT : (length T <= 14)%nat).
{ unfold T, snp_text. rewrite length_app. pose proof (csv_dec_length v).
  destruct HX as [[_ ->] | [_ ->]]; cbn [length]; lia. }
assert (Hsp47 : spZ regs <= 2 ^ 47) by (unfold kHighMemEnd in HSTKhi; lia).
assert (HKpos : 0 <= SNP_STK) by (unfold SNP_STK, ESTACK; lia).
assert (DIS : forall p q, YImgTop.IMG_LO <= p -> p + q <= YImgTop.IMG_TOP ->
              Forall (zdisjoint (p, q)) (snp_out SNP_STK (spZ regs) d len)).
{ intros p q Hp Hq. exact (img_out_disj ly (spZ regs) d len p q HSTKlo HK HIMG ltac:(lia) Hp Hq). }
(* the stack-protector cells *)
assert (GC : rdword rd FM_GOT_canary = Some FM_canary).
{ apply AF0x.val_mem_rdword; [unfold FM_canary; lia|].
  exact (AE22.got_canary_of_AR AD2l.TfibB AD2l.TfibB_syms ly S W mem md HAR). }
assert (Zc : YP08.zallb (YP08.img_byte_ok tfibsegs) FM_canary 8 = true) by (vm_compute; reflexivity).
destruct (rdword_some rd FM_canary
  (fun k Hk => img_range_vis (w_H W) mem FM_canary 8 Zc (FM_canary + k) ltac:(lia)))
  as (cval & GV).
(* the arguments *)
assert (A3 : argZ regs 3 = x).
{ transitivity (bv_unsigned (getr regs 13)); [reflexivity|]. rewrite R13.
  destruct HX as [[-> _] | [-> _]]; reflexivity. }
assert (A4 : argZ regs 4 = bv_unsigned (getr regs 14)) by reflexivity.
(* the separator's facts *)
assert (SEP : pf_arg_asan rd (snp_out SNP_STK (spZ regs) d len) x (APtr sep) /\
              amem_range x (str_end x sep - x) /\ amem_range x (Z.of_nat (length sep) + 8)).
{ pose proof HS as HS'. destruct HS' as (_ & _ & Hc & Hx0 & _ & _ & Ham & Hra & Hsh).
  destruct HX as [[-> ->] | [-> ->]].
  - assert (SE : str_end SNP_EMPTY [] = 0x21708) by reflexivity.
    assert (Zs : YP08.zallb (YP08.img_byte_ok tfibsegs) SNP_EMPTY 8 = true) by (vm_compute; reflexivity).
    rewrite SE. split; [|split; unfold amem_range, kLowMemEnd, SNP_EMPTY; cbn [length]; lia].
    refine (conj Hc (conj Hx0 (conj _ (conj (cstr_bytes _ _ _ _ _ HS)
      (conj _ (conj _ (conj Ham (conj Hra Hsh)))))))).
    + cbn [length]. lia.
    + intros a Ha. cbn [length] in Ha. rewrite SE in Ha.
      apply (img_range_vis (w_H W) mem SNP_EMPTY 8 Zs). unfold SNP_EMPTY in *. lia.
    + rewrite SE. apply DIS; unfold SNP_EMPTY; lia.
  - assert (SE : str_end SNP_COMMA [44] = 0x216e8) by reflexivity.
    assert (Zs : YP08.zallb (YP08.img_byte_ok tfibsegs) SNP_COMMA 8 = true) by (vm_compute; reflexivity).
    rewrite SE. split; [|split; unfold amem_range, kLowMemEnd, SNP_COMMA; cbn [length]; lia].
    refine (conj Hc (conj Hx0 (conj _ (conj (cstr_bytes _ _ _ _ _ HS)
      (conj _ (conj _ (conj Ham (conj Hra Hsh)))))))).
    + cbn [length]. lia.
    + intros a Ha. cbn [length] in Ha. rewrite SE in Ha.
      apply (img_range_vis (w_H W) mem SNP_COMMA 8 Zs). unfold SNP_COMMA in *. lia.
    + rewrite SE. apply DIS; unfold SNP_COMMA; lia. }
destruct SEP as (SA & SL & SM).
(* the format family *)
assert (FF : FmI.FF_fmP pf_rate_piece rd (snp_out SNP_STK (spZ regs) d len) SNP_FMT
               (map (argZ regs) [3; 4; 5; 6; 7] ++ []) T).
{ exists SNP_FMT_BYTES, [Ps; Pd], [APtr sep; AInt v].
  pose proof HF as HF'. destruct HF' as (_ & _ & _ & Hf0 & _ & _ & Famr & Fra & Fsh).
  refine (conj _ (conj eq_refl (conj _ (conj _ (conj _ (conj I (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - refine (conj Hf0 (conj (cstr_bytes _ _ _ _ _ HF) (conj _ (conj Famr (conj Fra Fsh))))).
    apply DIS; unfold SNP_FMT, SNP_FMT_BYTES; cbn [length]; lia.
  - repeat constructor.
  - cbn [map app pf_args_asan]. rewrite A3. split; [exact SA|]. split; [|exact I].
    cbn [pf_arg_asan]. split; [exact Hv|]. rewrite A4. exact R14.
  - cbn [pf_text option_map]. unfold T, snp_text. rewrite pf_dec_csv, app_nil_r. reflexivity.
  - unfold SNP_FMT. lia.
  - unfold SNP_FMT, SNP_FMT_BYTES. cbn [length]. lia.
  - cbn [map app pf_args_slack]. rewrite A3. split; [exact SL | exact I].
  - unfold SNP_FMT_BYTES. discriminate.
  - cbn [map app RTS.pf_args_amem]. rewrite A3. split; [exact SM | exact I]. }
(* the read-only constants *)
assert (CV : consts_view tfibsegs W mem FMsnprintfCr.fm_cr)
  by exact (FMsnprintfRomO.fm_cr_consts_view_AR AD2l.TfibB AD2l.TfibB_syms ly S W mem md HAR HRO).
assert (CRD : Forall (fun r => Forall (zdisjoint r) (snp_out SNP_STK (spZ regs) d len)) FMsnprintfCr.fm_cr).
{ apply Forall_forall. intros r Hr.
  pose proof (proj1 (Forall_forall _ _) FMsnprintfCr.fm_cr_in_image r Hr) as Hb. cbv beta in Hb.
  destruct r as [p q]. cbn [fst snd] in Hb. apply DIS; lia. }
apply (TOP ly S W regs mem md d SNP_SIZE SNP_FMT [] (map (argZ regs) [3; 4; 5; 6; 7] ++ []) T cval
  HE HK HP R10 R11 R12 CV FMsnprintfCr.fm_cr_bounds CRD GC GV).
- unfold FM_GOT_canary. lia.
- unfold FM_GOT_canary. lia.
- unfold FM_canary. lia.
- unfold FM_canary. lia.
- apply DIS; unfold FM_GOT_canary; lia.
- apply DIS; unfold FM_canary; lia.
- split; [reflexivity|]. intros i Hi. cbn [length] in Hi. exfalso. lia.
- cbn [length]. lia.
- unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd length].
  + right. lia.
  + unfold SNP_SIZE in *. lia.
- exact FF.
- unfold SNP_SIZE. lia.
- lia.
- exact Hd0.
- unfold SNP_SIZE in *. lia.
- unfold snp_out. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint. cbn [fst snd]. unfold SNP_SIZE in *. lia.
- intros a Ha. apply DOK. unfold SNP_SIZE in *. lia.
- unfold amem_range in *. unfold SNP_SIZE in *. lia.
- intros a Ha. apply RA. unfold SNP_SIZE in *. lia.
- exact (shadow_hull_vis_sub _ d SNP_SIZE len Hlen SHV).
- unfold zdisjoint. cbn [fst snd]. unfold SNP_SIZE in *. lia.
- exact FRM.
Qed.
End s.
