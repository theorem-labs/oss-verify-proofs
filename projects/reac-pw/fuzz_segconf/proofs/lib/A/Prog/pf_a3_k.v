(* reac-pw/fuzz_segconf, image A: the two CALL SITES of segment A3 of reac_segconf_parse_file's walk, as
   closed lemmas over a program walk's journal. Segment A3's proof, 2026-10-30.

     a3_snp_site   0x87ce8 jal snprintf(&c->reading, 96, "%s", L)   (RtFormat.asnprintf_realizes, row 4)
     a3_mset_site  0x87d4c jal __asan_memset(cur_name, 0, 16)       (aintrin_realizes OSet)

   Each is the pattern of fuzz_command's check_reply_s4.v (snprintf: srr_art_postF_of_pf, aj_art_own_atF,
   srr_after_artF -- the destination lies in the caller's own footprint) and of PaCall.aj_intrin_atS (memset:
   the destination lies in the caller's own side-stack frame). The format family is fuzz_command's FR_cmd
   (lib/A/Rt/RtPFCmd.v): A3's one format is "%s", whose only piece is Ps, so FR_cmd covers it and the walk
   keeps the released row-4 text; the interceptor owner's wider family RtPFSeg.seg_asnprintf_realizes is not
   needed here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFPf RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaCall PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA.
(* segment A8b's snprintf step and its "%s" family fact (pfa8b_aj_snprintf_atSF, pfa8b_FR_s_regs) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a8b_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* what snprintf(d, 96, "%s", L) leaves at d, as RtPFShared.sn_bytes (96 - 1) L *)
Definition a3_Tw (LT : list Z) : list Z := firstn 95 LT.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis MSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIGMA SS___asan_memset).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the read span RtPFShared.str_end uses is seg_spec.cstr_span *)
Lemma a3_span_eq : forall (w : Z) (s : list Z), RtPFShared.str_end w s - w = seg_spec.cstr_span w s.
Proof.
intros w s. unfold RtPFShared.str_end, seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as H1.
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as H2.
set (r := (w + Z.of_nat (length s)) mod 8) in *.
assert (E : (- (w + Z.of_nat (length s) + 1)) mod 8 = (7 - r) mod 8).
{ replace (- (w + Z.of_nat (length s) + 1)) with ((7 - (w + Z.of_nat (length s))) + (-1) * 8) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, (Z.mod_small 7 8) by lia. reflexivity. }
rewrite E, (Z.mod_small (7 - r) 8) by lia. lia.
Qed.

(* the unowned read-only view, from the walk's arodata premise (SegRecImg.seg_rom_view_on's proof) *)
Lemma a3_rom_view : forall RLO RHI (W : world SEGS) mem,
  arodata_okP SEGS RLO RHI B (rdW W mem) -> RtDefs.rt_rom_view SEGS B W mem.
Proof. intros RLO RHI W mem H a Hrom Ho He. apply H; [left; exact Hrom | exact Ho | exact He]. Qed.

(* what snprintf(d, 96, ...) writes, as RtPFShared's sn_bytes / sn_len at n = 96 *)
Lemma a3_sn_bytes : forall LT, RtPFShared.sn_bytes (96 - 1) LT = a3_Tw LT ++ [0].
Proof. intros LT. reflexivity. Qed.
Lemma a3_Tw_len : forall LT, (length (a3_Tw LT) <= 95)%nat.
Proof. intros LT. unfold a3_Tw. rewrite length_firstn. lia. Qed.
Lemma a3_sn_len : forall LT, RtPFShared.sn_len (96 - 1) LT = Z.of_nat (S (length (a3_Tw LT))).
Proof. intros LT. unfold RtPFShared.sn_len. rewrite a3_sn_bytes, length_app. cbn [length]. lia. Qed.
(* the image address of the literal "%s" (SegInstA's seg_litA_rc, image A 0x21340) *)
Lemma a3_litF : seg_litA_rc F_s = 0x21340.
Proof. vm_compute. reflexivity. Qed.
(* the shadow cells of a 32-aligned frame's bytes F + 32 .. F + 47 *)
Lemma a3_shadow_sub : forall F j, F mod 32 = 0 -> 0 <= j < 16 ->
  shadow_addr (F + 32 + j) = shadow_addr F + 4 + j / 8.
Proof.
intros F j HF Hj. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
set (q := F / 32) in D. clearbody q. subst F. unfold shadow_addr.
replace (32 * q + 32 + j) with (j + (4 * q + 4) * 8) by lia.
replace (32 * q) with ((4 * q) * 8) by lia.
rewrite Z.div_add, Z.div_mul by lia. lia.
Qed.
Lemma a3_shadow_base : forall F, F mod 32 = 0 -> shadow_addr F = SHADOW_OFF + 4 * (F / 32).
Proof.
intros F HF. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
set (q := F / 32) in *. clearbody q. subst F. unfold shadow_addr.
replace (32 * q) with ((4 * q) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* ===================== 0x87ce8 : snprintf(&c->reading, 96, "%s", L) ===================== *)
Lemma a3_snp_site :
forall (W : world SEGS) (regsT : bvmap 5 word) memT sp0 ly St (W0 : world SEGS) mem md lyc Sc mdc k
       (c LP : Z) (LT : list Z) (pos o : Z) raw (pc : Z),
ajournal SEGS B STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)]
  lyc Sc W memT mdc k ->
(* the call's registers and stack offset *)
getr regsT 10 = w64 (c + seg_spec.RC_READING) -> getr regsT 11 = w64 96 ->
getr regsT 12 = w64 (seg_litA_rc F_s) -> getr regsT 13 = w64 LP ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 ->
2 * ESTACK - o <= STK_reac_segconf_parse_file ->
alloc_ceiling <= sp0 + o - 2 * ESTACK ->
(* the block c, the destination's home *)
sa_heap B lyc Sc c seg_spec.SEG_C_SIZE -> sa_addr (rdW W memT) c seg_spec.SEG_C_SIZE ->
4096 <= c -> c + seg_spec.SEG_C_SIZE <= alloc_ceiling ->
off_img c seg_spec.SEG_C_SIZE ->
(* the label text LT at LP *)
sa_str (rdW W memT) LP LT -> sa_addr (rdW W memT) LP (Z.of_nat (length LT) + 1) ->
(length LT <= 65535)%nat -> 0 < LP ->
amem_range LP (Z.of_nat (length LT) + 8) ->
LP + seg_spec.cstr_span LP LT <= alloc_ceiling ->
sa_disj LP (seg_spec.cstr_span LP LT) (c + seg_spec.RC_READING) 96 ->
(* the format literal "%s" *)
sa_lit SEGS B (rdW W memT) (seg_litA_rc F_s) F_s ->
(* printf's machine: the guard cells, the unowned read-only bytes, the rounding mode *)
sa_ssp (rdW W memT) gotwA guardA ->
arodata_okP SEGS RLO_A RHI_A B (rdW W memT) ->
PaFx.frm0 fx ->
pc = SIGMA SS___interceptor_trampoline_snprintf ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, PaFx.fxrel fx fx1 /\
 c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)]
   lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < Z.of_nat (S (length (a3_Tw LT))) ->
    rdW W mem2 (c + seg_spec.RC_READING + i) = Some (nth (Z.to_nat i) (a3_Tw LT ++ [0]) 0)) /\
 (forall a, 0 <= a < 2 ^ 64 ->
    ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
    ~ (c + seg_spec.RC_READING <= a < c + seg_spec.RC_READING + Z.of_nat (S (length (a3_Tw LT)))) ->
    rdW W mem2 a = rdW W memT a)).
Proof.
intros W regsT memT sp0 ly St W0 mem md lyc Sc mdc k c LP LT pos o raw pc
  HJ R10 R11 R12 R13 R3 R4 R1 Hraw Hsp Ho16 Ho HSTK Hceil
  Hheap _ _ _ Hoff Hstr HaddL HlenL HLP0 HamL HspanL Hdisj Hlit Hssp Hrod Hfrm Hpc.
subst pc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HK : RtPFCmd.CMD_SNP_K = 2 * ESTACK) by reflexivity.
assert (ERR : seg_spec.RC_READING = 16512) by reflexivity.
assert (EGN : seg_spec.RC_GEN = 16608) by reflexivity.
assert (ESZ : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (EkI : kImgEnd = 0x601000) by reflexivity.
pose proof (proj1 HJ) as HAR.
pose proof Hoff as Hoff'. unfold off_img in Hoff'.
(* |LT| <= 65535 as a Z bound (lia does not read the abstract nat literal) *)
assert (Hl : Z.of_nat (length LT) <= 65535).
{ apply Nat2Z.inj_le in HlenL. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity).
  rewrite E in HlenL. exact HlenL. }
pose proof (a3_Tw_len LT) as HTw.
assert (Hlen : 1 <= RtPFShared.sn_len (96 - 1) LT <= 96) by (rewrite a3_sn_len; lia).
(* the block c lies in: its bytes present, below alloc_ceiling *)
destruct Hheap as (b & m & Hbin & Hbc & Hcm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbin) as (_ & Hb4096 & Hbceil & _ & Hbp & _).
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
(* a3 holds LP *)
assert (Harg : argZ regsT 3 = LP).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite R13. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  destruct HaddL as (HL0 & HL63 & _). change (bv_modulus 64) with (2 ^ 64). lia. }
eapply SRr_mono.
{ apply (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (SIGMA SS___interceptor_trampoline_snprintf)
    (SNP fx) W regsT memT STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)]
    lyc Sc mdc k (c + seg_spec.RC_READING) 96 (seg_litA_rc F_s) LT o raw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact Ho16.
  - exact Ho.
  - rewrite HK. exact HSTK.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - (* each written byte: in the footprint's third range and in the live block c, below the window *)
    intros a Ha. split; [|rewrite HK; lia].
    right; left. split.
    + exists (c + seg_spec.RC_READING, c + seg_spec.RC_GEN + 4). split.
      * unfold seg_spec.RC_PARSE_W. right; right; left; reflexivity.
      * cbn [fst snd]. lia.
    + exists b, m. split; [exact Hbin | lia].
  - intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (Hbp a ltac:(lia))).
  - exact (amem_range_of_block SEGS B LAWS lyc Sc W memT mdc b m (c + seg_spec.RC_READING) (96 + 8) HAR Hbin
      ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdc b m (c + seg_spec.RC_READING) 96 HAR Hbin
      ltac:(lia) ltac:(lia)).
  - exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT mdc b m (c + seg_spec.RC_READING) 96 HAR Hbin
      ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (pfa8b_off_img_sub c seg_spec.SEG_C_SIZE (c + seg_spec.RC_READING) (RtPFShared.sn_len (96 - 1) LT)
      Hoff ltac:(lia) ltac:(lia) ltac:(lia)).
  - unfold RtPFCmd.CMD_IMG_HI. rewrite HK. lia.
  - exact Hssp.
  - unfold gotwA. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_HI. lia.
  - unfold guardA. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_HI. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_LO. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_LO. lia.
  - (* the family fact: "%s" with the one string argument LT at LP *)
    destruct Hlit as (Hf0 & Hfstr & Hpin & _ & _).
    pose proof (Hpin lyc Sc W memT mdc HAR) as Hfad. rewrite pfa8b_F_s_len in Hfad.
    apply (pfa8b_FR_s_regs _ _ _ LP LT regsT Harg Hf0).
    + rewrite a3_litF. unfold RtPFCmd.CMD_IMG_LO. lia.
    + rewrite a3_litF. unfold RtPFCmd.CMD_GOTW. lia.
    + exact Hfstr.
    + exact Hfad.
    + rewrite a3_litF. unfold RtPFShared.snp_out. rewrite Hsp, HK.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia|].
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor].
    + exact HLP0.
    + exact (pfa8b_bytes_range_aview SEGS (w_H W) memT LP LT Hstr).
    + lia.
    + exact Hstr.
    + exact HaddL.
    + exact HamL.
    + unfold RtPFShared.snp_out. rewrite Hsp, HK. unfold sa_disj in Hdisj.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia|].
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor].
  - lia.
  - exact (a3_rom_view RLO_A RHI_A W memT Hrod).
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP & _ & Hby & Hkeep & _ & _).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact Hfx|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split.
- intros i Hi. rewrite <- a3_sn_bytes. apply Hby. rewrite a3_sn_len. exact Hi.
- intros a Ha Hw Hd. apply Hkeep; [exact Ha | rewrite a3_sn_len; exact Hd | rewrite HK; exact Hw].
Qed.

(* ===================== 0x87d4c : __asan_memset(cur_name, 0, 16) ===================== *)
Lemma a3_mset_site :
forall (W : world SEGS) (regsT : bvmap 5 word) memT sp0 ly St (W0 : world SEGS) mem md lyc Sc mdc k
       (c : Z) (pos o : Z) raw (pc : Z),
ajournal SEGS B STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)]
  lyc Sc W memT mdc k ->
In (5, pos) (frames Sc) ->
getr regsT 10 = w64 (frame_addr lyc 5 pos + 32) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 16 ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK_reac_segconf_parse_file ->
alloc_ceiling <= sp0 + o - ESTACK ->
4096 <= frame_addr lyc 5 pos -> frame_addr lyc 5 pos + fs_frame_bytes 5 <= alloc_ceiling ->
in_app (frame_addr lyc 5 pos) (fs_frame_bytes 5) ->
(forall a, frame_addr lyc 5 pos <= a < frame_addr lyc 5 pos + fs_frame_bytes 5 ->
   ~ inFP (seg_spec.RC_PARSE_W c) a) ->
(* cur_name's two shadow cells are in scope (the run before the call wrote them) *)
(forall i, 0 <= i < 2 -> rdW W memT (shadow_addr (frame_addr lyc 5 pos) + 4 + i) = Some 0) ->
pc = SIGMA SS___asan_memset ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)]
   lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 (forall i, 0 <= i < 16 -> rdW W mem2 (frame_addr lyc 5 pos + 32 + i) = Some 0) /\
 (forall a, 0 <= a < 2 ^ 64 ->
    ~ (frame_addr lyc 5 pos + 32 <= a < frame_addr lyc 5 pos + 48) ->
    ~ (sp0 + o - ESTACK <= a < sp0 + o) -> rdW W mem2 a = rdW W memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
 same_but_materialized mdc md2).
Proof.
intros W regsT memT sp0 ly St W0 mem md lyc Sc mdc k c pos o raw pc
  HJ Hin5 R10 R11 R12 R3 R4 R1 Hraw Hsp Ho16 Ho HSTK Hceil _ _ _ HFnfp HFsh0 Hpc.
subst pc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
pose proof (proj1 HJ) as HAR.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HAR Hin5) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR Hin5) as (HFal & _ & _ & HFsh).
rewrite E5 in HFceil, HFapp, HFnfp, HFsh.
replace (2048 / 8) with 256 in HFsh by reflexivity.
eapply SRr_mono.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA SS___asan_memset) (MSET fx)
    W regsT memT STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W c) ly St W0 mem md [(5, pos)] lyc Sc mdc k
    (frame_addr lyc 5 pos + 32) 0 16 o raw HJ R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hsp Ho16 Ho HSTK
    R3 R4 R1 Hraw).
  - (* each written byte: in the walk's own class-5 frame, below the window *)
    intros a Ha. split; [|lia].
    right; right; right; left. exists 5, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite E5. lia.
  - intros a Ha Hfp. exfalso. exact (HFnfp a ltac:(lia) Hfp).
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia | lia].
  - (* the two granules' shadow cells read 0 *)
    intros x Hx. exists 0. split; [|left; reflexivity].
    assert (Ex : shadow_of_addr SHADOW_OFF x =
      shadow_addr (frame_addr lyc 5 pos + 32 + (x - frame_addr lyc 5 pos - 32))).
    { unfold shadow_of_addr, shadow_addr. f_equal. f_equal. lia. }
    rewrite Ex, (a3_shadow_sub _ (x - frame_addr lyc 5 pos - 32) HFal ltac:(lia)).
    apply HFsh0. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - (* the shadow hull: frame shadow cells, present by the frame law *)
    intros _ s Hs.
    pose proof (a3_shadow_sub _ 0 HFal ltac:(lia)) as S0. rewrite Z.add_0_r in S0.
    pose proof (a3_shadow_sub _ 15 HFal ltac:(lia)) as S15.
    replace (frame_addr lyc 5 pos + 32 + 16 - 1) with (frame_addr lyc 5 pos + 32 + 15) in Hs by lia.
    rewrite S15, S0 in Hs.
    assert (E0 : 0 / 8 = 0) by reflexivity. assert (E1 : 15 / 8 = 1) by reflexivity.
    rewrite E0, E1, Z.add_0_r in Hs.
    pose proof (a3_shadow_base _ HFal) as EsF.
    set (y := shadow_addr (frame_addr lyc 5 pos)) in *.
    pose proof (Z.div_mod (y + 4) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (y + 4) 8 ltac:(lia)) as B1.
    pose proof (Z.div_mod (y + 4 + 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (y + 4 + 1) 8 ltac:(lia)) as B2.
    assert (Hsl : y <= s < y + 256) by (unfold SHADOW_OFF in EsF; lia).
    destruct (HFsh (s - y) ltac:(lia)) as [Hp _].
    replace s with (y + (s - y)) by lia.
    exact (aview_some_of_apresent SEGS _ _ _ Hp).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Heff & Hkeep & Hpres & Hsame).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [intros i Hi; exact (Heff i Hi)|].
split; [intros a Ha H1 H2; apply Hkeep; [exact Ha | lia | exact H2]|].
split; [exact Hpres | exact Hsame].
Qed.

End e.
End f.
End d.
