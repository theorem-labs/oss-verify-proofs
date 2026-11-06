(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths, module names and numbers changed; 72 of its 561 lines of code are new or changed and 2405 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s20, its
   piece s20_L1 of segment S11 of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34): the probe loop's
   head H i (0x85700) to the point A i (0x85720) after snprintf(probe, 18, "%sx", m->seg[i].name).

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/PaRt.v cwc_aj_snprintf_atSF (origin/ossv/recipes 501c0d516c69),
   which takes formats with no string argument over FR_cmd, restated as s20c_aj_snprintf_atSF over row 4 as segconf
   states it (RtPFSeg.seg_asnprintf_realizes = RtPFCmd.cmd_asnprintf_realizes at FR_seg, window SEG_SNP_K) for a
   format with ONE string argument in a3; the journal is rebuilt by PaFx.v's aj_art_own_atF (the destination is a
   byte of the walk's own side-stack frame). The run of 0x85700 .. 0x8571c, the jal included, is one plain run
   (PaCallRun.v's paj_run_shc, as _s10 runs its shadow stores with paj_run_sh: the token runner's static check
   refuses a write window inside the shadow band that no shadow entry covers) over a seed whose one region is the
   window [24, 27) at s5 = SH(FR) (the probe's three shadow bytes) and whose s6 is pinned to 2; the run has no
   instrumented check.
   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s, listing SegList.v:676-683):
     0x85700 sb zero,24(s5); sb zero,25(s5); sb s6,26(s5)      the probe in scope (shadow 00 00 02)
     0x8570c li a1,18; mv a0,s9; mv a2,s3; mv a3,s4           probe, 18, "%sx" (A_OBJ 7), &m->seg[i].name
     0x8571c jal snprintf                                     -> 0x85720 (A i) at the FP state snprintf returns *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF
PaLibG PaArt PaFx PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFPf RtPFShared RtPFCmd RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ======================================= small facts ======================================= *)
(* a reader's value is a byte *)
Lemma s20c_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof.
intros segs H mem a v Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
(* a callee-saved register a call keeps *)
Lemma s20c_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

(* ================= the snprintf wrapper with one string argument (row 4 at FR_seg), a walk step ================= *)
Section snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
#[local] Notation rdM W mem := (aview segs (w_H W) mem).

(* snprintf(d, n, f, w) for a format f whose one conversion argument is the C string s at w (a3), under row 4 as
   segconf states it (RtPFSeg.v: RtPFCmd.cmd_asnprintf_realizes at FR_seg img_lo gotw, window SEG_SNP_K =
   2 * ESTACK, the return at some FP state). PaRt.v's cwc_aj_snprintf_atSF with: the destination [d, d + n)
   bytes the journal lets the walk write, present and not the runtime's (the caller's side-stack frame, say), below
   the call's window; the format, the stack-protector cells and the read-only ranges below d; the string's bytes,
   its NUL and the slack word after it mapped (sa_str), addressable with 8 bytes past its NUL in application memory,
   apart from the destination and below the window. The step returns at some fx1 with fxrel fx fx1, keeps the
   journal at the same count, writes sn_bytes (n - 1) T at d and its window, and keeps every other byte. *)
Lemma s20c_aj_snprintf_atSF : forall img_lo img_hi cr pc gotw guard,
  @RtPFSeg.seg_asnprintf_realizes fx rc segs B img_lo img_hi cr pc gotw guard ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt qs w s T (o : Z) raw,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f -> getr regsT 13 = w64 w ->
  1 <= n < 2 ^ 31 -> 0 < d ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> RtPFSeg.SEG_SNP_K - o <= STK -> sp0 + o <= 2 ^ 47 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n ->
     awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
     writable_at segs (mrestrict (w_H W) memT) a /\ ~ aowned B lyc Sc a) ->
  d + n <= sp0 + o - RtPFSeg.SEG_SNP_K ->
  sa_addr (rdM W memT) d n -> amem_range d (n + 8) ->
  zdisjoint (d, n) (img_lo, img_hi - img_lo) ->
  Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r + snd r <= d) cr ->
  sa_ssp (rdM W memT) gotw guard -> 0 <= gotw -> gotw + 8 <= d -> 0 <= guard -> guard + 8 <= d ->
  RtDefs.rt_rom_view segs B W memT ->
  0 < f -> sa_zs (rdM W memT) f (fmt ++ [0]) -> sa_addr (rdM W memT) f (Z.of_nat (length fmt) + 1) ->
  img_lo <= f -> f + Z.of_nat (length fmt) + 1 <= gotw -> fmt <> [] ->
  RtPFSeg.seg_parse fmt = Some qs -> RtPFSeg.seg_text qs [RtPFPf.APtr s] = Some T ->
  RtPFSeg.seg_prec_pos qs [RtPFPf.APtr s] ->
  0 < w -> sa_str (rdM W memT) w s -> sa_addr (rdM W memT) w (Z.of_nat (length s) + 1) ->
  amem_range w (Z.of_nat (length s) + 8) -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  zdisjoint (w, RtPFShared.str_end w s - w) (d, n) ->
  RtPFShared.str_end w s <= sp0 + o - RtPFSeg.SEG_SNP_K ->
  Z.of_nat (length T) < 2 ^ 31 - 1 -> frm0 fx ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
  (fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
    c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    (getr regs2 10 = w64 (Z.of_nat (length T)) /\
     forall i, 0 <= i < RtPFShared.sn_len (n - 1) T ->
       rdM W mem2 (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o) ->
       ~ (d <= a < d + RtPFShared.sn_len (n - 1) T) -> rdM W mem2 a = rdM W memT a)).
Proof using LAWS segs_low.
intros img_lo img_hi cr pc gotw guard AP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f fmt qs w s T o
  raw HJ Ha0 Ha1 Ha2 Ha3 Hn Hd Hsp' Hal Hneg Hbud Hsp47 Hgp Htp Hra Hraw Hdest Hdw Hdaddr Hdamr Hdog HCR Hssp
  Hgc0 Hgc1 Hgv0 Hgv1 Hrom Hf Hfz Hfaddr Hflo Hfhi Hfne Hparse Htext Hprec Hw Hstr Hwaddr Hwamem Hslen Hwd Hws HT
  Hfrm.
assert (HK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
set (len := RtPFShared.sn_len (n - 1) T).
assert (Hlen : 1 <= len <= n).
{ unfold len, RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
destruct Hdaddr as (Hd0 & Hdn & Hdamr0 & Hdrad & Hdhull).
destruct Hfaddr as (Hf0 & Hfn & Hfamr & Hfrad & Hfhull).
destruct Hwaddr as (Hw0 & Hwn & Hwamr & Hwrad & Hwhull).
destruct Hssp as (Hgw & cval & Hcw).
destruct Hstr as ((Hwz & Hwnz) & Hwt).
assert (HPRE : RtDefs.ecall_pre_stk segs B RtPFSeg.SEG_SNP_K lyc Sc W regsT memT mdc).
{ eapply ecall_pre_stk_at; try eassumption; first [lia | rewrite Hra; exact Hraw]. }
destruct HPRE as (HEP & Hslo & Hscr).
(* what the call writes: its window and [d, d + len); everything it reads lies below d *)
assert (HOUT : forall x wd, 0 <= wd -> x + wd <= d ->
  Forall (zdisjoint (x, wd)) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)).
{ intros x wd Hwd0 Hx. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil]. }
assert (HSE : Z.of_nat (length s) + 1 <= RtPFShared.str_end w s - w <= Z.of_nat (length s) + 8).
{ unfold RtPFShared.str_end. pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
assert (HWOUT : Forall (zdisjoint (w, RtPFShared.str_end w s - w))
  (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)).
{ unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint in *. cbn [fst snd] in *. lia. }
(* the string's bytes are bytes, none of them 0 *)
assert (Hsb : Forall (fun c => 0 < c < 256) s).
{ apply Forall_forall. intros c Hc. destruct (In_nth s c 0 Hc) as (j & Hj & Ej).
  pose proof (Hwz j ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
  rewrite app_nth1 in Hb by lia. rewrite Ej in Hb.
  pose proof (s20c_aview_byte _ _ _ _ _ Hb) as Hr.
  assert (Hc0 : c <> 0) by (intros E0; apply Hwnz; rewrite <- E0; exact Hc).
  lia. }
assert (A3 : argZ regsT 3 = w).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite Ha3. unfold w64. apply unsigned_lit_small. lia. }
assert (HARGS : RtPFShared.pf_args_asan (rdM W memT) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len)
  (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) [RtPFPf.APtr s]).
{ cbn [map app RtPFShared.pf_args_asan RtPFShared.pf_arg_asan]. rewrite A3.
  split; [|exact I].
  split; [exact Hsb|]. split; [exact Hw|]. split; [exact Hslen|].
  split.
  { intros j Hj. pose proof (Hwz (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  split; [unfold RtPFShared.str_end; exact Hwt|].
  split; [exact HWOUT|]. split; [exact Hwamr|]. split; [exact Hwrad | apply Hwhull; lia]. }
assert (HFR : RtPFSeg.FR_seg img_lo gotw (rdM W memT) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d len) f
  (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T).
{ unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam. exists fmt, qs, [RtPFPf.APtr s].
  split.
  { split; [exact Hf|]. split.
    - intros j Hj. pose proof (Hfz (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia. exact Hb.
    - split; [apply HOUT; lia|]. split; [exact Hfamr|]. split; [exact Hfrad | apply Hfhull; lia]. }
  split; [exact Hparse|].
  split; [apply Forall_forall; intros q _; destruct q; exact I|].
  split; [exact HARGS|]. split; [exact Htext|]. split; [exact Hprec|].
  split; [exact Hflo|]. split; [exact Hfhi|].
  split.
  { cbn [map app RtPFCmd.cmd_args_slack]. rewrite A3. split; [|exact I].
    unfold amem_range in *. lia. }
  split; [exact Hfne|].
  cbn [map app RtPFCmd.cmd_args_amem]. rewrite A3. split; [exact Hwamem | exact I]. }
apply (aj_art_own_atF segs B LAWS segs_low RtPFSeg.SEG_SNP_K (fun a => d <= a < d + len) pc W regsT memT STK sp0 FP
  ly S W0 mem md own lyc Sc mdc k o raw
  (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length T)) /\
     forall i, 0 <= i < len -> rdM W mem' (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0))
  HJ Hsp' Hal Hneg ltac:(lia) ltac:(lia) Hra).
{ intros a Ha. exact (proj1 (Hdest a ltac:(lia))). }
apply (srr_art_postF_of_pf segs B RtPFSeg.SEG_SNP_K lyc Sc W regsT memT mdc _ d len
  (RtPFShared.sn_bytes (n - 1) T) (Z.of_nat (length T))).
{ intros a Ha. apply Hscr. exact Ha. }
apply (AP lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval HEP).
all: try fold len.
- exact Hslo.
- intros a Ha. apply Hscr. exact Ha.
- exact Ha0.
- exact Ha1.
- exact Ha2.
- exact Hrom.
- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HCR r Hr) as (H1 & H2 & H3). lia.
- apply Forall_forall. intros [x wd] Hr. pose proof (proj1 (Forall_forall _ _) HCR (x, wd) Hr) as (H1 & H2 & H3).
  cbn [fst snd] in *. apply HOUT; lia.
- exact Hgw.
- exact Hcw.
- exact Hgc0.
- lia.
- exact Hgv0.
- lia.
- apply HOUT; lia.
- apply HOUT; lia.
- split; [reflexivity | intros j Hj; cbn [length] in Hj; lia].
- cbn [length]. rewrite Hsp'. lia.
- cbn [length]. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- exact HFR.
- exact Hn.
- exact HT.
- exact Hd.
- lia.
- unfold RtPFShared.snp_out. rewrite HK, Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
  apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
- intros a Ha. destruct (Hdest a ltac:(lia)) as (_ & Hwr & Hno). split; [exact Hwr|]. split; [exact Hno|].
  rewrite Hsp'. lia.
- unfold amem_range in *. lia.
- intros x Hx. apply Hdrad. lia.
- intros sx Hsx. apply (Hdhull ltac:(lia)). split; [lia|].
  assert (E1 : (d + len - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr in *.
  assert (E2 : (SHADOW_OFF + (d + len - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8)
    by (apply Z.div_le_mono; lia).
  lia.
- unfold zdisjoint in *. cbn [fst snd] in *. lia.
- exact Hfrm.
Qed.
End snp.

(* ======================================= the walk step H i -> A i ======================================= *)
(* the seed of 0x85700: every register its own atom, one region: the window [24, 27) at s5 = SH(FR) *)
Definition s20c_shr : YP09.region := YP09.mkRegion (Some 21%nat) 24 27 24 27 [].
Definition ss_s20c : sstate := mkSS LO_H sr_atoms [s20c_shr] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s20c_seed : forall (W : world SEGS) regs mem,
  0 <= bv_unsigned (getr regs 21) + 24 -> bv_unsigned (getr regs 21) + 27 <= 2 ^ 64 ->
  (forall o, 24 <= o < 27 -> writable_at SEGS (mrestrict (w_H W) mem) (bv_unsigned (getr regs 21) + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_s20c
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_H)) mem (seg_rom SEGS))).
Proof.
intros W regs mem H0 H1 Hwr. rewrite restrict_mkst_fx. unfold ss_s20c. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, s20c_shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (ew_Eimg_Ereg_nat regs [] 21 21%bv ltac:(reflexivity)).
  split; [exact H0|]. split; [exact H1|]. split; [exact Hwr | apply Forall_nil].
- split; exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

(* the frame address of a journal's target layout is the entry's *)
Lemma s20c_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* image numbers of the runtime rows (instantiated by the close) *)
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
(* the runtime entries and callees S11 / S12 reach, at every FP state *)
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
(* row 4's image numbers (_s15's text, shared by both harness snprintf sites): the harness's formats lie in
   [snp_lo, gotwA) (FR_seg), the read-only ranges inside [snp_lo, snp_hi), and [snp_lo, snp_hi) below the
   allocator ceiling and the fake stack (dest_off_globals for a destination in the class-3 frame); at image A
   snp_lo := 0x10000, snp_hi := YG0f.kImgEnd, each a computation *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
(* the walk hypotheses (the close discharges them at image A) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* the entry sp and the realigned base S1 (_s12's lk_sp) *)
Lemma s20c_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* the class-3 frame of a state the journal reaches: its address, its place in the fake stack (above the image and
   row 4's snp_hi), its bytes and its 64 shadow bytes present and not the runtime's *)
Lemma s20c_frame_at : forall cx ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\ In (LT_FCLS, x_fpos cx) (frames S) /\
  snp_hi <= ly_F ly /\ ly_F ly <= x_fr cx /\ kImgEnd <= ly_F ly /\ 4096 <= x_fr cx /\
  x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (forall j, 0 <= j < 64 -> apresent (w_H W) mem (x_sh cx + j) /\ ~ aowned B ly S (x_sh cx + j)).
Proof.
intros cx ly S W mem md k HJ.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20c_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : x_fr cx = ly_F ly + fs_frame_off LT_FCLS (x_fpos cx)) by (rewrite <- EF; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (_ & Happ & Hpres & Hspres).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (H4096 & Hceil & _).
destruct (frame_facts B ly S _ LT_FCLS (x_fpos cx) (proj1 HAR) HinF) as (Hc & Hp & HFapp & HNO & _ & Hoff & _).
destruct (pa_img_cover ly S md (proj1 (proj2 HAR))) as [IC1 IC2].
pose proof (HSNP_FAKE ly S W mem md HAR) as HFK.
assert (F512 : fs_frame_bytes LT_FCLS = 512) by reflexivity.
rewrite EF, F512 in Happ, Hpres, Hceil. rewrite EF in H4096. rewrite EF, F512 in Hspres.
change (512 / 8) with 64 in Hspres.
unfold kFakeFramesOff, LT_FCLS in Hoff.
assert (HFimg : kImgEnd <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) kImgEnd) as [Hlt|Hge]; [exfalso|exact Hge].
  apply HNO. exists (Z.max (ly_F ly) 0x10000). unfold in_zr. cbn [fst snd].
  destruct HFapp as [HF1 _]. unfold kFakeStackSize, kImgEnd in *. split; [lia | left; lia]. }
split; [exact EF|]. split; [exact HinF|]. split; [exact HFK|].
split; [unfold LT_FCLS in EF2; lia|]. split; [exact HFimg|]. split; [exact H4096|]. split; [exact Hceil|].
split; [exact Happ|]. split; [exact Hpres|]. unfold x_sh. exact Hspres.
Qed.

(* m->seg[i].name through the reader of a state where m is a harness block holding the model state mc: a C string
   of at most 15 bytes inside m's entry i, its slack word mapped, addressable, 8 bytes past its NUL in application
   memory *)
Lemma s20c_name : forall ly S (W : world SEGS) mem md m mc i,
  AR SEGS B ly S W mem md -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  sa_mconf (rdW W mem) m mc -> (i < length (SegModel.mc_seg mc))%nat ->
  0 < seg_spec.mseg_addr m i /\ m <= seg_spec.mseg_addr m i /\
  seg_spec.mseg_addr m i + 256 <= m + seg_spec.SEG_M_SIZE /\
  (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) < 16)%nat /\
  sa_str (rdW W mem) (seg_spec.mseg_addr m i) (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)) /\
  sa_addr (rdW W mem) (seg_spec.mseg_addr m i)
    (Z.of_nat (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d))) + 1) /\
  amem_range (seg_spec.mseg_addr m i)
    (Z.of_nat (length (SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d))) + 8).
Proof.
intros ly S W mem md m mc i HAR Hhb Hmc Hi.
destruct Hhb as (Hin & H4096 & H16 & _).
pose proof asan_consts as (C1 & _).
assert (Hn32 : (length (SegModel.mc_seg mc) <= 32)%nat) by (eapply proj2; eapply s20_mconf_n; eassumption).
set (nm := SegModel.ms_name (nth i (SegModel.mc_seg mc) SegModel.mseg_d)).
assert (HNM : sa_zs (rdW W mem) (seg_spec.mseg_addr m i) (nm ++ [0]) /\ ~ In 0 nm /\ (length nm < 16)%nat /\
  (forall j, 0 <= j < 16 -> rdW W mem (seg_spec.mseg_addr m i + j) <> None))
  by (eapply s20_mconf_name; eassumption).
destruct HNM as (Hzs & Hn0 & Hl16 & Hmap).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreq].
pose proof (al_blocks _ _ LAWS ly S W mem md m _ HAR Hin) as (_ & _ & Hceil & _).
assert (Ew : seg_spec.mseg_addr m i = m + 256 * Z.of_nat i) by reflexivity.
assert (Hw8 : exists q, seg_spec.mseg_addr m i = 8 * q).
{ exists (2 * (m / 16) + 32 * Z.of_nat i). rewrite Ew. pose proof (Z.div_mod m 16 ltac:(lia)). lia. }
destruct Hw8 as (q & Hq).
assert (Hlim : seg_spec.mseg_addr m i + 256 <= m + seg_spec.SEG_M_SIZE)
  by (rewrite Ew; unfold seg_spec.SEG_M_SIZE; lia).
split; [lia|]. split; [lia|]. split; [exact Hlim|]. split; [exact Hl16|].
split.
{ split; [split; [exact Hzs | exact Hn0]|].
  intros x Hx.
  pose proof (Z.div_mod (seg_spec.mseg_addr m i + Z.of_nat (length nm)) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (seg_spec.mseg_addr m i + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
  assert (Hj : 0 <= x - seg_spec.mseg_addr m i < 16) by lia.
  pose proof (Hmap _ Hj) as Hx'.
  replace (seg_spec.mseg_addr m i + (x - seg_spec.mseg_addr m i)) with x in Hx' by lia.
  exact Hx'. }
split.
{ split; [lia|]. split; [lia|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia]|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia]|].
  intros Hpos. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE);
    [exact HAR | exact Hin | lia | lia | lia]. }
apply (amem_range_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE); [exact HAR | exact Hin | lia | lia].
Qed.

(* ---- H i -> A i: the probe in scope, a1 = 18, a0 = the probe, a2 = "%sx", a3 = &m->seg[i].name, snprintf ---- *)
Lemma s20_L1 : forall i, S20A_A B MT i -> S20_H_stmt B MT i.
Proof.
intros i HAA. unfold S20_H_stmt.
intros cx ly S W regs mem md k acc c m HB Hfrm Hlt Hctx HL.
pose proof Hctx as (HC & _ & _ & _ & _).
pose proof HC as (HF & _ & _ & _).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HL as (R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (s20c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HFM : LTOI_FRAME_MAX = 336) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s20c_frame_at cx ly S W mem md k HJ) as (EF0 & _ & _ & _ & _ & HF4096 & HFceil & _ & _ & HSP0).
assert (USH : bv_unsigned (getr regs 21) = x_sh cx).
{ rewrite R21. unfold w64. apply unsigned_lit_small. unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
(* the seed: s5's window [24, 27) is the probe's shadow, present; s6 pinned to 2 *)
pose proof (s20c_seed W regs mem) as HS0.
specialize (HS0 ltac:(rewrite USH; unfold x_sh, shadow_addr, SHADOW_OFF; lia)
  ltac:(rewrite USH; unfold x_sh, shadow_addr, SHADOW_OFF; lia)).
specialize (HS0 ltac:(intros o Ho; rewrite USH; apply (apresent_writable SEGS); exact (proj1 (HSP0 o ltac:(lia))))).
pose proof (st_ok_pi_pin_reg' _ _ _ 22%bv 2 HS0 R22 eq_refl) as HS. clear HS0.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr)
  by (intros n rr Hn; exact (ew_Eimg_Ereg_nat regs [] n rr Hn)).
assert (U21 : bv_unsigned (ew (Eimg (Ereg regs [])) 21) = x_sh cx)
  by (rewrite (EEo 21%nat 21%bv ltac:(reflexivity)); exact USH).
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x85700 .. 0x8571c: the probe's three shadow bytes 00 00 02, a1 := 18, a0 := s9, a2 := s3, a3 := s4, jal snprintf *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
  exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
  rewrite EF0. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
(* the stored bytes: the region's chunks at the call *)
lazymatch type of HS with st_ok _ _ ?ssB _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth _ ssB _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as RSH end.
destruct RSH as (_ & _ & _ & CSH).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH. rewrite U21 in CSH.
pose proof (s10_zs_ok _ (w_H W) _ (x_sh cx) _ [0; 0; 2] 24 CSH ltac:(vm_compute; reflexivity)) as HZS.
(* the registers at the call *)
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; first [apply EEo; reflexivity | rewrite R22; reflexivity] | ]).
  destruct Hr. }
pmkst HS.
(* the memory after the run: only the three shadow bytes changed *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 24 <= a < x_sh cx + 27) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W) mem (ms_mem ms) (fun y => x_sh cx + 24 <= y < x_sh cx + 27) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in
    change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U21 in Hx.
  cbv beta. lia. }
assert (RK1 : s20_rkept regs (ms_regs ms)).
{ split; [apply KR; cbn; tauto|]. split; [apply KR; cbn; tauto|]. split; [apply KR; cbn; tauto|].
  split; [apply KR; cbn; tauto | apply KR; cbn; tauto]. }
(* s20_ctx with the probe in scope *)
assert (Hctx1 : s20_ctx B MT cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc LFO_P c m).
{ eapply s20_ctx_store; try eassumption; first [exact RK1 | exact KEEP | reflexivity | exact HZS]. }
pose proof Hctx1 as (HC1 & HHc1 & HHm1 & HSL1 & HCM1).
pose proof HC1 as (HF1 & HI1 & HBL1 & HBUD1).
pose proof (proj1 HJ) as HAR1.
pose proof (s20c_frame_at cx ly S W (ms_mem ms) md1 k HJ)
  as (EF & HinF & HFK & HFF & HFimg & HF4096' & HFceil' & HFapp & HFpres & _).
assert (HPA : sa_addr (rdW W (ms_mem ms)) (s20_probe cx) 18).
{ eapply s20_probe_addr; first [exact HF1 | reflexivity | eassumption]. }
pose proof (s20c_name ly S W (ms_mem ms) md1 m (x_mcF cx) i HAR1 HHm1 (proj2 HCM1) Hlt)
  as (Hw0 & Hwm & Hwlim & Hnl & Hstr & Hwaddr & Hwamem).
pose proof (al_blocks _ _ LAWS ly S W (ms_mem ms) md1 m seg_spec.SEG_M_SIZE HAR1 (proj1 HHm1))
  as (_ & _ & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS ly S W (ms_mem ms) md1 m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR1
  (proj1 HHm1) HinF) as Hsep.
rewrite EF in Hsep. change (fs_frame_bytes LT_FCLS) with 512 in Hsep.
(* the image facts at the call: the format, the stack-protector cells, the read-only view *)
destruct HI1 as (HRO & HIM & _).
destruct HIM as (_ & _ & Hfz & _ & _ & _ & _ & _ & Hssp & _).
assert (HLIT : In LIT_PROBE LTOI_FZ_LITS)
  by (unfold LTOI_FZ_LITS; apply in_or_app; left; unfold LTOI_LITS; cbn [In]; tauto).
destruct (Hfz LIT_PROBE HLIT) as ((Hf0 & ((Hfzs & _) & _) & Hpin & _) & _).
pose proof (Hpin ly S W (ms_mem ms) md1 HAR1) as Hfaddr.
destruct (HSNP_LIT LIT_PROBE ltac:(unfold LTOI_LITS; cbn [In]; tauto)) as [Hflo Hfhi].
assert (EF7 : VAL (A_OBJ 7) = seg_litA_fz LIT_PROBE).
{ rewrite (VOBJS 7%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. }
assert (ELP : LIT_PROBE = [37; 115; 120]) by (vm_compute; reflexivity).
assert (HROM : RtDefs.rt_rom_view SEGS B W (ms_mem ms)).
{ intros a Ha Ho He. apply HRO; [left; exact Ha | exact Ho | exact He]. }
(* the text: the name and 'x', at most 16 bytes, so all of it and its NUL are written *)
assert (HTlen : (length (s20_T cx i) <= 16)%nat)
  by (unfold s20_T; rewrite length_app; cbn [length]; unfold x_seg; lia).
assert (Esb : RtPFShared.sn_bytes (18 - 1) (s20_T cx i) = s20_T cx i ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity|]. change (Z.to_nat (18 - 1)) with 17%nat. lia. }
assert (Esl : RtPFShared.sn_len (18 - 1) (s20_T cx i) = Z.of_nat (length (s20_T cx i)) + 1).
{ unfold RtPFShared.sn_len. rewrite Esb, length_app. cbn [length]. lia. }
assert (Hpr : s20_probe cx = x_fr cx + 192) by reflexivity.
assert (Usp : spZ (ms_regs ms) = x_s1 cx).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
eapply SRr_bind.
{ apply (s20c_aj_snprintf_atSF SEGS B LAWS pa_segs_low snp_lo snp_hi snp_cr _ gotwA guardA (ASNPRINTF fx)
    W (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md1 k (s20_probe cx) 18 (VAL (A_OBJ 7)) LIT_PROBE
    [RtPFSeg.PRel RtPFPf.Ps; RtPFSeg.PRel (RtPFPf.PLit 120)] (seg_spec.mseg_addr m i)
    (SegModel.ms_name (nth i (SegModel.mc_seg (x_mcF cx)) SegModel.mseg_d))
    (s20_T cx i) (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + LO_A)) HJ).
  - rewrite P10, (EEo 25%nat 25%bv ltac:(reflexivity)). exact R25.
  - rewrite P11. reflexivity.
  - rewrite P12, (EEo 19%nat 19%bv ltac:(reflexivity)). exact R19.
  - rewrite P13, (EEo 20%nat 20%bv ltac:(reflexivity)). exact R20.
  - lia.
  - rewrite Hpr. lia.
  - rewrite Usp. lia.
  - pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)). pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)).
    apply Z.mod_divide; [lia|]. exists (2 * (x_s1 cx / 32) - x_sp0 cx / 16). lia.
  - lia.
  - unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - lia.
  - rewrite (KR 3%bv ltac:(cbn; tauto)), R3. exact Hgp0.
  - rewrite (KR 4%bv ltac:(cbn; tauto)), R4. exact Htp0.
  - exact P1.
  - apply ret_ok_codeptr_v; [unfold LO_A; lia | reflexivity].
  - intros a Ha. rewrite Hpr in Ha.
    destruct (HFpres a ltac:(lia)) as [Hap Hno].
    split; [|split; [exact (apresent_writable SEGS _ _ _ Hap) | exact Hno]].
    right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left.
    rewrite EF. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LT_FCLS) with 512. lia.
  - rewrite Hpr. unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - exact HPA.
  - rewrite Hpr. destruct HFapp as [HA1 [HA2 | [HA3 HA4]]];
      unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
  - unfold zdisjoint. cbn [fst snd]. rewrite Hpr. right. lia.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HSNP_CR r Hr) as (H1 & H2 & H3).
    rewrite Hpr. lia.
  - exact Hssp.
  - unfold gotwA. lia.
  - rewrite Hpr. unfold gotwA, kImgEnd in *. lia.
  - unfold guardA. lia.
  - rewrite Hpr. unfold guardA, kImgEnd in *. lia.
  - exact HROM.
  - rewrite EF7. exact Hf0.
  - rewrite EF7. exact Hfzs.
  - rewrite EF7. exact Hfaddr.
  - rewrite EF7. exact Hflo.
  - rewrite EF7. exact Hfhi.
  - rewrite ELP. discriminate.
  - rewrite ELP. vm_compute. reflexivity.
  - reflexivity.
  - exact I.
  - exact Hw0.
  - exact Hstr.
  - exact Hwaddr.
  - exact Hwamem.
  - lia.
  - unfold zdisjoint in Hsep |- *. cbn [fst snd] in Hsep |- *. rewrite Hpr. unfold RtPFShared.str_end.
    lazymatch goal with |- context [?e mod 8] => pose proof (Z.mod_pos_bound e 8 ltac:(lia)) end.
    lia.
  - unfold RtPFShared.str_end.
    lazymatch goal with |- context [?e mod 8] => pose proof (Z.mod_pos_bound e 8 ltac:(lia)) end.
    unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - lia.
  - exact Hfrm. }
intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & (H10 & HBY) & HKP).
rewrite Esl in HBY, HKP. rewrite Esb in HBY.
(* the callee-saved registers *)
assert (KR2 : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r z Hz Hr; exact (s20c_pres_reg _ _ r z HP2 Hz Hr)).
assert (RK2 : s20_rkept (ms_regs ms) regs2).
{ unfold s20_rkept.
  rewrite (KR2 2%bv 2), (KR2 3%bv 3), (KR2 4%bv 4), (KR2 8%bv 8), (KR2 9%bv 9)
    by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  repeat (split; [reflexivity|]). reflexivity. }
assert (KPT : s20_kept B cx c m W (ms_mem ms) W mem2).
{ eapply s20_kept_of_win with (lo := x_s1 cx - RtPFSeg.SEG_SNP_K); try eassumption.
  - unfold RtPFSeg.SEG_SNP_K, ESTACK. lia.
  - intros a Ha H1 H2. apply HKP; [exact Ha | |].
    + intros Hq. apply H1. unfold RtPFSeg.SEG_SNP_K, ESTACK in *. lia.
    + intros Hq. apply H2. lia. }
assert (Hctx2 : s20_ctx B MT cx ly S W regs2 mem2 md2 k acc LFO_P c m).
{ eapply s20_ctx_carry; try eassumption; first [exact RK2 | exact KPT | apply Permutation_refl]. }
unfold lt_post. eapply (srr_apost_baseF_lift _ fx1); [exact Hfx|].
apply (HAA fx1 cx ly S W regs2 mem2 md2 k acc c m HB (fxrel_frm0 fx fx1 Hfrm Hfx) Hlt Hctx2).
- unfold s20_lregs.
  rewrite (KR2 18%bv 18), (KR2 19%bv 19), (KR2 20%bv 20), (KR2 21%bv 21), (KR2 22%bv 22), (KR2 23%bv 23),
    (KR2 25%bv 25), (KR2 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite (KR 18%bv ltac:(cbn; tauto)), (KR 19%bv ltac:(cbn; tauto)), (KR 20%bv ltac:(cbn; tauto)),
    (KR 21%bv ltac:(cbn; tauto)), (KR 22%bv ltac:(cbn; tauto)), (KR 23%bv ltac:(cbn; tauto)),
    (KR 25%bv ltac:(cbn; tauto)), (KR 26%bv ltac:(cbn; tauto)).
  split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
  split; [exact R22|]. split; [exact R23|]. split; [exact R25 | exact R26].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  pose proof (HBY (Z.of_nat j) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. exact Hb.
Qed.

End e.
End f.
End d.
