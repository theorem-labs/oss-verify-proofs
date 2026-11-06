(* libreac/fuzz_boxreg, build asan-ubsan: the bridge from a Theorem Labs lane's shared snprintf contract to boxreg's B contract
   absnprintf_realizes (lib/B/Rt/SnprintfDefB.v). lib/A/Rt/SnprintfBridge.v holds the image-generic side conditions
   (snp_cr_rom, snp_cr_not_owned, snp_cr_not_errno, snp_img_word, snp_canary_ar, snp_canary_got; the reason for each is
   in its header). Until R1, absnprintf_realizes was asnprintf_realizes's text with B names, and
   boxb_absnprintf_of_shared was box_asnprintf_of_shared by conversion. R2 (abd0df80365) makes that conversion false:
   the format bound P2 is a different constant per image (f + 3 <= 0x99b40 on A, f + 3 <= 0x99f60 on B, each image's
   GOT canary slot). So boxb_absnprintf_of_shared is now proved from the image-generic bridge
   lib/A/Rt/SnprintfBridgeFm.v snp_fm_of_shared at B's own bound 0x99f60 (its family pf_family (fun p => p = Ps) by
   snp_ff_entry_ps, its constants by snp_cv_kept_of_not_owned); the result is snp_fm_realizes at 0x99f60, which is
   absnprintf_realizes by conversion. Rule 24: no function is proved here.
   fuzz_boxreg.asan-ubsan's instance: the printf core's constants sit at the asan build's addresses (GXA-FIT.md section
   2: 0x21f38, 0x22018, 0x22080, 0x22250, 0x10b54, byte-equal tables), in the read-only first segment; the canary is the
   .got word 0x99f60 (file bytes 0x5f4390) and __stack_chk_guard 0x5f4390 (.bss). The asyms instance's parts (no owned
   static and no errno byte in the constants; the .got word a const cell of B) stay premises of
   boxb_absnprintf_of_shared_img, as in the A file.
   Discharged per image in the same scratch build as the A side (a Theorem Labs lane, 2026-10-29; file kept at
   a Theorem Labs lane's boxpa/bridge-side/SnprintfSideB.v, rc=0 log
   s1x-build-20261029T031130Z.log), against the generated B
   asyms data (a Theorem Labs lane's collector/generated/B/YF0m.v, 02:21Z, placed as lib/B/AF0m.v in the scratch tree with its
   four refused numerals -- TFIB_HASH's two values and ts_junk's two bounds, none of them in Tfib_owned_static,
   Tfib_const or TFIB_ERRNO -- replaced by 0): boxb_cr_not_owned, boxb_cr_not_errno, boxb_canary_in_const (the row
   z8 (ANum 0x99f60) 0x5f4390), boxb_snp_side_of_syms and boxb_asnprintf_of_shared_syms.
   Rule-24 record: in lib/A/Rt/SnprintfBridge.v's header (one search for both files). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfBridge SnprintfBridgeFm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.libreac.fuzz_boxreg.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The bytes the shared post writes are the bytes boxreg's B post names. *)
Lemma absn_out_sn_bytes : forall n s, absn_out n s = sn_bytes (n - 1) s /\ Z.of_nat (length (absn_out n s)) = sn_len (n - 1) s.
Proof. intros n s. split; reflexivity. Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem boxb_absnprintf_of_shared : forall segs B gc gv img_lo img_hi cr pc,
AR_laws segs B ->
snp_cr_rom segs cr -> snp_cr_not_owned B cr -> snp_cr_not_errno B cr ->
snp_img_word segs gc -> snp_img_word segs gv -> snp_canary_ar segs B gc gv -> snp_img_range segs img_lo img_hi ->
sh_asnprintf_realizes segs B (pf_family (fun p => p = Ps)) (2 * ESTACK) gc gv img_lo img_hi cr pc ->
absnprintf_realizes segs B pc.
Proof.
intros segs B gc gv img_lo img_hi cr pc LAWS Hcr Hno Hne Hgc Hgv Hcan Himg HSH.
exact (snp_fm_of_shared segs B (pf_family (fun p => p = Ps)) 0x99f60 gc gv img_lo img_hi cr pc LAWS
  (snp_ff_entry_ps 0x99f60) Hcr (snp_cv_kept_of_not_owned segs B cr Hcr Hno Hne) Hgc Hgv Hcan Himg HSH).
Qed.
End b.
(* ---- fuzz_boxreg.asan-ubsan's instance ---- *)
Definition boxb_snp_cr : list (Z * Z) := [(0x21f38, 224); (0x22018, 32); (0x22080, 464); (0x22250, 16); (0x10b54, 9)].
Definition BOXB_SNP_GC : Z := 0x99f60.
Definition BOXB_SNP_GV : Z := 0x5f4390.
Lemma boxb_snp_cr_rom : snp_cr_rom boxb_segs boxb_snp_cr.
Proof.
split.
- unfold boxb_snp_cr. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
- intros a Ha. exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  apply Exists_exists in Ha as (r & Hr & Hz). unfold boxb_snp_cr in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz; lia.
Qed.
Lemma boxb_snp_img_gc : snp_img_word boxb_segs BOXB_SNP_GC.
Proof. apply snp_img_word_of_b; [unfold BOXB_SNP_GC; lia | unfold BOXB_SNP_GC; lia | vm_compute; reflexivity]. Qed.
Lemma boxb_snp_img_gv : snp_img_word boxb_segs BOXB_SNP_GV.
Proof. apply snp_img_word_of_b; [unfold BOXB_SNP_GV; lia | unfold BOXB_SNP_GV; lia | vm_compute; reflexivity]. Qed.
(* fuzz_boxreg.asan-ubsan's four loaded segments tile [IMG_LO, IMG_TOP) with no hole (same bounds as the asan
   build's, read from images.AsanUbsan by vm_compute). *)
Lemma boxb_img_cover_all : forall a, IMG_LO <= a < IMG_TOP -> in_img boxb_segs a.
Proof.
intros a Ha. unfold in_img, boxb_segs, AsanUbsan.M.loaded_segments.
assert (E0 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000) = IMG_LO) by (vm_compute; reflexivity).
assert (S0 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000) + Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000) = 0x2f000)
  by (vm_compute; reflexivity).
assert (E1 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001) = 0x2f000) by (vm_compute; reflexivity).
assert (S1 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001) + Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001) = 0x98000)
  by (vm_compute; reflexivity).
assert (E2 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002) = 0x98000) by (vm_compute; reflexivity).
assert (S2 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002) + Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002) = 0x9a000)
  by (vm_compute; reflexivity).
assert (E3 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003) = 0x9a000) by (vm_compute; reflexivity).
assert (S3 : Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003) + Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003) = IMG_TOP)
  by (vm_compute; reflexivity).
destruct (Z_lt_le_dec a 0x2f000) as [H|H]; [exists AsanUbsan.AsanUbsan_segment_000; split; [left; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x98000) as [H'|H']; [exists AsanUbsan.AsanUbsan_segment_001; split; [right; left; reflexivity | lia]|].
destruct (Z_lt_le_dec a 0x9a000) as [H''|H'']; [exists AsanUbsan.AsanUbsan_segment_002; split; [right; right; left; reflexivity | lia]|].
exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity | lia].
Qed.
(* This image's writable PT_LOADs: [0x98000, 0x9a000) (.data.rel.ro 0x98d78, .got 0x99278) and [0x9a000, IMG_TOP)
   (.data 0x9afd0, asan_globals 0x9db90, .bss 0x9dd00; last loaded byte 0x5f5c30, page-rounded), images.AsanUbsan's
   segments 002 and 003. So GLOBALS_TOP is IMG_TOP here too. *)
Definition BOXB_GLOBALS_TOP : Z := IMG_TOP.
Definition BOXB_GLOBALS_LO : Z := 0x98000.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem boxb_dest_off_globals : forall B ly S W mem md b m d w,
AR_laws boxb_segs B -> AR boxb_segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w ->
d + w <= IMG_LO \/ BOXB_GLOBALS_TOP <= d.
Proof.
intros B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw.
exact (snp_dest_off_img boxb_segs B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw boxb_img_cover_all).
Qed.
End g.
Lemma boxb_snp_img_range : snp_img_range boxb_segs BOXB_GLOBALS_LO BOXB_GLOBALS_TOP.
Proof.
split; [unfold BOXB_GLOBALS_LO, BOXB_GLOBALS_TOP; lia|]. split; [unfold BOXB_GLOBALS_TOP; lia|]. exact boxb_img_cover_all.
Qed.
Section gz. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* 401616133a7's form (zdisjoint (d, w) (img_lo, img_hi - img_lo)) at this image's writable-globals range. *)
Theorem boxb_dest_zd_globals : forall B ly S W mem md b m d w,
AR_laws boxb_segs B -> AR boxb_segs B ly S W mem md -> In (b, m) (ablocks B ly S) ->
b <= d -> d + w <= b + m -> 0 < w ->
zdisjoint (d, w) (BOXB_GLOBALS_LO, BOXB_GLOBALS_TOP - BOXB_GLOBALS_LO).
Proof.
intros B ly S W mem md b m d w LAWS HAR Hin Hbd Hdw Hw.
exact (snp_dest_zd_img boxb_segs B ly S W mem md b m d w BOXB_GLOBALS_LO BOXB_GLOBALS_TOP LAWS HAR Hin Hbd Hdw Hw
  boxb_snp_img_range).
Qed.
(* 401616133a7's premise at a call, from absnprintf_realizes's own facts (see the A file). *)
Theorem boxb_dest_zd_globals_call : forall B ly S W mem md p m d n (s : list Z),
AR_laws boxb_segs B -> AR boxb_segs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
p <= d -> d + n <= p + m -> 1 <= n ->
zdisjoint (d, sn_len (n - 1) s) (BOXB_GLOBALS_LO, BOXB_GLOBALS_TOP - BOXB_GLOBALS_LO).
Proof.
intros B ly S W mem md p m d n s LAWS HAR Hin Hpd Hdn Hn.
pose proof (snp_sn_len_bounds n s Hn) as Hw.
exact (boxb_dest_zd_globals B ly S W mem md p m d (sn_len (n - 1) s) LAWS HAR Hin Hpd ltac:(lia) ltac:(lia)).
Qed.
End gz.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem boxb_absnprintf_of_shared_img : forall B pc,
AR_laws boxb_segs B ->
snp_cr_not_owned B boxb_snp_cr -> snp_cr_not_errno B boxb_snp_cr -> snp_canary_got B BOXB_SNP_GC BOXB_SNP_GV ->
sh_asnprintf_realizes boxb_segs B (pf_family (fun p => p = Ps)) (2 * ESTACK) BOXB_SNP_GC BOXB_SNP_GV
  BOXB_GLOBALS_LO BOXB_GLOBALS_TOP boxb_snp_cr pc ->
absnprintf_realizes boxb_segs B pc.
Proof.
intros B pc LAWS Hno Hne Hgot HSH.
apply (boxb_absnprintf_of_shared boxb_segs B BOXB_SNP_GC BOXB_SNP_GV BOXB_GLOBALS_LO BOXB_GLOBALS_TOP boxb_snp_cr pc LAWS
  boxb_snp_cr_rom Hno Hne boxb_snp_img_gc boxb_snp_img_gv
  (snp_canary_ar_of boxb_segs B BOXB_SNP_GC BOXB_SNP_GV Hgot boxb_snp_img_gv) boxb_snp_img_range HSH).
Qed.
End i.
