(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the ENTRY STATE of segment L6x of
   LLVMFuzzerTestOneInput, the exit lane (listing +0x1c4 .. the `ret` at +0x2c4), for the lane proof in
   lib/A/Prog/Ent102L6A.v. Two lemmas:
     l6_geom     - the geometry of the fake frame this lane releases, read off the cf AR laws of
                   lib/Reusable/YG0lawscf.v (alc_frames, alc_flag, alc_sep, alc_client_img);
     l6_entry_ok - the symbolic state ss_l6 of lib/A/Prog/Ent102L6ADefs.v describes the machine at cut_exit.
   STATEMENT read: lib/A/Ent102CutsA.v (blob 2fb50b636f51: ec_rk, ec_frame, ec_saved, EC_FRAME_BYTES, LLVMF_FS_CLASS).
   LISTING: lib/A/Listing_prog.v blob 7ed1529926bd (v3; through ss_l6's pc only). The image half stays generic
   ({PA : PAImg A_prog_listing}); lib/A/PAImg_prog.v is not loaded. THE KIT TEXTS: none read here (lib/A/PRH_Base.v
   fdb45545469b and lib/A/PRH_FnPj.v 908f34f0beaa are the lane file's).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L6x (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + the internal lemma index / `proof-index LLVMFuzzerTestOneInput` exit=0, output
   the lane's index output, the internal file idx-llvm-newpin.txt; checker R24CheckLLVMF CONFIRM; NEW walk on the #102 pins).
   This file: the entry-state lemma of that segment.
   PORTED FROM (by path, image-free shape): lib/B/Prog/EntS7EntB.v of a working branch c3e54cc5ad62
   (s7_geom, s7_entry_ok; image B, old pin), at this image's register map (s2 = s11 = fk, s10 = shadow_addr fk,
   s0 = sp0) and frame (128 bytes, the saved block at sp0 - 8 .. sp0 - 104).
   NUMERALS: 128 / 120 / 104 / 16 / 8 are LENGTHs of this frame (EC_SAVE / EC_FRAME_BYTES and the saved-block slots);
   2 ^ 46, 2 ^ 47, 4096, 0x7fffff800000, 0x7fff8000 and 0x10007fff8000 are the engine's range facts (ASan constants,
   never an image address); 32768 is LLVMF_STK. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102L6ADefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section L6E. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).

(* the reader's eight bytes, in the representation the chunks are stated over *)
Lemma l6_rd64_val : forall (H : word -> bool) (m : word -> option byte) a v,
  rd64 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 8 v.
Proof.
intros H m a v Hr k Hk.
specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb;
cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hr. f_equal.
transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. exact Hr.
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. THE GEOMETRY of the fake frame the lane releases. *)
Lemma l6_geom : forall ly S Hp (W : world SEGS) mem md pos fr,
  ARcf SEGS B ly S Hp W mem md -> In (LLVMF_FS_CLASS, pos) (frames S) ->
  fr = frame_addr ly LLVMF_FS_CLASS pos ->
  fr mod 32 = 0 /\ 4096 <= fr /\ fr + EC_FRAME_BYTES <= YM05.alloc_ceiling /\ in_app fr EC_FRAME_BYTES /\
  (forall a, fr <= a < fr + EC_FRAME_BYTES ->
     apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < EC_FRAME_BYTES / 8 ->
     apresent (w_H W) mem (shadow_addr fr + i) /\ ~ aowned B ly S (shadow_addr fr + i)) /\
  apresent (w_H W) mem (flag_addr ly LLVMF_FS_CLASS pos) /\
  aowned B ly S (flag_addr ly LLVMF_FS_CLASS pos) /\
  in_app (flag_addr ly LLVMF_FS_CLASS pos) 1 /\
  flag_addr ly LLVMF_FS_CLASS pos < YM05.alloc_ceiling /\
  ~ in_img SEGS (flag_addr ly LLVMF_FS_CLASS pos) /\
  ~ (fr <= flag_addr ly LLVMF_FS_CLASS pos < fr + EC_FRAME_BYTES) /\
  ~ (shadow_addr fr <= flag_addr ly LLVMF_FS_CLASS pos < shadow_addr fr + EC_FRAME_BYTES / 8).
Proof.
intros ly S Hp W mem md pos fr HAR Hin ->.
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = EC_FRAME_BYTES) by (vm_compute; reflexivity).
assert (HFB8 : fs_frame_bytes LLVMF_FS_CLASS / 8 = 16) by (vm_compute; reflexivity).
change (EC_FRAME_BYTES / 8) with 16.
destruct (alc_frames SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md LLVMF_FS_CLASS pos HAR Hin)
  as (Hal & Happ & Hfpres & Hshpres).
destruct (alc_flag SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md LLVMF_FS_CLASS pos HAR Hin)
  as (Hgp & Hgo & Hgapp & Hgceil).
destruct (alc_sep SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md HAR) as (_ & Hfor).
rewrite Forall_forall in Hfor.
destruct (Hfor (LLVMF_FS_CLASS, pos) Hin) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
rewrite HFB in Happ, Hfpres, Hhi. rewrite HFB8 in Hshpres.
assert (HIMG : forall a, (frame_addr ly LLVMF_FS_CLASS pos <= a < frame_addr ly LLVMF_FS_CLASS pos + EC_FRAME_BYTES
                          \/ a = flag_addr ly LLVMF_FS_CLASS pos) -> ~ in_img SEGS a).
{ intros a Ha.
  assert (Hcase : (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
    (exists cid ps, In (cid, ps) (frames S) /\
       frame_addr ly cid ps <= a < frame_addr ly cid ps + fs_frame_bytes cid) \/
    (exists cid ps, In (cid, ps) (frames S) /\ a = flag_addr ly cid ps)).
  { destruct Ha as [Ha|Ha]; [right; left | right; right]; exists LLVMF_FS_CLASS, pos;
    (split; [exact Hin|]); [rewrite HFB; exact Ha | exact Ha]. }
  exact (proj2 (alc_client_img SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md a HAR Hcase)). }
split; [exact Hal|].
split; [exact Hlo|].
split; [exact Hhi|].
split; [exact Happ|].
split; [intros a Ha; destruct (Hfpres a Ha) as (P & O);
        split; [exact P|]; split; [exact O|]; apply HIMG; left; exact Ha|].
split; [exact Hshpres|].
split; [exact Hgp|].
split; [exact Hgo|].
split; [exact Hgapp|].
split; [exact Hgceil|].
split; [apply HIMG; right; reflexivity|].
split; [intros Hc; exact (proj2 (Hfpres _ Hc) Hgo)|].
intros Hc.
  assert (Hi : 0 <= flag_addr ly LLVMF_FS_CLASS pos - shadow_addr (frame_addr ly LLVMF_FS_CLASS pos) < 16)
    by lia.
  destruct (Hshpres _ Hi) as (_ & Ho). apply Ho.
  replace (shadow_addr (frame_addr ly LLVMF_FS_CLASS pos) +
           (flag_addr ly LLVMF_FS_CLASS pos - shadow_addr (frame_addr ly LLVMF_FS_CLASS pos)))
    with (flag_addr ly LLVMF_FS_CLASS pos) by lia.
  exact Hgo.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE ENTRY STATE. *)
Lemma l6_entry_ok : forall (E : ecx (L := A_prog_listing) (PA := PA)) fk ly S Hp (W : world SEGS) regs mem md pos,
  ARcf SEGS B ly S Hp W mem md -> In (LLVMF_FS_CLASS, pos) (frames S) ->
  fk = frame_addr ly LLVMF_FS_CLASS pos ->
  rd64 (aview SEGS (w_H W) mem) (fk + EC_FRAME_BYTES - 8) (flag_addr ly LLVMF_FS_CLASS pos) ->
  YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47 -> e_sp0 E mod 16 = 0 ->
  ec_rk E fk regs -> ec_frame E fk W mem ->
  st_ok_pi SEGS VAL (L6_EI (e_regs E) (flag_addr ly LLVMF_FS_CLASS pos) regs) ss_l6
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L6_K)) mem (seg_rom SEGS))).
Proof.
intros E fk ly S Hp W regs mem md pos HAR Hin Hfkeq Hflagw Rsp Hal16 HRK HFR.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HRK as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
destruct HFR as (Hsaved & Hshv & Hal32).
unfold ec_saved in Hsaved.
destruct Hsaved as (Sra & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
destruct (l6_geom ly S Hp W mem md pos fk HAR Hin Hfkeq)
  as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh & Ggp & Ggo & Ggapp & Ggceil & Gimg & Gnf & Gns).
set (flag := flag_addr ly LLVMF_FS_CLASS pos) in *.
change (EC_FRAME_BYTES / 8) with 16 in Gsh, Gns.
unfold EC_FRAME_BYTES in Gceil, Gfr, Gapp, Gnf, Hflagw.
assert (Rsp64 : 0 <= e_sp0 E < 2 ^ 64) by lia.
(* the frame's shadow lies in the shadow band, and is clear of the frame and of the stack window *)
assert (Hq0 : 0 <= fk / 8) by (apply Z.div_pos; lia).
assert (Hq8 : 8 * (fk / 8) <= fk) by (apply Z.mul_div_le; lia).
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
assert (HSHhi : shadow_addr fk + 16 <= e_sp0 E - 128).
{ rewrite Esh. unfold SHADOW_OFF. lia. }
assert (HSH0 : 0 <= shadow_addr fk) by (rewrite Esh; unfold SHADOW_OFF; lia).
assert (HSHband : 0x7fff8000 <= shadow_addr fk <= 0x10007fff8000).
{ rewrite Esh. unfold SHADOW_OFF. lia. }
assert (HSHsep : shadow_addr fk + 16 <= fk \/ fk + 128 <= shadow_addr fk).
{ rewrite Esh. destruct Gapp as (_ & [Hlow | (Hhigh & _)]);
  [right | left]; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
(* the atoms of this lane's environment *)
set (EE := L6_EI (e_regs E) flag regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew EE n = ew (Ereg regs (l6_extra (e_regs E) flag)) n)
  by (intros n Hn; unfold EE, L6_EI; apply Eimg_low; exact Hn).
assert (E8 : ew EE 8 = Z_to_bv 64 (e_sp0 E))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E18 : ew EE 18 = Z_to_bv 64 fk)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E26 : ew EE 26 = Z_to_bv 64 (shadow_addr fk))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew EE 27 = Z_to_bv 64 fk)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew EE 32 = Z_to_bv 64 flag)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew EE 33 = Z_to_bv 64 (raZ (e_regs E)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew EE 34 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 8)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew EE 35 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 9)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew EE 36 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 18)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew EE 37 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 19)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew EE 38 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 20)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew EE 39 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 21)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew EE 40 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 22)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew EE 41 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 23)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew EE 42 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 24)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew EE 43 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 25)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew EE 44 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 26)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew EE 45 = Z_to_bv 64 (bv_unsigned (getr (e_regs E) 27)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (U8 : bv_unsigned (ew EE 8) = e_sp0 E)
  by (rewrite E8; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew EE 18) = fk)
  by (rewrite E18; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew EE 26) = shadow_addr fk)
  by (rewrite E26; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew EE 27) = fk)
  by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew EE 32) = flag)
  by (rewrite E32; apply unsigned_lit_small; destruct Ggapp as (Hg4096 & _); lia).
(* a saved-block chunk: the word the prologue stored, in the chunk representation *)
assert (CHK : forall (off v a : Z) (n : nat),
  ew EE n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rd64 (aview SEGS (w_H W) mem) a v ->
  a = e_sp0 E + off ->
  YP09.chunk_ok SEGS EE (mrestrict (w_H W) mem) (e_sp0 E) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
{ intros off v a n Hn Hv Hr Ha. subst a.
  apply (YI04.chunk_ok_val SEGS EE (mrestrict (w_H W) mem) (e_sp0 E) off 8 (SOff n 0) v).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact (l6_rd64_val _ _ _ _ Hr). }
rewrite restrict_mkst_fx.
unfold ss_l6. apply pa_entry_st_ok_full.
- unfold EE, L6_EI. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold l6_regions, l6_r_saved, l6_r_shadow, l6_r_hdr, l6_r_flagptr, l6_r_flag, l6_saved_chunks.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  { rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (CHK (-8) _ _ 33%nat E33 (u64_range (getr (e_regs E) 1)) Sra ltac:(lia)).
    * exact (CHK (-16) _ _ 34%nat E34 (u64_range (getr (e_regs E) 8)) S8 ltac:(lia)).
    * exact (CHK (-24) _ _ 35%nat E35 (u64_range (getr (e_regs E) 9)) S9 ltac:(lia)).
    * exact (CHK (-32) _ _ 36%nat E36 (u64_range (getr (e_regs E) 18)) S18 ltac:(lia)).
    * exact (CHK (-40) _ _ 37%nat E37 (u64_range (getr (e_regs E) 19)) S19 ltac:(lia)).
    * exact (CHK (-48) _ _ 38%nat E38 (u64_range (getr (e_regs E) 20)) S20 ltac:(lia)).
    * exact (CHK (-56) _ _ 39%nat E39 (u64_range (getr (e_regs E) 21)) S21 ltac:(lia)).
    * exact (CHK (-64) _ _ 40%nat E40 (u64_range (getr (e_regs E) 22)) S22 ltac:(lia)).
    * exact (CHK (-72) _ _ 41%nat E41 (u64_range (getr (e_regs E) 23)) S23 ltac:(lia)).
    * exact (CHK (-80) _ _ 42%nat E42 (u64_range (getr (e_regs E) 24)) S24 ltac:(lia)).
    * exact (CHK (-88) _ _ 43%nat E43 (u64_range (getr (e_regs E) 25)) S25 ltac:(lia)).
    * exact (CHK (-96) _ _ 44%nat E44 (u64_range (getr (e_regs E) 26)) S26 ltac:(lia)).
    * exact (CHK (-104) _ _ 45%nat E45 (u64_range (getr (e_regs E) 27)) S27 ltac:(lia)). }
  { rewrite U26. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (YCbq.apresent_writable SEGS). exact (proj1 (Gsh o Ho)). }
  { rewrite U27. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (YCbq.apresent_writable SEGS).
    exact (proj1 (Gfr (fk + o) ltac:(lia))). }
  { rewrite U18. split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (YI04.chunk_ok_val SEGS EE (mrestrict (w_H W) mem) fk 120 8 (SOff 32 0) flag).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). destruct Ggapp as (Hg4096 & _). lia.
    * cbn [Z.of_N]. lia.
    * cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply l6_rd64_val.
      replace (fk + 120) with (fk + 128 - 8) by lia.
      exact Hflagw. }
  { rewrite U32. destruct Ggapp as (Hg4096 & _). split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (flag + o) with flag by lia. apply (YCbq.apresent_writable SEGS). exact Ggp. }
- apply pairwise_disjoint_of_extents.
  unfold l6_regions, l6_r_saved, l6_r_shadow, l6_r_hdr, l6_r_flagptr, l6_r_flag, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U8, U18, U26, U27, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Ggapp as (Hg4096 & _).
  repeat split; lia.
- split; [|split].
  + cbn [l6_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8, U18, U26, U27, U32.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    destruct Ggapp as (Hg4096 & _).
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
  + exact I.
  + exact I.
Qed.

End L6E.
