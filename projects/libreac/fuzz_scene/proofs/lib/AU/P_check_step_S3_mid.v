(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v, with its module paths and module names changed; 246 of its 293 lines of code are new or changed and 163 lines of the source are left out. *)
(* The middle of segment S3 of the asan-ubsan walk of check_step (a Theorem Labs lane, 2026-10-29; fuzz_scene.asan-ubsan,
   sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f), proved, and used by a Theorem Labs lane's cs_S3.
   Rule 24 is met: this is part of one segment of the walk; reac_ctrl_parse is the Section hypothesis PARSE.
   Range: the return of the second __asan_memcpy (0x83678 = check_step + 0x3e4) to the return of reac_ctrl_parse
   (0x836a0 = check_step + 0x40c):
     0x83678 sb zero,0x10(s9) .. sb zero,0x13(s9)      the shadow of p = F + 128: 4 x 00
     0x83688 li a0,4; sb a0,0x14(s9)                   then 04 (p is 36 bytes)
     0x83690 li a1,50; mv a0,s6; mv a2,s7; jal reac_ctrl_parse   (f = F + 32, n = 50, o = F + 128)
   with s9 = SHADOW_OFF + F / 8 (x25), s6 = F + 32 (x22), s7 = F + 128 (x23), F = check_step's class-2 fake frame.
   The post is exactly the premise list of s3u_tail (a Theorem Labs lane, lib/AU/P_check_step_S3_aux.v, the statement of
   TAIL.md (sha256 6abba4a46cee; internal record)) after cs_pre, at the parse return, so cs_S3 chains the two with
   SRr_bind. The symbolic run at 0x83678: atoms 0..31 are the registers; one region, the shadow bytes 16..20 of the
   own frame (base atom 25 = s9), writable. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC45 SceneACjr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step_S3_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The symbolic state at 0x83678 (AF_check_step + 0x3e4). *)
Definition S3M_PC : Z := AF_check_step + 0x3e4.
Definition s3m_regions : smem := [ YP09.mkRegion (Some 25%nat) 16 21 16 21 [] ].
(* Granules of an 8-aligned frame. *)
Lemma s3m_rng : forall F x lo hi, 8 * (F / 8) = F -> F + 8 * lo <= x < F + 8 * hi -> F / 8 + lo <= x / 8 < F / 8 + hi.
Proof.
intros F x lo hi HF Hx. split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma s3m_gran : forall F x j, 8 * (F / 8) = F -> F + 8 * j <= x < F + 8 * j + 8 -> x / 8 = F / 8 + j /\ x mod 8 = x - F - 8 * j.
Proof.
intros F x j HF Hx. split.
- symmetry. apply (Z.div_unique x 8 (F / 8 + j) (x - F - 8 * j)); lia.
- symmetry. apply (Z.mod_unique x 8 (F / 8 + j) (x - F - 8 * j)); lia.
Qed.
(* range_addressable moves to a reader that agrees on the shadow bytes of the range. *)
Lemma s3m_ra_transfer : forall (rd rd' : Z -> option Z) Bs p n,
range_addressable rd Bs p n -> (forall x, p <= x < p + n -> rd' (shadow_of_addr Bs x) = rd (shadow_of_addr Bs x)) ->
range_addressable rd' Bs p n.
Proof.
intros rd rd' Bs p n HR Hk x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [rewrite Hk by exact Hx; exact Hs | exact Hok].
Qed.
(* An application byte of a frame in the application range is not a shadow byte of that frame. *)
Lemma s3m_sep {rc : YM05.RunCeil} : forall F a j, 8 * (F / 8) = F -> 4096 <= F -> F + 256 <= alloc_ceiling ->
(F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F) -> 0 <= j < 32 -> F <= a < F + 256 -> a <> SHADOW_OFF + F / 8 + j.
Proof.
intros F a j HF H4 Hc Happ Hj Ha. pose proof asan_consts as (C1 & _).
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* LAWS is a theorem, not a hypothesis (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803). *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* reac_ctrl_parse: a Theorem Labs lane (8cd86323565). *)
Hypothesis PARSE : tctrl_parse_spec (SK := SK) B.
Lemma s3u_mid : forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
  ly3 S3 (W3 : world SEGS) (regs3 : bvmap 5 word) mem3 md3,
  cs_pre B ly S W regs mem md ch blk body k b ->
  cs_frame SK B regs ly S W mem md fpos ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 20 = w64 2 ->
  getr regs3 21 = w64 (scene_seg k) -> getr regs3 24 = w64 (scene_len k) ->
  getr regs3 22 = w64 (frame_addr ly3 CS_CID fpos + 32) -> getr regs3 23 = w64 (frame_addr ly3 CS_CID fpos + 128) ->
  (forall i, (i < 50)%nat -> aview SEGS (w_H W3) mem3 (frame_addr ly3 CS_CID fpos + 32 + Z.of_nat i) =
     Some (cp_v (s3_fr b k) i)) ->
  range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (frame_addr ly3 CS_CID fpos + 32) 50 ->
  SRr SEGS W3 (cfg_at SEGS (A_check_step + 0x3e4) regs3 mem3 md3)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS (A_check_step + 0x40c) regs2 mem2 md2 /\
       cs_frame SK B regs ly S W mem md fpos ly2 S2 W2 regs2 mem2 md2 /\
       getr regs2 10 = w64 2 /\ getr regs2 20 = w64 2 /\
       getr regs2 21 = w64 (scene_seg k) /\ getr regs2 24 = w64 (scene_len k) /\
       getr regs2 22 = w64 (frame_addr ly2 CS_CID fpos + 32) /\ getr regs2 23 = w64 (frame_addr ly2 CS_CID fpos + 128) /\
       (forall i, (i < 36)%nat -> aview SEGS (w_H W2) mem2 (frame_addr ly2 CS_CID fpos + 128 + Z.of_nat i) =
          Some (bv_unsigned (nth i (snd (ctrlparse 50 (s3_fr b k))) cp_z))) /\
       (forall i, (i < 50)%nat -> aview SEGS (w_H W2) mem2 (frame_addr ly2 CS_CID fpos + 32 + Z.of_nat i) =
          Some (cp_v (s3_fr b k) i)) /\
       range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CS_CID fpos + 32) 50).
Proof.
intros ly S W regs mem md ch blk body k b fpos ly3 S3 W3 regs3 mem3 md3 HP HFR R20 R21 R24 R22 R23 HFB HFRA.
pose proof HP as (HPRE & Hal32 & Htop32 & Hfr7 & HROD & H10 & H11 & H12 & Hk & HFO & Hbody & Hlen & Hbb & Hblk & Hev & Hlive).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HFR as (HJ & Hablk & Hflagw & Hsaved & Q2 & Q3 & Q4 & Q8 & Q18 & Q25 & Q26 & Q27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_scene)) as HBLO.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & ETOP3 & _).
assert (Hin3 : In (CS_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR3 Hin3) as (HF64 & _ & _).
change (fs_frame_bytes CS_CID) with 256 in *. change (256 / 8) with 32 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
remember (frame_addr ly3 CS_CID fpos) as F eqn:EF.
assert (HF8 : 8 * (F / 8) = F).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (HFapp' : F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F) by (unfold kLowShadowBeg, kHighMemBeg; lia).
assert (Hsp8 : spZ regs mod 8 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
  replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
(* the environment: atoms 0..31 the registers at 0x83678 *)
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E25 : ew E 25 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (rewrite (EE 25%nat 25%bv eq_refl); exact Q25).
assert (USH : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS S3M_PC sr_atoms s3m_regions None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + S3M_PC)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s3m_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite USH. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). pose proof (proj1 (HFSpres o ltac:(lia))) as Hp.
    unfold shadow_addr in Hp. exact Hp.
  - unfold s3m_regions. cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
clear HE.
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
  replace pcw with (Z_to_bv 64 (BASE + S3M_PC)) by (unfold S3M_PC, A_check_step, w64; rewrite Z.add_assoc; reflexivity) end.
pose proof (SRr_run_pi_AJ (PL := PL_scene) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (PL := PL_scene) (PI := PI) B LAWS) as RUNC.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Hr). cbn [ss_mem] in Hin. unfold s3m_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite USH in Hr.
  right. right. right. exists CS_CID, fpos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID / 8) with 32. lia. }
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msC end.
lazymatch goal with HF : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HF into HFr end.
(* what the run kept: everything outside s9 + [16, 21) *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 16 <= a < SHADOW_OFF + F / 8 + 21) ->
  aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr). cbn [ss_mem] in Hin. unfold s3m_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite USH in Hr. lia. }
(* the shadow of p the run wrote *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRsh. cbn [ms_mem restrict] in HRsh.
assert (ZS0 : forall j, 16 <= j < 20 -> aview SEGS (w_H W3) (ms_mem msC) (SHADOW_OFF + F / 8 + j) = Some 0).
{ intros j Hj. assert (Hj4 : j = 16 \/ j = 17 \/ j = 18 \/ j = 19) by lia.
  destruct Hj4 as [-> | [-> | [-> | ->]]];
  (apply (aview_of_val_mem1 SEGS); [| lia];
   eapply (field_of_region E _ 25 (SHADOW_OFF + F / 8) _ _ _ _ _ _ 1%N _ _ HRsh);
   [exact USH | cbn; tauto | reflexivity | cbn; lia | cbn; lia]). }
assert (ZS4 : aview SEGS (w_H W3) (ms_mem msC) (SHADOW_OFF + F / 8 + 20) = Some 4).
{ apply (aview_of_val_mem1 SEGS); [| lia].
  eapply (field_of_region E _ 25 (SHADOW_OFF + F / 8) _ _ _ _ _ _ 1%N _ _ HRsh);
  [exact USH | cbn; tauto | reflexivity | cbn; lia | cbn; lia]. }
assert (HRAo : range_addressable (aview SEGS (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 128) 36).
{ intros x Hx. unfold shadow_of_addr.
  destruct (Z_lt_ge_dec x (F + 160)) as [Hlt | Hge].
  - exists 0. split; [|left; reflexivity].
    pose proof (s3m_rng F x 16 20 HF8 ltac:(lia)) as Hr.
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + (x / 8 - F / 8)) by lia. apply ZS0. lia.
  - exists 4. destruct (s3m_gran F x 20 HF8 ltac:(lia)) as [D1 D2].
    rewrite D1, Z.add_assoc. split; [exact ZS4 | right; lia]. }
assert (HRAf : range_addressable (aview SEGS (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 32) 50).
{ apply (s3m_ra_transfer _ _ _ _ _ HFRA). intros x Hx. unfold shadow_of_addr.
  pose proof (s3m_rng F x 4 11 HF8 ltac:(lia)) as Hr.
  apply KEEP; [unfold SHADOW_OFF; lia | lia]. }
(* the registers at the call *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) RR2. prreg HS (3%bv : bv 5) RR3. prreg HS (4%bv : bv 5) RR4.
prreg HS (8%bv : bv 5) RR8. prreg HS (10%bv : bv 5) RR10. prreg HS (11%bv : bv 5) RR11. prreg HS (12%bv : bv 5) RR12.
prreg HS (18%bv : bv 5) RR18. prreg HS (20%bv : bv 5) RR20. prreg HS (21%bv : bv 5) RR21. prreg HS (22%bv : bv 5) RR22.
prreg HS (23%bv : bv 5) RR23. prreg HS (24%bv : bv 5) RR24. prreg HS (25%bv : bv 5) RR25. prreg HS (26%bv : bv 5) RR26.
prreg HS (27%bv : bv 5) RR27.
assert (Hsp' : spZ (ms_regs msC) = spZ regs - 128).
{ unfold spZ at 1. rewrite RR2, (EE 2%nat 2%bv eq_refl), Q2. unfold w64, CHECK_STEP_FRAME. apply unsigned_lit_small. lia. }
assert (Hs0' : s0Z (ms_regs msC) = spZ regs).
{ unfold s0Z. rewrite RR8, (EE 8%nat 8%bv eq_refl), Q8. unfold w64. apply unsigned_lit_small. lia. }
pmkst HS. rewrite pa_sigma_reac_ctrl_parse.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & FJ1 & _).
assert (Hlenb : length b = 8904%nat) by (rewrite Hlen; reflexivity).
assert (Hk' : 0 <= k <= 342) by (unfold CS_LAST in Hk; lia).
pose proof (Hsaved 0%nat ltac:(lia)) as SV0. pose proof (Hsaved 1%nat ltac:(lia)) as SV1.
change (Z.of_nat 0) with 0 in SV0. change (Z.of_nat 1) with 1 in SV1.
replace (spZ regs - 8 - 8 * 0) with (spZ regs - 8) in SV0 by lia.
replace (spZ regs - 8 - 8 * 1) with (spZ regs - 16) in SV1 by lia.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ =>
  eapply (PARSE TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly3 S3 W3 m d 0 r _ (F + 32) 50 (F + 128) (s3_fr b k) HJ) end.
  - eapply (arodata_ok_journalP SEGS _ _ pa_relro_img); [exact HJ | exact HROD].
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite RR3, (EE 3%nat 3%bv eq_refl), Q3. exact Hgp.
  - rewrite RR4, (EE 4%nat 4%bv eq_refl), Q4. exact Htp.
  - rewrite RR10, (EE 22%nat 22%bv eq_refl), R22. reflexivity.
  - rewrite RR11. reflexivity.
  - rewrite RR12, (EE 23%nat 23%bv eq_refl), R23. reflexivity.
  - lia.
  - rewrite Hsp', Hs0'. apply (achain_ly_top ly ly3 _ _ _ _ ETOP3).
    eapply (achain_push ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) (raZ regs) ch _ Hch).
    + lia.
    + intros a Ha. apply FJ1; lia.
    + rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem msC)) (spZ regs - 8)); [exact SV0|].
      intros k0 Hk0. apply KEEP; [lia | unfold SHADOW_OFF; lia].
    + rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) (ms_mem msC)) (spZ regs - 16)); [exact SV1|].
      intros k0 Hk0. apply KEEP; [lia | unfold SHADOW_OFF; lia].
    + exact Hra4.
    + lia.
    + exact Hsp8.
    + lia.
    + lia.
  - rewrite Hsp'. rewrite Zminus_mod, Hal16. reflexivity.
  - rewrite Hsp'. unfold TPARSE_STK, ESTACK. lia.
  - rewrite Hsp'. lia.
  - rewrite Hfrs3. cbn [app length]. rewrite Nat2Z.inj_succ. lia.
  - eapply (afobj_of_own SK SEGS B); [exact HJ | left; reflexivity | unfold CS_CID; lia | rewrite <- EF; lia
    | rewrite <- EF; change (fs_frame_bytes CS_CID) with 256; lia
    | replace (F + 32) with ((F / 8 + 4) * 8) by lia; apply Z_mod_mult | exact HRAf].
  - eapply (afobj_of_own SK SEGS B); [exact HJ | left; reflexivity | unfold CS_CID; lia | rewrite <- EF; lia
    | rewrite <- EF; change (fs_frame_bytes CS_CID) with 256; lia
    | replace (F + 128) with ((F / 8 + 16) * 8) by lia; apply Z_mod_mult | exact HRAo].
  - left. lia.
  - intros a Ha. right. right. right. exists CS_CID, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID) with 256. lia.
  - apply s3_fr_length; assumption.
  - intros i Hi. rewrite KEEP; [exact (HFB i Hi) | lia |].
    intros [Hc1 Hc2]. exact (s3m_sep F (F + 32 + Z.of_nat i) (F + 32 + Z.of_nat i - SHADOW_OFF - F / 8) HF8 HF4096 HFceil HFapp' ltac:(lia) ltac:(lia) ltac:(lia)). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfrs2 & Hab2 & _ & Ha0 & Ho & HK).
pose proof HJ2 as (_ & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & ELF2 & _).
assert (EF2 : frame_addr ly2 CS_CID fpos = F) by (rewrite EF; unfold frame_addr; rewrite ELF2, ELF3; reflexivity).
assert (EFL2 : flag_addr ly2 CS_CID fpos = flag_addr ly3 CS_CID fpos) by (unfold flag_addr; rewrite ELF2, ELF3; reflexivity).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite Hsp' in K1.
(* parse kept the own frame outside p, and the frame's shadow *)
assert (KF : forall a, F <= a < F + 256 -> ~ (F + 128 <= a < F + 128 + 36) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hno. rewrite (K4 CS_CID fpos a Hin3).
  - apply KEEP; [lia|]. intros [Hc1 Hc2].
    exact (s3m_sep F a (a - SHADOW_OFF - F / 8) HF8 HF4096 HFceil HFapp' ltac:(lia) Ha ltac:(lia)).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID) with 256. lia.
  - exact Hno. }
assert (KS : forall j, 4 <= j < 11 ->
  aview SEGS (w_H W2) mem2 (SHADOW_OFF + F / 8 + j) = aview SEGS (w_H W3) mem3 (SHADOW_OFF + F / 8 + j)).
{ intros j Hj. rewrite (K4 CS_CID fpos _ Hin3).
  - apply KEEP; [unfold SHADOW_OFF; lia | lia].
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID / 8) with 32. lia.
  - intros [Hc1 Hc2].
    exact (s3m_sep F (SHADOW_OFF + F / 8 + j) j HF8 HF4096 HFceil HFapp' ltac:(lia) ltac:(lia) eq_refl). }
assert (GS : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs msC) (Z_to_bv 5 r)) by exact HP2.
exists ly2, S2, regs2, mem2, md2.
split.
{ unfold cfg_at. rewrite R1. unfold A_check_step, AF_check_step, w64.
  replace (BASE + 0x9f0 + 0x40c) with (BASE + 3580) by lia. reflexivity. }
split.
{ unfold cs_frame. split; [exact HJ2|]. split; [rewrite Hab2; exact Hablk|].
  split.
  { rewrite EF2, EFL2. change (fs_frame_bytes CS_CID) with 256.
    rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) mem2) (F + 256 - 8)); [exact Hflagw|].
    intros k0 Hk0. apply KF; lia. }
  split.
  { intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W2) mem2)); [exact (Hsaved j Hj)|].
    intros k0 Hk0. rewrite K1 by (unfold TPARSE_STK, ESTACK; lia). apply KEEP; [lia | unfold SHADOW_OFF; lia]. }
  split; [transitivity (getr (ms_regs msC) (2%bv : bv 5)); [exact (GS 2 ltac:(unfold acallee_saved; lia)) | rewrite RR2, (EE 2%nat 2%bv eq_refl); exact Q2]|].
  split; [transitivity (getr (ms_regs msC) (3%bv : bv 5)); [exact (GS 3 ltac:(unfold acallee_saved; lia)) | rewrite RR3, (EE 3%nat 3%bv eq_refl); exact Q3]|].
  split; [transitivity (getr (ms_regs msC) (4%bv : bv 5)); [exact (GS 4 ltac:(unfold acallee_saved; lia)) | rewrite RR4, (EE 4%nat 4%bv eq_refl); exact Q4]|].
  split; [transitivity (getr (ms_regs msC) (8%bv : bv 5)); [exact (GS 8 ltac:(unfold acallee_saved; lia)) | rewrite RR8, (EE 8%nat 8%bv eq_refl); exact Q8]|].
  rewrite EF2.
  split; [transitivity (getr (ms_regs msC) (18%bv : bv 5)); [exact (GS 18 ltac:(unfold acallee_saved; lia)) | rewrite RR18, (EE 18%nat 18%bv eq_refl); exact Q18]|].
  split; [transitivity (getr (ms_regs msC) (25%bv : bv 5)); [exact (GS 25 ltac:(unfold acallee_saved; lia)) | rewrite RR25, (EE 25%nat 25%bv eq_refl); exact Q25]|].
  split; [transitivity (getr (ms_regs msC) (26%bv : bv 5)); [exact (GS 26 ltac:(unfold acallee_saved; lia)) | rewrite RR26, (EE 26%nat 26%bv eq_refl); exact Q26]|].
  transitivity (getr (ms_regs msC) (27%bv : bv 5)); [exact (GS 27 ltac:(unfold acallee_saved; lia)) | rewrite RR27, (EE 27%nat 27%bv eq_refl); exact Q27]. }
split.
{ rewrite Ha0. pose proof (s3_fr_parse b k Hlenb Hk') as SP. cbv zeta in SP. destruct SP as (SP0 & _). rewrite SP0. reflexivity. }
split; [transitivity (getr (ms_regs msC) (20%bv : bv 5)); [exact (GS 20 ltac:(unfold acallee_saved; lia)) | rewrite RR20, (EE 20%nat 20%bv eq_refl); exact R20]|].
split; [transitivity (getr (ms_regs msC) (21%bv : bv 5)); [exact (GS 21 ltac:(unfold acallee_saved; lia)) | rewrite RR21, (EE 21%nat 21%bv eq_refl); exact R21]|].
split; [transitivity (getr (ms_regs msC) (24%bv : bv 5)); [exact (GS 24 ltac:(unfold acallee_saved; lia)) | rewrite RR24, (EE 24%nat 24%bv eq_refl); exact R24]|].
rewrite EF2.
split; [transitivity (getr (ms_regs msC) (22%bv : bv 5)); [exact (GS 22 ltac:(unfold acallee_saved; lia)) | rewrite RR22, (EE 22%nat 22%bv eq_refl); exact R22]|].
split; [transitivity (getr (ms_regs msC) (23%bv : bv 5)); [exact (GS 23 ltac:(unfold acallee_saved; lia)) | rewrite RR23, (EE 23%nat 23%bv eq_refl); exact R23]|].
split; [intros i Hi; exact (Ho i Hi)|].
split; [intros i Hi; rewrite KF by lia; exact (HFB i Hi)|].
apply (s3m_ra_transfer _ _ _ _ _ HFRA). intros x Hx. unfold shadow_of_addr.
pose proof (s3m_rng F x 4 11 HF8 ltac:(lia)) as Hr.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + (x / 8 - F / 8)) by lia. apply KS. lia.
Qed.
End h.
End f.
End d.
Print Assumptions s3u_mid.
About s3u_mid.
