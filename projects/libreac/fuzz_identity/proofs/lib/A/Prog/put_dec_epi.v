(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:136-141;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC93.v:83-84. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC45 YC4b YC81.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition pe_frame_region : YP09.region :=
YP09.mkRegion (Some 24%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition pe_shadow_region : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition pe_stack_region : YP09.region :=
YP09.mkRegion (Some 8%nat) (-128) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0))].
Definition pe_flag_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition pe_sr : list sv := sr_set sr_atoms (18%bv : bv 5) (SOff 24 0).
Definition pe_ss : sstate :=
mkSS (AF_put_dec + 532) pe_sr [pe_frame_region; pe_shadow_region; pe_stack_region] None (mkFacts [] [] []).
Definition pe_extra (FL : Z) (regs0 : bvmap 5 word) : list word :=
[Z_to_bv 64 FL; getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20;
 getr regs0 21; getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26].
Ltac pe_norm_ss HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Lemma pe_kept : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Section e.
Variable B : asyms.
Lemma pe_awr_frame : forall STK sp0 FP bl0 blc ly own pos a,
(frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 \/
 SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
awr_byte STK sp0 FP bl0 blc ly ((0, pos) :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. exact Ha.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
Lemma pd_epi : forall (F FL sp0e pos : Z)
W (regs regs0 : bvmap 5 word) memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k,
getr regs 2 = Z_to_bv 64 (sp0e - 128) -> getr regs 8 = Z_to_bv 64 sp0e ->
getr regs 9 = Z_to_bv 64 (sp0e - 128) ->
getr regs 18 = Z_to_bv 64 F -> getr regs 24 = Z_to_bv 64 F ->
getr regs 23 = Z_to_bv 64 SHADOW_OFF -> getr regs 25 = Z_to_bv 64 (SHADOW_OFF + F / 8) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> getr regs 27 = getr regs0 27 ->
getr regs0 2 = Z_to_bv 64 sp0e -> YK0s.ret_ok (getr regs0 1) ->
sp0 - STK <= sp0e - 128 -> sp0e <= sp0 ->
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc k ->
F = frame_addr lyc 0 pos -> FL = flag_addr lyc 0 pos ->
rdword (aview SEGS (w_H W) memc) (F + 56) = Some FL ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 120) 8 (bv_unsigned (getr regs0 1)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 112) 8 (bv_unsigned (getr regs0 8)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 104) 8 (bv_unsigned (getr regs0 9)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 96) 8 (bv_unsigned (getr regs0 18)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 88) 8 (bv_unsigned (getr regs0 19)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 80) 8 (bv_unsigned (getr regs0 20)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 72) 8 (bv_unsigned (getr regs0 21)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 64) 8 (bv_unsigned (getr regs0 22)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 56) 8 (bv_unsigned (getr regs0 23)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 48) 8 (bv_unsigned (getr regs0 24)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 40) 8 (bv_unsigned (getr regs0 25)) ->
val_mem SEGS (mrestrict (w_H W) memc) (sp0e - 128 + 32) 8 (bv_unsigned (getr regs0 26)) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 532))) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc (stack_free_state 0 pos Sc) W mem' md' k /\
aregs_preserved regs0 regs' /\
(0, pos) :: frames (stack_free_state 0 pos Sc) = frames Sc /\
ablocks B lyc (stack_free_state 0 pos Sc) = ablocks B lyc Sc /\
st_nev (stack_free_state 0 pos Sc) = st_nev Sc /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0e - 128 <= a < sp0e) -> ~ (F <= a < F + 64) ->
~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) -> a <> FL ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
intros F FL sp0e pos W regs regs0 memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k
G2 G8 G9 G18 G24 G23 G25 G3 G4 G27 Gsp0 Hra Hstklo Hstkhi HJ EF EFL Hflag
V1 V8 V9 V18 V19 V20 V21 V22 V23 V24 V25 V26.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & HST & _).
pose proof HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 0 pos HAR Hin) as (HFal & _ & HFpres & HFSpres).
destruct (FFL lyc Sc W memc mdc 0 pos HAR Hin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp, HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres.
rewrite <- EF in HF4096, HFceil, HFapp, HFal, HFpres, HFSpres.
rewrite <- EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HD8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
assert (HM8 : 0 <= F mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HSPlo : alloc_ceiling + 128 <= sp0e) by lia.
assert (HSPhi : sp0e <= 2 ^ 47) by lia.
assert (HSH1 : SHADOW_OFF + 512 <= SHADOW_OFF + F / 8) by (unfold SHADOW_OFF; lia).
assert (HSH2 : SHADOW_OFF + F / 8 + 8 <= 17594333495296) by (unfold SHADOW_OFF; lia).
assert (HSHF : SHADOW_OFF + F / 8 + 8 <= F \/ F + 64 <= SHADOW_OFF + F / 8)
by (unfold SHADOW_OFF; destruct HFapp as (_ & [Hq | (Hq & _)]); [right | left]; lia).
assert (HFLnf : ~ (F <= FL < F + 64)) by (intros Hr; exact (proj2 (HFpres FL Hr) HFLown)).
assert (HFLsh2 : ~ (SHADOW_OFF + F / 8 <= FL < SHADOW_OFF + F / 8 + 8))
by (unfold SHADOW_OFF in *; intros Hq; destruct HFLapp as (_ & [Hr | (Hr & _)]); lia).
remember (Eimg (Ereg regs (pe_extra FL regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (pe_extra FL regs0) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44.
cbn [Nat.add nth pe_extra] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44.
clear EX.
assert (HAE : env_agree 32 (Ereg regs (pe_extra FL regs0)) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8v : ew E 8 = Z_to_bv 64 sp0e) by (rewrite (EE 8%nat (8%bv : bv 5) eq_refl); exact G8).
assert (E24v : ew E 24 = Z_to_bv 64 F) by (rewrite (EE 24%nat (24%bv : bv 5) eq_refl); exact G24).
assert (E25v : ew E 25 = Z_to_bv 64 (SHADOW_OFF + F / 8))
by (rewrite (EE 25%nat (25%bv : bv 5) eq_refl); exact G25).
assert (U8 : bv_unsigned (ew E 8) = sp0e) by (rewrite E8v; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = F) by (rewrite E24v; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
by (rewrite E25v; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pe_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 532))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full E (AF_put_dec + 532) pe_sr regs
[pe_frame_region; pe_shadow_region; pe_stack_region] (mkFacts [] [] []) (mrestrict (w_H W) memc)).
- unfold pe_sr. apply regs_ok_pin; [| intros Hq; discriminate Hq |].
  + rewrite HE. apply regs_ok_Eimg_Ereg.
  + cbn [sv_denot]. rewrite E24v, Z.add_0_r, Z_to_bv_bv_unsigned. exact G18.
- vm_compute; reflexivity.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
  + unfold pe_frame_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))). }
    apply Forall_cons; [| apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) F 56 8%N (SOff 32 0) FL);
    [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
    | exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ].
  + unfold pe_shadow_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
    split; [| apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). unfold shadow_addr in HFSpres.
    exact (proj1 (HFSpres o ltac:(lia))).
  + unfold pe_stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat (apply Forall_cons; [solve
      [ apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-8) 8%N (SOff 33 0) (bv_unsigned (getr regs0 1)));
        [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -8) with (sp0e - 128 + 120) by lia; exact V1 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-16) 8%N (SOff 34 0) (bv_unsigned (getr regs0 8)));
        [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -16) with (sp0e - 128 + 112) by lia; exact V8 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-24) 8%N (SOff 35 0) (bv_unsigned (getr regs0 9)));
        [ cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -24) with (sp0e - 128 + 104) by lia; exact V9 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-32) 8%N (SOff 36 0) (bv_unsigned (getr regs0 18)));
        [ cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -32) with (sp0e - 128 + 96) by lia; exact V18 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-40) 8%N (SOff 37 0) (bv_unsigned (getr regs0 19)));
        [ cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -40) with (sp0e - 128 + 88) by lia; exact V19 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-48) 8%N (SOff 38 0) (bv_unsigned (getr regs0 20)));
        [ cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -48) with (sp0e - 128 + 80) by lia; exact V20 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-56) 8%N (SOff 39 0) (bv_unsigned (getr regs0 21)));
        [ cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -56) with (sp0e - 128 + 72) by lia; exact V21 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-64) 8%N (SOff 40 0) (bv_unsigned (getr regs0 22)));
        [ cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -64) with (sp0e - 128 + 64) by lia; exact V22 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-72) 8%N (SOff 41 0) (bv_unsigned (getr regs0 23)));
        [ cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -72) with (sp0e - 128 + 56) by lia; exact V23 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-80) 8%N (SOff 42 0) (bv_unsigned (getr regs0 24)));
        [ cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -80) with (sp0e - 128 + 48) by lia; exact V24 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-88) 8%N (SOff 43 0) (bv_unsigned (getr regs0 25)));
        [ cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -88) with (sp0e - 128 + 40) by lia; exact V25 ]
      | apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) sp0e (-96) 8%N (SOff 44 0) (bv_unsigned (getr regs0 26)));
        [ cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
        | cbn; lia | replace (sp0e + -96) with (sp0e - 128 + 32) by lia; exact V26 ] ] |]).
    apply Forall_nil.
- unfold pe_frame_region, pe_shadow_region, pe_stack_region.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U24, U25.
  repeat split; unfold SHADOW_OFF in *; lia.
- split; [exact I|]. split; exact I. }
unfold pe_ss in HS.
paj_run_sh RUNP HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U24 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply pe_awr_frame. left. rewrite <- EF. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | ].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply pe_awr_frame. right. rewrite <- EF. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  rewrite (U_atom E 24 F E24v ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc. lia. }
pe_norm_ss HS.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) ->
~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha H1 H2.
  apply (pe_kept E (ss_mem pe_ss) (w_H W) memc (ms_mem ms)
    (fun x => (F <= x < F + 64) \/ (SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 8)) HFr);
  [| exact Ha | tauto].
  intros x (r & Hr & Hw). unfold pe_ss, pe_frame_region, pe_shadow_region, pe_stack_region in Hr.
  cbn [ss_mem In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U8, ?U24, ?U25 in Hw; lia. }
clear HF HFr.
destruct (FFL lyc Sc W (ms_mem ms) _ 0 pos (proj1 HJ) Hin) as (HFLpres2 & _).
rewrite <- EFL in HFLpres2.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ex ssx msx pe_flag_region HS eq_refl) as HSF end.
specialize (HSF ltac:(unfold pe_flag_region, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rewrite U32; split; [lia|]; split; [lia|]; split; [| apply Forall_nil];
  intros o Ho; replace (FL + o) with FL by lia; apply (apresent_writable SEGS); exact HFLpres2)).
specialize (HSF ltac:(unfold pe_flag_region; cbn [ss_mem all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U32, U8, U24, U25;
  repeat split; unfold SHADOW_OFF in *; lia)).
clear HS. rename HSF into HS. pe_norm_ss HS.
paj_run_flag_sh RUNF HS HJ.
- lia.
- intros a (r & Hr & Hw). cbn [ss_mem In] in Hr.
  repeat destruct Hr as [<- | Hr]; try destruct Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U32, ?U8, ?U24, ?U25 in Hw.
  + right. rewrite <- EFL. lia.
  + left. apply pe_awr_frame. left. rewrite <- EF. lia.
  + left. apply pe_awr_frame. right. rewrite <- EF. lia.
  + lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 0%nat _ HSr eq_refl) as HR0.
  pose proof (field_of_region E (ms_mem msr) 32%nat FL _ _ _ _ _ 0 1%N (SLit 0) 0 HR0 U32
    ltac:(cbn; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite <- EFL. specialize (V 0%nat ltac:(cbn; lia)). change (Z.of_nat 0) with 0 in V.
  rewrite !Z.add_0_r in V. exact V.
- assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) ->
  ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) -> a <> FL ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha H1 H2 H3.
    lazymatch type of HFr with frame_of _ ?rsx _ _ =>
    apply (pe_kept E rsx (w_H W) (ms_mem ms) (ms_mem ms0)
      (fun x => (F <= x < F + 64) \/ (SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 8) \/ x = FL) HFr) end;
    [| exact Ha | tauto].
    intros x (r & Hr & Hw). cbn [ss_mem In] in Hr. repeat destruct Hr as [<- | Hr]; try destruct Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?U32, ?U8, ?U24, ?U25 in Hw;
    [right; right; lia | left; lia | right; left; lia | lia]. }
  eapply (RET W E _ ms0 _ _ HS); [vm_compute; reflexivity | vm_compute; reflexivity |].
  intros mat3.
  prreg HS (1%bv : bv 5) Q1.
  assert (EPC : v_jalr (getr (ms_regs ms0) 1) 0 = getr regs0 1)
  by (rewrite Q1, E33; exact Hra).
  rewrite EPC.
  split; [reflexivity|].
  exists (ms_regs ms0), (ms_mem ms0). eexists.
  split; [reflexivity|].
  split; [exact (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat3 HJ)|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia. clear Hr.
    destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
    - prreg HS (Z_to_bv 5 2) Q. rewrite Q, E8v.
      change (Z_to_bv 5 2) with (Z_to_bv 5 (bv_unsigned (2%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      rewrite Gsp0. reflexivity.
    - prreg HS (Z_to_bv 5 3) Q. rewrite Q, (EE 3%nat (3%bv : bv 5) eq_refl), G3.
      change (Z_to_bv 5 3) with (Z_to_bv 5 (bv_unsigned (3%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 4) Q. rewrite Q, (EE 4%nat (4%bv : bv 5) eq_refl), G4.
      change (Z_to_bv 5 4) with (Z_to_bv 5 (bv_unsigned (4%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 8) Q. rewrite Q, E34.
      change (Z_to_bv 5 8) with (Z_to_bv 5 (bv_unsigned (8%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 9) Q. rewrite Q, E35.
      change (Z_to_bv 5 9) with (Z_to_bv 5 (bv_unsigned (9%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 18) Q. rewrite Q, E36.
      change (Z_to_bv 5 18) with (Z_to_bv 5 (bv_unsigned (18%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 19) Q. rewrite Q, E37.
      change (Z_to_bv 5 19) with (Z_to_bv 5 (bv_unsigned (19%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 20) Q. rewrite Q, E38.
      change (Z_to_bv 5 20) with (Z_to_bv 5 (bv_unsigned (20%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 21) Q. rewrite Q, E39.
      change (Z_to_bv 5 21) with (Z_to_bv 5 (bv_unsigned (21%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 22) Q. rewrite Q, E40.
      change (Z_to_bv 5 22) with (Z_to_bv 5 (bv_unsigned (22%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 23) Q. rewrite Q, E41.
      change (Z_to_bv 5 23) with (Z_to_bv 5 (bv_unsigned (23%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 24) Q. rewrite Q, E42.
      change (Z_to_bv 5 24) with (Z_to_bv 5 (bv_unsigned (24%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 25) Q. rewrite Q, E43.
      change (Z_to_bv 5 25) with (Z_to_bv 5 (bv_unsigned (25%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 26) Q. rewrite Q, E44.
      change (Z_to_bv 5 26) with (Z_to_bv 5 (bv_unsigned (26%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity.
    - prreg HS (Z_to_bv 5 27) Q. rewrite Q, (EE 27%nat (27%bv : bv 5) eq_refl), G27.
      change (Z_to_bv 5 27) with (Z_to_bv 5 (bv_unsigned (27%bv : bv 5))). rewrite Z_to_bv_bv_unsigned.
      reflexivity. }
  split.
  { replace (frames (stack_free_state 0 pos Sc)) with (del_pos (frames Sc) 0 pos) by reflexivity.
    rewrite Hfrs. cbn [app del_pos]. rewrite !Z.eqb_refl. cbn [andb]. reflexivity. }
  split; [unfold ablocks; rewrite blocks_stack_free_state; reflexivity|].
  split; [reflexivity|].
  split.
  { intros a Ha Hstk Hfr Hsh Hfl. rewrite (K2 a Ha Hfr Hsh Hfl). exact (K1 a Ha Hfr Hsh). }
  intros a Hp. eapply apresent_grows; [exact HG0 | eapply apresent_grows; [exact HG | exact Hp]].
Qed.
End e.
End d.
End b.
