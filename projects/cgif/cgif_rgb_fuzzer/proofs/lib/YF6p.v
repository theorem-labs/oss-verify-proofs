(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF6m YF6b YF6q YF6o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition fvirt (R D : bvmap 5 word) : bvmap 5 word :=
(regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R 5 (getr D 5)) 6 (getr D 6)) 7 (getr D 7)) 12 (getr D 20)) 13 (getr D 19)) 14 (getr D 21)) 15 (getr D 22)) 16 (getr D 16)) 17 (getr D 17)) 28 (getr D 28)) 29 (getr D 29)) 30 (getr D 30)) 31 (getr D 31)).
Ltac fvirt_get := unfold fvirt; repeat first [ rewrite getr_same by (img_try (intros XX; discriminate XX)) | rewrite getr_other by (img_try (intros XX; discriminate XX)) ]; try img_refl.
Lemma fvirt_same : forall R D (r : bv 5), In r [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (fvirt R D) r = getr R r.
Proof. intros R D r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (fvirt_get)|]). destruct Hr. Qed.
Lemma fvirt_self : forall R D (r : bv 5), In r [5; 6; 7; 16; 17; 28; 29; 30; 31]%bv -> getr (fvirt R D) r = getr D r.
Proof. intros R D r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (fvirt_get)|]). destruct Hr. Qed.
Lemma fvirt_12 : forall R D, getr (fvirt R D) 12 = getr D 20. Proof. intros. fvirt_get. Qed.
Lemma fvirt_13 : forall R D, getr (fvirt R D) 13 = getr D 19. Proof. intros. fvirt_get. Qed.
Lemma fvirt_14 : forall R D, getr (fvirt R D) 14 = getr D 21. Proof. intros. fvirt_get. Qed.
Lemma fvirt_15 : forall R D, getr (fvirt R D) 15 = getr D 22. Proof. intros. fvirt_get. Qed.
Definition DCFACTS {imgk : img} (R D : bvmap 5 word) : Prop :=
getr D 1 = w64 (0x32434 + D_150) /\
getr D 2 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2208)) /\
getr D 3 = getr R 3 /\
getr D 4 = w64 TFX_TP /\
getr D 8 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2136)) /\
getr D 9 = getr R 10 /\
getr D 10 = w64 TFX_INST /\
getr D 11 = getr R 10 /\
getr D 12 = w64 0 /\
getr D 13 = w64 0 /\
getr D 14 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2136)) /\
getr D 15 = w64 1 /\
getr D 18 = w64 TFX_INST /\
getr D 23 = getr R 23 /\
getr D 24 = getr R 24 /\
getr D 25 = getr R 25 /\
getr D 26 = getr R 26 /\
getr D 27 = getr R 27.
Lemma REGSD_of {imgk : img} : forall (R D : bvmap 5 word) (extra : list word), DCFACTS R D -> regs_ok (Ereg (fvirt R D) extra) REGS_DC D.
Proof.
intros R D extra (F1 & F2 & F3 & F4 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F18 & F23 & F24 & F25 & F26 & F27).
img_apply regs_ok_by_cases. intros r Hr. unfold all_regs in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
lazymatch goal with |- getr D ?r = sv_denot _ (sr_get ?sr ?r) => let e := img_ev (sr_get sr r) in img_change (sr_get sr r) with e end.
- img_refl.
- rewrite F1. img_refl.
- rewrite F2. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 2 2%bv eq_refl), (fvirt_same R D 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- rewrite F3. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 3 3%bv eq_refl), (fvirt_same R D 3%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F4. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 5 5%bv eq_refl), (fvirt_self R D 5%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 6 6%bv eq_refl), (fvirt_self R D 6%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 7 7%bv eq_refl), (fvirt_self R D 7%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F8. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 2 2%bv eq_refl), (fvirt_same R D 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- rewrite F9. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 10 10%bv eq_refl), (fvirt_same R D 10%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F10. img_refl.
- rewrite F11. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 10 10%bv eq_refl), (fvirt_same R D 10%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F12. img_refl.
- rewrite F13. img_refl.
- rewrite F14. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 2 2%bv eq_refl), (fvirt_same R D 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- rewrite F15. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 16 16%bv eq_refl), (fvirt_self R D 16%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 17 17%bv eq_refl), (fvirt_self R D 17%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F18. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 13 13%bv eq_refl), (fvirt_13 R D), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 12 12%bv eq_refl), (fvirt_12 R D), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 14 14%bv eq_refl), (fvirt_14 R D), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 15 15%bv eq_refl), (fvirt_15 R D), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F23. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 23 23%bv eq_refl), (fvirt_same R D 23%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F24. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 24 24%bv eq_refl), (fvirt_same R D 24%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F25. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 25 25%bv eq_refl), (fvirt_same R D 25%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F26. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 26 26%bv eq_refl), (fvirt_same R D 26%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F27. cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 27 27%bv eq_refl), (fvirt_same R D 27%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 28 28%bv eq_refl), (fvirt_self R D 28%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 29 29%bv eq_refl), (fvirt_self R D 29%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 30 30%bv eq_refl), (fvirt_self R D 30%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (fvirt R D) extra 31 31%bv eq_refl), (fvirt_self R D 31%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
Qed.
Definition CFRAMES {imgk : img} : list (Z * sv) :=
[(-2208, SLit 1); (-2200, SLit (0x53640 + D_2c4)); (-2192, SOff 10 0); (-2184, SOff 11 0); (-2176, SOff 2 0); (-2168, SLit (0x32340 + D_150)); (-2152, SLit (0x536b0 + D_2c4)); (-2136, SOff 2 (-2120)); (-64, SOff 22 0); (-56, SOff 21 0); (-48, SOff 20 0); (-40, SOff 19 0); (-32, SOff 18 0); (-24, SOff 9 0); (-16, SOff 8 0); (-8, SOff 1 0)].
Definition CFRAMES_ok {imgk : img} (R : bvmap 5 word) (len : Z) (H : word -> bool) (m : word -> option byte) : Prop :=
val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + (-2128)) 8 len /\
Forall (fun p : Z * sv => val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg R []) (snd p)))) CFRAMES.
Lemma STKD_of {imgk : img} : forall (R D : bvmap 5 word) (len : Z) (H : word -> bool) (m : word -> option byte),
CFRAMES_ok R len H m -> 0 <= len < 2 ^ 64 ->
TFX_IMG_END + ASTACK <= bv_unsigned (getr R 2) -> (forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> apresent H m a) ->
forall extra : list word, nth 4 extra (w64 0) = w64 len ->
Forall (region_ok tfxsegs (Ereg (fvirt R D) extra) (mrestrict H m)) [R_OBJ; R_SCR; R_TOP].
Proof.
intros R D len H m (HL & HF) Hlr Hsp HPR extra Hlen.
assert (GF : forall p, In p CFRAMES -> val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg R []) (snd p)))) by (img_try (img_apply Forall_forall; img_exact HF)). clear HF.
assert (B2 : base_val (Ereg (fvirt R D) extra) (Some 2%nat) = bv_unsigned (getr R 2)).
{ cbn [base_val]. rewrite (ew_Ereg_nat (fvirt R D) extra 2 2%bv eq_refl), (fvirt_same R D 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. }
pose proof (bv_unsigned_in_range 64 (getr R 2)) as U2. img_change (bv_modulus 64) with (2 ^ 64) in U2.
assert (WR : forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> writable_at tfxsegs (mrestrict H m) a).
{ intros a Ha. img_exact (YE0v.apresent_writable H m a (HPR a Ha)). }
assert (CK : forall off e, In (off, e) CFRAMES -> sv_denot (Ereg (fvirt R D) extra) e = sv_denot (Ereg R []) e ->
YQ0b.chunk_ok tfxsegs (Ereg (fvirt R D) extra) (mrestrict H m) (bv_unsigned (getr R 2)) (YQ0b.mkChunk off (CVal 8 e))).
{ intros off e Hin He. eapply (chunk_ok_val tfxsegs _ _ _ off 8 e (bv_unsigned (sv_denot (Ereg R []) e))); [img_try (rewrite Z_to_bv_bv_unsigned; img_exact He)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) e)) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (img_exact (GF (off, e) Hin)) ]. }
assert (AT : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> In r [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
ew (Ereg (fvirt R D) extra) k = ew (Ereg R []) k).
{ intros k r Hk Hr. rewrite (ew_Ereg_nat (fvirt R D) extra k r Hk), (ew_Ereg_nat R [] k r Hk). img_exact (fvirt_same R D r Hr). }
img_apply Forall_cons.
{ unfold R_OBJ, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [img_try (img_apply (CK (-2208) (SLit 1)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2200) (SLit (0x53640 + D_2c4))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2192) (SOff 10 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 10%nat 10%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2184) (SOff 11 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 11%nat 11%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2176) (SOff 2 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 2%nat 2%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2168) (SLit (0x32340 + D_150))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2152) (SLit (0x536b0 + D_2c4))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2136) (SOff 2 (-2120))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 2%nat 2%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs _ _ _ (-2128) 8 (SOff 36%nat 0) len); [img_try (cbn [sv_denot]; img_change (ew (Ereg (fvirt R D) extra) 36) with (nth 4 extra (w64 0)); rewrite Hlen; unfold w64; rewrite unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)
| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia) | img_try (cbn; img_lia) | img_try (img_exact HL) ]. }
img_apply Forall_cons.
{ unfold R_SCR, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold TFX_IMG_END, ASTACK in *; img_lia) | img_try (img_apply Forall_nil)]. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold R_TOP, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold TFX_IMG_END, ASTACK in *; img_lia)|].
img_apply Forall_cons; [img_try (img_apply (CK (-64) (SOff 22 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 22%nat 22%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-56) (SOff 21 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 21%nat 21%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-48) (SOff 20 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 20%nat 20%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-40) (SOff 19 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 19%nat 19%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-32) (SOff 18 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 18%nat 18%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-24) (SOff 9 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 9%nat 9%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-16) (SOff 8 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 8%nat 8%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-8) (SOff 1 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 1%nat 1%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_nil.
Qed.
Lemma CFRAMES_of_MID {imgk : img} : forall (R U : bvmap 5 word) (len : Z) (H : word -> bool) (regs' : bvmap 5 word) (m m' : word -> option byte),
MIDST_top (virt R U) len H regs' m ->
(forall a, bv_unsigned (getr R 2) - 2208 <= a < bv_unsigned (getr R 2) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
CFRAMES_ok R len H m'.
Proof.
intros R U len H regs' m m' (_ & HL & _ & HF) HM.
rewrite (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))) in HL, HF.
assert (GF : forall p, In p MIDFRAMES -> val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg (virt R U) []) (snd p)))) by (img_try (img_apply Forall_forall; img_exact HF)). clear HF.
assert (TR : forall off v, -2208 <= off -> off + 8 <= 0 -> val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + off) 8 v -> val_mem tfxsegs (mrestrict H m') (bv_unsigned (getr R 2) + off) 8 v).
{ intros off v Ho1 Ho2 V. eapply val_mem_frame; [|img_try (img_exact V)]. intros k Hk. img_apply HM. img_lia. }
assert (AT : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> In r [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv -> ew (Ereg (virt R U) []) k = ew (Ereg R []) k).
{ intros k r Hk Hr. rewrite (ew_Ereg_nat (virt R U) [] k r Hk), (ew_Ereg_nat R [] k r Hk). img_apply virt_same. cbn [In] in Hr |- *. tauto. }
assert (A10 : ew (Ereg (virt R U) []) 11 = ew (Ereg R []) 10) by (img_try (rewrite (ew_Ereg_nat (virt R U) [] 11 11%bv eq_refl), (ew_Ereg_nat R [] 10 10%bv eq_refl); img_apply virt_11)).
assert (A11 : ew (Ereg (virt R U) []) 10 = ew (Ereg R []) 11) by (img_try (rewrite (ew_Ereg_nat (virt R U) [] 10 10%bv eq_refl), (ew_Ereg_nat R [] 11 11%bv eq_refl); img_apply virt_10)).
split; [img_try (img_apply (TR (-2128) len ltac:(img_lia) ltac:(img_lia)); img_exact HL)|].
unfold CFRAMES.
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SLit 1)) with (sv_denot (Ereg (virt R U) []) (SLit 1)) by (img_refl);
img_apply (TR (-2208) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2208), SLit 1) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SLit (0x53640 + D_2c4))) with (sv_denot (Ereg (virt R U) []) (SLit (0x53640 + D_2c4))) by (img_refl);
img_apply (TR (-2200) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2200), SLit (0x53640 + D_2c4)) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 10 0)) with (sv_denot (Ereg (virt R U) []) (SOff 11 0)) by (cbn [sv_denot]; rewrite A10; img_refl);
img_apply (TR (-2192) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2192), SOff 11 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 11 0)) with (sv_denot (Ereg (virt R U) []) (SOff 10 0)) by (cbn [sv_denot]; rewrite A11; img_refl);
img_apply (TR (-2184) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2184), SOff 10 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 2 0)) with (sv_denot (Ereg (virt R U) []) (SOff 2 0)) by (cbn [sv_denot]; rewrite (AT 2%nat 2%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-2176) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2176), SOff 2 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SLit (0x32340 + D_150))) with (sv_denot (Ereg (virt R U) []) (SLit (0x32340 + D_150))) by (img_refl);
img_apply (TR (-2168) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2168), SLit (0x32340 + D_150)) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SLit (0x536b0 + D_2c4))) with (sv_denot (Ereg (virt R U) []) (SLit (0x536b0 + D_2c4))) by (img_refl);
img_apply (TR (-2152) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2152), SLit (0x536b0 + D_2c4)) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 2 (-2120))) with (sv_denot (Ereg (virt R U) []) (SOff 2 (-2120))) by (cbn [sv_denot]; rewrite (AT 2%nat 2%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-2136) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-2136), SOff 2 (-2120)) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 22 0)) with (sv_denot (Ereg (virt R U) []) (SOff 22 0)) by (cbn [sv_denot]; rewrite (AT 22%nat 22%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-64) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-64), SOff 22 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 21 0)) with (sv_denot (Ereg (virt R U) []) (SOff 21 0)) by (cbn [sv_denot]; rewrite (AT 21%nat 21%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-56) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-56), SOff 21 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 20 0)) with (sv_denot (Ereg (virt R U) []) (SOff 20 0)) by (cbn [sv_denot]; rewrite (AT 20%nat 20%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-48) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-48), SOff 20 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 19 0)) with (sv_denot (Ereg (virt R U) []) (SOff 19 0)) by (cbn [sv_denot]; rewrite (AT 19%nat 19%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-40) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-40), SOff 19 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 18 0)) with (sv_denot (Ereg (virt R U) []) (SOff 18 0)) by (cbn [sv_denot]; rewrite (AT 18%nat 18%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-32) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-32), SOff 18 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 9 0)) with (sv_denot (Ereg (virt R U) []) (SOff 9 0)) by (cbn [sv_denot]; rewrite (AT 9%nat 9%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-24) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-24), SOff 9 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 8 0)) with (sv_denot (Ereg (virt R U) []) (SOff 8 0)) by (cbn [sv_denot]; rewrite (AT 8%nat 8%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-16) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-16), SOff 8 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_cons; [img_try (cbn [fst snd]; replace (sv_denot (Ereg R []) (SOff 1 0)) with (sv_denot (Ereg (virt R U) []) (SOff 1 0)) by (cbn [sv_denot]; rewrite (AT 1%nat 1%bv eq_refl ltac:(cbn [In]; tauto)); img_refl);
img_apply (TR (-8) _ ltac:(img_lia) ltac:(img_lia)); img_exact (GF ((-8), SOff 1 0) ltac:(unfold MIDFRAMES; cbn [In]; repeat first [left; img_refl | right])))|].
img_apply Forall_nil.
Qed.
