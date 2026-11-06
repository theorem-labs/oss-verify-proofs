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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF6q YF6v YF6z YF7a YF79 YF6s.
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
Definition virt (R U : bvmap 5 word) : bvmap 5 word :=
regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
10 (getr R 11)) 11 (getr R 10)) 5 (getr U 5)) 6 (getr U 6)) 7 (getr U 7)) 17 (getr U 17)) 28 (getr U 28)) 29 (getr U 29)) 30 (getr U 30)) 31 (getr U 31).
Ltac virt_get := unfold virt; repeat first [ rewrite getr_same by (img_try (intros XX; discriminate XX)) | rewrite getr_other by (img_try (intros XX; discriminate XX)) ]; try img_refl.
Lemma virt_same : forall R U (r : bv 5), In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (virt R U) r = getr R r.
Proof. intros R U r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (virt_get)|]). destruct Hr. Qed.
Lemma virt_10 : forall R U, getr (virt R U) 10 = getr R 11. Proof. intros. virt_get. Qed.
Lemma virt_11 : forall R U, getr (virt R U) 11 = getr R 10. Proof. intros. virt_get. Qed.
Lemma virt_dead : forall R U (r : bv 5), In r [5; 6; 7; 17; 28; 29; 30; 31]%bv -> getr (virt R U) r = getr U r.
Proof. intros R U r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (virt_get)|]). destruct Hr. Qed.
Lemma REGSU_of {imgk : img} : forall (R U : bvmap 5 word) (len : Z) (H : word -> bool) (m : word -> option byte),
PAST_top R len H U m -> forall extra : list word, regs_ok (Ereg (virt R U) extra) REGS_A U.
Proof.
intros R U len H m (_ & HR & _) extra.
assert (G : forall p, In p PAREGS -> getr U (fst p) = sv_denot (Ereg R []) (snd p)) by (img_try (img_apply Forall_forall; img_exact HR)). clear HR.
img_apply regs_ok_by_cases. intros r Hr. unfold all_regs in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
lazymatch goal with |- getr U ?r = sv_denot _ (sr_get ?sr ?r) => let e := img_ev (sr_get sr r) in img_change (sr_get sr r) with e end.
- img_refl.
- pose proof (G (1%bv, SLit (0x32388 + D_150)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (2%bv, SOff 2 (-2208)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (3%bv, SOff 3 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 3 3%bv eq_refl), (ew_Ereg_nat (virt R U) extra 3 3%bv eq_refl), (virt_same R U 3%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (4%bv, SLit TFX_TP) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 5 5%bv eq_refl), (virt_dead R U 5%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 6 6%bv eq_refl), (virt_dead R U 6%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 7 7%bv eq_refl), (virt_dead R U 7%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (G (8%bv, SOff 2 (-2136)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (9%bv, SOff 10 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 10 10%bv eq_refl), (ew_Ereg_nat (virt R U) extra 11 11%bv eq_refl), (virt_11 R U). img_refl.
- pose proof (G (10%bv, SLit TFX_INST) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (11%bv, SOff 11 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 11 11%bv eq_refl), (ew_Ereg_nat (virt R U) extra 10 10%bv eq_refl), (virt_10 R U). img_refl.
- pose proof (G (12%bv, SLit 8) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (13%bv, SOff 2 (-2136)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (14%bv, SLit 1) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (15%bv, SLit 1) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (16%bv, SOff 2 (-2136)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 17 17%bv eq_refl), (virt_dead R U 17%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (G (18%bv, SLit TFX_INST) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (19%bv, SOff 11 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 11 11%bv eq_refl), (ew_Ereg_nat (virt R U) extra 10 10%bv eq_refl), (virt_10 R U). img_refl.
- pose proof (G (20%bv, SLit 1) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. img_refl.
- pose proof (G (21%bv, SOff 2 (-2136)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (22%bv, SOff 2 (-89)) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (23%bv, SOff 23 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 23 23%bv eq_refl), (ew_Ereg_nat (virt R U) extra 23 23%bv eq_refl), (virt_same R U 23%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (24%bv, SOff 24 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 24 24%bv eq_refl), (ew_Ereg_nat (virt R U) extra 24 24%bv eq_refl), (virt_same R U 24%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (25%bv, SOff 25 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 25 25%bv eq_refl), (ew_Ereg_nat (virt R U) extra 25 25%bv eq_refl), (virt_same R U 25%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (26%bv, SOff 26 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 26 26%bv eq_refl), (ew_Ereg_nat (virt R U) extra 26 26%bv eq_refl), (virt_same R U 26%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- pose proof (G (27%bv, SOff 27 0) ltac:(img_try (unfold PAREGS; cbn [In]; repeat first [left; img_refl | right]))) as X. cbn [fst snd] in X. rewrite X. cbn [sv_denot]. rewrite (ew_Ereg_nat R [] 27 27%bv eq_refl), (ew_Ereg_nat (virt R U) extra 27 27%bv eq_refl), (virt_same R U 27%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 28 28%bv eq_refl), (virt_dead R U 28%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 29 29%bv eq_refl), (virt_dead R U 29%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 30 30%bv eq_refl), (virt_dead R U 30%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (virt R U) extra 31 31%bv eq_refl), (virt_dead R U 31%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
Qed.
Lemma STKU_of {imgk : img} : forall (R U : bvmap 5 word) (len : Z) (H : word -> bool) (m : word -> option byte),
PAST_top R len H U m -> 0 <= len < 2 ^ 64 ->
TFX_IMG_END + ASTACK <= bv_unsigned (getr R 2) -> (forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> apresent H m a) ->
forall extra : list word, nth 4 extra (w64 0) = w64 len ->
Forall (region_ok tfxsegs (Ereg (virt R U) extra) (mrestrict H m)) [R_bstA; R_scrA; R_topA].
Proof.
intros R U len H m (HL & _ & HF) Hlr Hsp HPR extra Hlen. unfold MIDLEN in HL. cbn [fst snd] in HL.
assert (GF : forall p, In p PAFRAMES -> val_mem tfxsegs (mrestrict H m) (bv_unsigned (getr R 2) + fst p) 8 (bv_unsigned (sv_denot (Ereg R []) (snd p)))) by (img_try (img_apply Forall_forall; img_exact HF)). clear HF.
assert (B2 : base_val (Ereg (virt R U) extra) (Some 2%nat) = bv_unsigned (getr R 2)).
{ cbn [base_val]. rewrite (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. }
pose proof (bv_unsigned_in_range 64 (getr R 2)) as U2. img_change (bv_modulus 64) with (2 ^ 64) in U2.
assert (WR : forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> writable_at tfxsegs (mrestrict H m) a).
{ intros a Ha. img_apply apresent_writable; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia) | img_try (img_exact (HPR a Ha))]. }
img_apply Forall_cons.
{ unfold R_bstA, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2136) 8 (SOff 2 (-2120)) (bv_unsigned (sv_denot (Ereg R []) (SOff 2 (-2120))))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 2 (-2120)))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2136), SOff 2 (-2120)) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2128) 8 (SOff aLEN 0) len); [img_try (cbn [sv_denot]; unfold aLEN; img_change (ew (Ereg (virt R U) extra) 36) with (nth 4 extra (w64 0)); rewrite Hlen; unfold w64; rewrite unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)
| img_try (img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia) | img_try (cbn; img_lia) | img_try (try rewrite B2; img_exact HL) ]. }
img_apply Forall_nil. }
img_apply Forall_cons.
{ unfold R_scrA, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold TFX_IMG_END, ASTACK in *; img_lia)|].
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2208) 8 (SLit 1) (bv_unsigned (sv_denot (Ereg R []) (SLit 1)))); [img_try (rewrite Z_to_bv_bv_unsigned; img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SLit 1))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2208), SLit 1) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2200) 8 (SLit (0x53640 + D_2c4)) (bv_unsigned (sv_denot (Ereg R []) (SLit (0x53640 + D_2c4))))); [img_try (rewrite Z_to_bv_bv_unsigned; img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SLit (0x53640 + D_2c4)))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2200), SLit (0x53640 + D_2c4)) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2192) 8 (SOff 11 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 10 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 10 10%bv eq_refl), (ew_Ereg_nat (virt R U) extra 11 11%bv eq_refl), (virt_11 R U); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 10 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2192), SOff 10 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2184) 8 (SOff 10 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 11 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 11 11%bv eq_refl), (ew_Ereg_nat (virt R U) extra 10 10%bv eq_refl), (virt_10 R U); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 11 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2184), SOff 11 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2176) 8 (SOff 2 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 2 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 2 2%bv eq_refl), (ew_Ereg_nat (virt R U) extra 2 2%bv eq_refl), (virt_same R U 2%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 2 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2176), SOff 2 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2168) 8 (SLit (0x32340 + D_150)) (bv_unsigned (sv_denot (Ereg R []) (SLit (0x32340 + D_150))))); [img_try (rewrite Z_to_bv_bv_unsigned; img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SLit (0x32340 + D_150)))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2168), SLit (0x32340 + D_150)) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-2152) 8 (SLit (0x536b0 + D_2c4)) (bv_unsigned (sv_denot (Ereg R []) (SLit (0x536b0 + D_2c4))))); [img_try (rewrite Z_to_bv_bv_unsigned; img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SLit (0x536b0 + D_2c4)))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-2152), SLit (0x536b0 + D_2c4)) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_nil. }
img_apply Forall_cons.
{ unfold R_topA, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold TFX_IMG_END, ASTACK in *; img_lia)|].
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-64) 8 (SOff 22 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 22 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 22 22%bv eq_refl), (ew_Ereg_nat (virt R U) extra 22 22%bv eq_refl), (virt_same R U 22%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 22 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-64), SOff 22 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-56) 8 (SOff 21 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 21 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 21 21%bv eq_refl), (ew_Ereg_nat (virt R U) extra 21 21%bv eq_refl), (virt_same R U 21%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 21 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-56), SOff 21 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-48) 8 (SOff 20 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 20 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 20 20%bv eq_refl), (ew_Ereg_nat (virt R U) extra 20 20%bv eq_refl), (virt_same R U 20%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 20 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-48), SOff 20 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-40) 8 (SOff 19 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 19 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 19 19%bv eq_refl), (ew_Ereg_nat (virt R U) extra 19 19%bv eq_refl), (virt_same R U 19%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 19 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-40), SOff 19 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 18 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 18 18%bv eq_refl), (ew_Ereg_nat (virt R U) extra 18 18%bv eq_refl), (virt_same R U 18%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 18 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-32), SOff 18 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 9 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 9 9%bv eq_refl), (ew_Ereg_nat (virt R U) extra 9 9%bv eq_refl), (virt_same R U 9%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 9 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-24), SOff 9 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 8 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 8 8%bv eq_refl), (ew_Ereg_nat (virt R U) extra 8 8%bv eq_refl), (virt_same R U 8%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 8 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-16), SOff 8 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (sv_denot (Ereg R []) (SOff 1 0)))); [img_try (rewrite Z_to_bv_bv_unsigned; cbn [sv_denot]; rewrite (ew_Ereg_nat R [] 1 1%bv eq_refl), (ew_Ereg_nat (virt R U) extra 1 1%bv eq_refl), (virt_same R U 1%bv ltac:(cbn [In]; tauto)); img_refl)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) (SOff 1 0))) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (try rewrite B2; pose proof (GF ((-8), SOff 1 0) ltac:(unfold PAFRAMES; cbn [In]; repeat first [left; img_refl | right])) as X; cbn [fst snd] in X; img_exact X) ]. }
img_apply Forall_nil. }
img_apply Forall_nil.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma call_trace_virt : forall ly pc0 R U ch, call_trace ly pc0 (virt R U) ch = call_trace ly pc0 R ch.
Proof.
intros ly pc0 R U ch. unfold call_trace, frame0_ok, spZ, raZ, s0Z.
rewrite (virt_same R U 2%bv ltac:(img_try (cbn [In]; tauto))), (virt_same R U 1%bv ltac:(img_try (cbn [In]; tauto))), (virt_same R U 8%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
Qed.
Section c. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Hypothesis D1 : tfx_depot_spec B.
Hypothesis IA1 : tfx_ialloc_spec.
Hypothesis U1 : tfx_unwind_spec.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (R : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (pp : sptr) (nold rn : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x53640 + D_2c4) R ch.
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Hypothesis PRE : acall_pre tfxsegs B ly S W R mem md ch.
Hypothesis HBLK : In (pp, nold) (blocks S).
Hypothesis HA0 : getr R 10 = w64 (sptr_addr B ly pp).
Hypothesis HA1 : getr R 11 = w64 rn.
Hypothesis Nrange : 64513 <= rn < MALLOC_MAX.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + rn <= LIVE_MAX.
Hypothesis Hev : aregime s1.
Definition jab_leaf (r : sptr * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists (U : bvmap 5 word) (memU : word -> option byte) (mdU : Model),
AR tfxsegs B ly s1 W memU mdU /\ same_io md mdU /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly s1 a -> ~ ascratch B ASTACK R a ->
aview tfxsegs (w_H W) memU a = aview tfxsegs (w_H W) mem a) /\
(forall a, spZ R <= a < ly_top ly -> aview tfxsegs (w_H W) memU a = aview tfxsegs (w_H W) mem a) /\
mid_leaf B ly s1 W (virt R U) memU mdU rn tr r W' c'.

End c.
End b.
