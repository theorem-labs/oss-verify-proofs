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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YE0v YF19.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF77 YF6b YF6p.
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
Definition R_N1 {imgk : img} : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- ASTACK) (-2160) (- ASTACK) (-2160)
[YQ0b.mkChunk (-2208) (CVal 8 (SLit 1)); YQ0b.mkChunk (-2200) (CVal 8 (SLit (0x53640 + D_2c4))); YQ0b.mkChunk (-2192) (CVal 8 (SOff 40 0)); YQ0b.mkChunk (-2184) (CVal 8 (SOff 41 0));
YQ0b.mkChunk (-2176) (CVal 8 (SOff 2 0)); YQ0b.mkChunk (-2168) (CVal 8 (SLit (0x32340 + D_150)))].
Definition R_N2 {imgk : img} : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-2160) (-64) 0 0 [YQ0b.mkChunk (-2152) (CVal 8 (SLit (0x536b0 + D_2c4)))].
Definition errR {imgk : img} : YQ0b.region := YQ0b.mkRegion None TFX_ERRNO (TFX_ERRNO + 4) TFX_ERRNO (TFX_ERRNO + 4) [].
Definition REGS_N {imgk : img} : list sv :=
[SLit 0; SOff 39 0; SOff 2 (-2208); SOff 3 0; SLit TFX_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 32 0; SOff 33 0; SLit 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
SOff 16 0; SOff 17 0; SOff 34 0; SOff 35 0; SOff 36 0; SOff 37 0; SOff 38 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition SN {imgk : img} : sstate := mkSS (0x323bc + D_150) REGS_N [R_N1; R_N2; R_TOP; errR] None (mkFacts [] [] []).
Definition nvirt (R M : bvmap 5 word) : bvmap 5 word :=
(regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd M 1 (getr R 1)) 2 (getr R 2)) 8 (getr R 8)) 9 (getr R 9)) 18 (getr R 18)) 19 (getr R 19)) 20 (getr R 20)) 21 (getr R 21)) 22 (getr R 22)).
Definition XN (R M : bvmap 5 word) : list word := [getr M 8; getr M 9; getr M 18; getr M 19; getr M 20; getr M 21; getr M 22; getr M 1; getr R 10; getr R 11].
Ltac nvirt_get := unfold nvirt; repeat first [ rewrite getr_same by (img_try (intros XX; discriminate XX)) | rewrite getr_other by (img_try (intros XX; discriminate XX)) ]; try img_refl.
Lemma nvirt_thunk : forall R M (r : bv 5), In r [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv -> getr (nvirt R M) r = getr R r.
Proof. intros R M r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (nvirt_get)|]). destruct Hr. Qed.
Lemma nvirt_mach : forall R M (r : bv 5), In r [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr (nvirt R M) r = getr M r.
Proof. intros R M r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [img_try (nvirt_get)|]). destruct Hr. Qed.
Lemma REGSN_ok {imgk : img} : forall (R M : bvmap 5 word),
getr M 2 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2208)) -> getr M 4 = w64 TFX_TP -> getr M 10 = w64 0 ->
regs_ok (Ereg (nvirt R M) (XN R M)) REGS_N M.
Proof.
intros R M F2 F4 F10.
img_apply regs_ok_by_cases. intros r Hr. unfold all_regs in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
lazymatch goal with |- getr M ?r = sv_denot _ (sr_get ?sr ?r) => let e := img_ev (sr_get sr r) in img_change (sr_get sr r) with e end.
- img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 39) with (getr M 1). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F2. cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 2 2%bv eq_refl), (nvirt_thunk R M 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 3 3%bv eq_refl), (nvirt_mach R M 3%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F4. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 5 5%bv eq_refl), (nvirt_mach R M 5%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 6 6%bv eq_refl), (nvirt_mach R M 6%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 7 7%bv eq_refl), (nvirt_mach R M 7%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 32) with (getr M 8). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 33) with (getr M 9). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite F10. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 11 11%bv eq_refl), (nvirt_mach R M 11%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 12 12%bv eq_refl), (nvirt_mach R M 12%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 13 13%bv eq_refl), (nvirt_mach R M 13%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 14 14%bv eq_refl), (nvirt_mach R M 14%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 15 15%bv eq_refl), (nvirt_mach R M 15%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 16 16%bv eq_refl), (nvirt_mach R M 16%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 17 17%bv eq_refl), (nvirt_mach R M 17%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 34) with (getr M 18). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 35) with (getr M 19). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 36) with (getr M 20). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 37) with (getr M 21). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. img_change (ew (Ereg (nvirt R M) (XN R M)) 38) with (getr M 22). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 23 23%bv eq_refl), (nvirt_mach R M 23%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 24 24%bv eq_refl), (nvirt_mach R M 24%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 25 25%bv eq_refl), (nvirt_mach R M 25%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 26 26%bv eq_refl), (nvirt_mach R M 26%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 27 27%bv eq_refl), (nvirt_mach R M 27%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 28 28%bv eq_refl), (nvirt_mach R M 28%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 29 29%bv eq_refl), (nvirt_mach R M 29%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 30 30%bv eq_refl), (nvirt_mach R M 30%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- cbn [sv_denot]. rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 31 31%bv eq_refl), (nvirt_mach R M 31%bv ltac:(img_try (cbn [In]; tauto))), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d. Context {imgk : img}.
Variable W : world tfxsegs.
Variable md : Model.
Let H := w_H W.
Definition cnull_post (R : bvmap 5 word) (memM : word -> option byte) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr R 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) /\
getr regs' 10 = w64 0 /\
(forall x : word, ~ (bv_unsigned (getr R 2) - ASTACK <= bv_unsigned x < bv_unsigned (getr R 2)) -> ~ (TFX_ERRNO <= bv_unsigned x < TFX_ERRNO + 4) -> mem' x = memM x) /\
(forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> apresent H mem' a).
Lemma c_null : forall (R M : bvmap 5 word) (memM : word -> option byte) (len : Z),
getr M 2 = Z_to_bv 64 (bv_unsigned (getr R 2) + (-2208)) -> getr M 4 = w64 TFX_TP -> getr M 10 = w64 0 ->
(forall r : bv 5, In r [3; 23; 24; 25; 26; 27]%bv -> getr M r = getr R r) -> getr R 4 = w64 TFX_TP -> YK0s.ret_ok (getr R 1) ->
CFRAMES_ok R len H memM ->
TFX_IMG_END + ASTACK <= bv_unsigned (getr R 2) -> (forall a, bv_unsigned (getr R 2) - ASTACK <= a < bv_unsigned (getr R 2) -> apresent H memM a) ->
SRr tfxsegs W (mkCfg (mkst M (w64 (0x323bc + D_150)) memM (seg_rom tfxsegs)) md) (cnull_post R memM).
Proof.
intros R M memM len F2 F4 F10 FK R4 Hra (_ & HF0) Hsp HPR.
pose proof YF8r.Hwx_tfa as Hwx.
set (sp0 := bv_unsigned (getr R 2)) in *.
pose proof (bv_unsigned_in_range 64 (getr R 2)) as U2. img_change (bv_modulus 64) with (2 ^ 64) in U2. fold sp0 in U2.
assert (GF : forall p, In p CFRAMES -> val_mem tfxsegs (mrestrict H memM) (sp0 + fst p) 8 (bv_unsigned (sv_denot (Ereg R []) (snd p)))) by (img_try (img_apply Forall_forall; img_exact HF0)). clear HF0.
set (E := Ereg (nvirt R M) (XN R M)).
assert (B2 : base_val E (Some 2%nat) = sp0).
{ cbn [base_val]. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 2 2%bv eq_refl), (nvirt_thunk R M 2%bv ltac:(img_try (cbn [In]; tauto))). img_refl. }
assert (WR : forall a, sp0 - ASTACK <= a < sp0 -> writable_at tfxsegs (mrestrict H memM) a).
{ intros a Ha. img_exact (YE0v.apresent_writable H memM a (HPR a Ha)). }
assert (CK : forall off eC e, In (off, eC) CFRAMES -> sv_denot E e = sv_denot (Ereg R []) eC ->
YQ0b.chunk_ok tfxsegs E (mrestrict H memM) sp0 (YQ0b.mkChunk off (CVal 8 e))).
{ intros off eC e Hin He. eapply (chunk_ok_val tfxsegs _ _ _ off 8 e (bv_unsigned (sv_denot (Ereg R []) eC))); [img_try (rewrite Z_to_bv_bv_unsigned; img_exact He)
| img_try (pose proof (bv_unsigned_in_range 64 (sv_denot (Ereg R []) eC)) as RR; img_change (bv_modulus 64) with (2 ^ 64) in RR; img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_exact RR) | img_try (cbn; img_lia)
| img_try (img_exact (GF (off, eC) Hin)) ]. }
assert (AT : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> In r [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv -> ew E k = ew (Ereg R []) k).
{ intros k r Hk Hr. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) k r Hk), (ew_Ereg_nat R [] k r Hk). img_exact (nvirt_thunk R M r Hr). }
assert (HS : st_ok tfxsegs E SN (restrict (w_H W) (mkst M (w64 (0x323bc + D_150)) memM (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold SN, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [img_refl|]). split; [img_try (img_exact (REGSN_ok R M F2 F4 F10))|]. split; [|img_try (split; [img_exact I | split; img_exact I])].
split; [img_try ((img_case; vm_compute); img_refl)|]. split.
- img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
+ unfold R_N1, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. fold E. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold ASTACK in *; img_lia)|].
img_apply Forall_cons; [img_try (img_apply (CK (-2208) (SLit 1)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2200) (SLit (0x53640 + D_2c4))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2192) (SOff 10 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] |
cbn [sv_denot]; img_change (ew E 40) with (getr R 10); rewrite (ew_Ereg_nat R [] 10 10%bv eq_refl); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2184) (SOff 11 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] |
cbn [sv_denot]; img_change (ew E 41) with (getr R 11); rewrite (ew_Ereg_nat R [] 11 11%bv eq_refl); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2176) (SOff 2 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 2%nat 2%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-2168) (SLit (0x32340 + D_150))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|].
img_apply Forall_nil.
+ unfold R_N2, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. fold E. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [img_try (img_apply (CK (-2152) (SLit (0x536b0 + D_2c4))); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | img_refl])|]. img_apply Forall_nil.
+ unfold R_TOP, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks]. fold E. rewrite B2.
split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)|]. split; [img_try (intros o Ho; img_apply WR; unfold ASTACK in *; img_lia)|].
img_apply Forall_cons; [img_try (img_apply (CK (-64) (SOff 22 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 22%nat 22%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-56) (SOff 21 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 21%nat 21%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-48) (SOff 20 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 20%nat 20%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-40) (SOff 19 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 19%nat 19%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-32) (SOff 18 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 18%nat 18%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-24) (SOff 9 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 9%nat 9%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-16) (SOff 8 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 8%nat 8%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_cons; [img_try (img_apply (CK (-8) (SOff 1 0)); [unfold CFRAMES; cbn [In]; repeat first [left; img_refl | right] | cbn [sv_denot]; rewrite (AT 1%nat 1%bv eq_refl ltac:(cbn [In]; tauto)); img_refl])|].
img_apply Forall_nil.
+ unfold errR, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_try (unfold TFX_ERRNO; img_lia)|]. split; [img_try (unfold TFX_ERRNO; img_lia)|]. split; [|img_try (img_apply Forall_nil)]. intros o Ho. rewrite Z.add_0_l. img_apply rw_writable. unfold TFX_ERRNO in *. img_lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_N1, R_N2, R_TOP, errR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi]. fold E. rewrite !B2. cbn [base_val].
unfold TFX_ERRNO, TFX_IMG_END, ASTACK in *. repeat split; img_lia. }
change (w64 (0x323bc + D_150)) with (Z_to_bv 64 (0x323bc + D_150)) in HS |- *.
srr_run_sh tfxtbl_rr_ok HS.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
assert (FRT : forall x : word, ~ (sp0 - ASTACK <= bv_unsigned x < sp0 - 2160) -> ~ (sp0 - 64 <= bv_unsigned x < sp0) -> ~ (TFX_ERRNO <= bv_unsigned x < TFX_ERRNO + 4) -> ms_mem msR x = memM x).
{ intros x Hx1 Hx1' Hx2. img_apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg).
lazymatch type of Hin with In _ (windows ?rs) => let ws := img_ev (windows rs) in img_change (windows rs) with ws in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <-; cbn [fst snd] in Hrg; try rewrite B2 in Hrg; cbn [base_val] in Hrg; unfold TFX_ERRNO, ASTACK in *; img_lia)|]).
destruct Hin. }
eapply (SRr_ret_at tfxsegs tfxtbl_rr tfxtbl_rr_ok Hwx W E); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. split; [img_refl|].
rreg HS (1%bv : bv 5) Q1. rewrite (AT 1%nat 1%bv eq_refl ltac:(img_try (cbn [In]; tauto))), (ew_Ereg_nat R [] 1 1%bv eq_refl) in Q1.
exists (ms_regs msR), (ms_mem msR), mat'.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split.
{ intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
- rreg HS (2%bv : bv 5) Q. rewrite Q. rewrite (AT 2%nat 2%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 2 2%bv eq_refl).
- rreg HS (3%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 3 3%bv eq_refl), (nvirt_mach R M 3%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto.
- rreg HS (4%bv : bv 5) Q. rewrite Q. symmetry. img_exact R4.
- rreg HS (8%bv : bv 5) Q. rewrite Q. rewrite (AT 8%nat 8%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 8 8%bv eq_refl).
- rreg HS (9%bv : bv 5) Q. rewrite Q. rewrite (AT 9%nat 9%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 9 9%bv eq_refl).
- rreg HS (18%bv : bv 5) Q. rewrite Q. rewrite (AT 18%nat 18%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 18 18%bv eq_refl).
- rreg HS (19%bv : bv 5) Q. rewrite Q. rewrite (AT 19%nat 19%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 19 19%bv eq_refl).
- rreg HS (20%bv : bv 5) Q. rewrite Q. rewrite (AT 20%nat 20%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 20 20%bv eq_refl).
- rreg HS (21%bv : bv 5) Q. rewrite Q. rewrite (AT 21%nat 21%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 21 21%bv eq_refl).
- rreg HS (22%bv : bv 5) Q. rewrite Q. rewrite (AT 22%nat 22%bv eq_refl ltac:(img_try (cbn [In]; tauto))). img_exact (ew_Ereg_nat R [] 22 22%bv eq_refl).
- rreg HS (23%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 23 23%bv eq_refl), (nvirt_mach R M 23%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto.
- rreg HS (24%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 24 24%bv eq_refl), (nvirt_mach R M 24%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto.
- rreg HS (25%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 25 25%bv eq_refl), (nvirt_mach R M 25%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto.
- rreg HS (26%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 26 26%bv eq_refl), (nvirt_mach R M 26%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto.
- rreg HS (27%bv : bv 5) Q. rewrite Q. (subst E; cbv beta). rewrite (ew_Ereg_nat (nvirt R M) (XN R M) 27 27%bv eq_refl), (nvirt_mach R M 27%bv ltac:(img_try (cbn [In]; tauto))). img_apply FK. cbn [In]. tauto. }
split. { rreg HS (10%bv : bv 5) Q. img_exact Q. }
split; [img_try (intros x Hx1 Hx2; img_apply FRT; [unfold sp0, ASTACK in *; clear - Hx1; img_lia | unfold sp0, ASTACK in *; clear - Hx1; img_lia | img_exact Hx2])|].
fold sp0.
intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2160)) as [L1|L1]; [|img_try (destruct (Z_lt_le_dec a (sp0 - 64)) as [L2|L2])].
- eapply (st_ok_window_apresent (w_H W) E _ _ 0 _ a HS); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite B2; unfold ASTACK in *; img_lia) | img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)].
-
img_apply (apresent_same H memM (ms_mem msR) a); [|img_try (img_exact (HPR a Ha))]. img_apply FRT; rewrite unsigned_lit_small by (img_try (clear - Ha U2 Hsp; unfold TFX_IMG_END, ASTACK in *; img_lia)); [img_try (clear - L1; img_lia) | img_try (clear - L2; img_lia) | img_try (clear - Ha Hsp; unfold TFX_ERRNO, TFX_IMG_END, ASTACK in *; img_lia)].
- eapply (st_ok_window_apresent (w_H W) E _ _ 2 _ a HS); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; rewrite B2; img_lia) | img_try (unfold TFX_IMG_END, ASTACK in *; img_lia)].
Qed.
End d.
End c.
