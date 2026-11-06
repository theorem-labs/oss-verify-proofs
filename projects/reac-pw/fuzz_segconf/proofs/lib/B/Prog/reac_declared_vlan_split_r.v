(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 108 of its 144 lines of code are new or changed and 218 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the image-B port of
   lib/A/Prog/reac_declared_vlan_split_r.v (commit ceb7e39832b2); image B's epilogue is image
   A's. The point KR (0x8a324), the epilogue. Eight loads restore ra and s0 .. s6 from the frame, `addi sp,sp,64`
   gives the entry sp back, `ret` returns to the entry ra; with the journal and the functional post of a0 at the
   point, the return is apost_base's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of a seeded state, without normalising its term *)
Ltac vs_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
(* awr_ok over the regions of a state with no write window *)
Ltac vs_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vs_view_mod : forall (H : word -> bool) (m : word -> option byte) a,
  aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof using.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.
Lemma vs_view_ext : forall (H : word -> bool) (m1 m2 : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m2 a = aview SEGS H m1 a) -> forall a, aview SEGS H m2 a = aview SEGS H m1 a.
Proof using.
intros H m1 m2 HK a. rewrite (vs_view_mod H m2 a), (vs_view_mod H m1 a). apply HK. apply Z.mod_pos_bound. lia.
Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Lemma vs_Q_ext : forall e ly' S' (W' : world SEGS) regs' mem1 mem2 md1 md2,
  (forall a, rdW W' mem2 a = rdW W' mem1 a) -> vs_Q B e ly' S' W' regs' mem1 md1 -> vs_Q B e ly' S' W' regs' mem2 md2.
Proof using.
intros e ly' S' W' regs' mem1 mem2 md1 md2 HK (H1 & H2 & H3 & H4). split; [exact H1|]. split.
{ destruct (SegModel.vlan_split (e_s e)) as [[p v]|]; [|exact I].
  destruct H2 as [[Hb Hn] Hv]. split; [split; [intros i Hi; rewrite HK; exact (Hb i Hi) | exact Hn]|].
  intros k Hk. rewrite HK. exact (Hv k Hk). }
split; [intros a Ha Hw He; rewrite HK; exact (H3 a Ha Hw He) | exact H4].
Qed.

Lemma vs_KR : vs_KR_stmt B gotw guard.
Proof using.
unfold vs_KR_stmt. intros e ly' S' W' regs' mem' md' v HE HJ Hsp G3 G4 G27 G22 HSL H10 HQ.
destruct HE as (HPRE & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HVS : VS_STK = 12352) by reflexivity.
unfold e_sp in *.
assert (Hsp64 : (spZ regs' + 64) = spZ (e_regs e)) by lia.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))) (vs_ssK VS_KR [])
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (BASE + VS_KR)) mem' (seg_rom SEGS)))).
{ apply vs_seedK; [rewrite Hsp64; exact HSL | lia | | exact G22 | exact I].
  rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
unfold vs_goal, vs_cfg.
paj_run_shc RUNP RUNC HS HJ.
{ vs_awr_ro. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN end.
eapply (RET W' _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly', S', r, m, d end.
split.
{ vs_preg HS (1%bv : bv 5) F1. rewrite F1. cbn [sv_denot]. subst E.
  rewrite (vs_Exn regs' (e_regs e) [] 32 0 1%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | unfold EV_reac_declared_vlan_split; lia]. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
  rewrite (st_ok_pi_restrict_reg (w_H W') E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; subst E.
  - rewrite (vs_EE regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hsp64.
    apply Z_to_bv_bv_unsigned.
  - rewrite (vs_EE regs' _ 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G3.
  - rewrite (vs_EE regs' _ 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G4.
  - rewrite (vs_Exn regs' (e_regs e) [] 33 1 8%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 34 2 9%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 35 3 18%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 36 4 19%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 37 5 20%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 38 6 21%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_Exn regs' (e_regs e) [] 39 7 22%bv eq_refl eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (vs_EE regs' _ 23 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact (G27 23 ltac:(lia)).
  - rewrite (vs_EE regs' _ 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact (G27 24 ltac:(lia)).
  - rewrite (vs_EE regs' _ 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact (G27 25 ltac:(lia)).
  - rewrite (vs_EE regs' _ 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact (G27 26 ltac:(lia)).
  - rewrite (vs_EE regs' _ 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact (G27 27 ltac:(lia)). }
apply (vs_Q_ext e ly' S' W' _ mem' _ md').
{ apply vs_view_ext. intros a Ha. exact (UN a Ha (fun x => x)). }
apply HQ. vs_preg HS (10%bv : bv 5) F10. rewrite F10. cbn [sv_denot]. subst E.
rewrite (vs_EE regs' _ 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact H10.
Qed.
End e.
End f.
End d.
