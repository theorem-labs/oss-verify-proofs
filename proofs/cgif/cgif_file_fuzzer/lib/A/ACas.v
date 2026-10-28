(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba ACb7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac idx_of_baselo rs n lo :=
lazymatch rs with
| YP09.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baselo tl n lo in constr:(S i)
end.
Definition dropAt {A} (i : nat) (m : list A) : list A := firstn i m ++ skipn (S i) m.
Lemma range_addressable_zero8 : forall (rd : Z -> option Z) Bs p,
rd (shadow_of_addr Bs p) = Some 0 -> p mod 8 = 0 -> range_addressable rd Bs p 8.
Proof.
intros rd Bs p Hz Hp. apply zero_shadow_range; [exact Hp | reflexivity |].
intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact Hz.
Qed.
Ltac xhas_net Hc :=
let E34 := lazymatch goal with H : ew _ 34 = Z_to_bv 64 ?r |- _ => H end in
lazymatch type of E34 with _ = Z_to_bv 64 ?rattr =>
let R24 := lazymatch goal with H : 0 <= rattr < _ |- _ => H end in
let Hnet := fresh "Hnet" in let Hl := fresh "Hl" in
unfold branch_taken in Hc; rewrite ?bv_eqb_unsigned in Hc; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc;
rewrite ?ew_ewset_other in Hc by lia; rewrite E34 in Hc; rewrite alu64_unsigned in Hc; cbn [zalu_raw] in Hc;
rewrite (unsigned_lit_small rattr) in Hc by (clear - R24; lia); rewrite Z.add_0_r in Hc;
rewrite (unsigned_lit_small rattr), (unsigned_lit_small 3), (unsigned_lit_small 1) in Hc by (clear - R24; lia);
assert (Hl : 0 <= Z.land rattr 3 <= 3) by (rewrite (YI0j.land_bits01 rattr 3) by lia; destruct (Z.testbit _ _ && _), (Z.testbit _ _ && _); cbn; lia);
unfold bv_wrap, bv_modulus in Hc; rewrite (Z.mod_small (Z.land rattr 3)) in Hc by (clear - Hl; cbn; lia);
pose proof (YI0j.has_net_land rattr) as Hnet; destruct (Z.land rattr 3 =? 1); cbn [negb] in Hc; try discriminate Hc; clear Hc Hl end.
Ltac xpre_X_sink :=
lazymatch goal with H : asink_at ?sg ?Kv ?m ?md ?f ?L |- _ =>
lazymatch L with context [?Sg ++ PRE_D ?Wd ?Hd ?sgct ?GCT ?rattr ?loops] =>
let Hnet := lazymatch goal with Hn : YI0j.has_net rattr = _ |- _ => Hn end in
assert (HSINKX : asink_at sg Kv m md f (Sg ++ PRE_X Wd Hd sgct GCT rattr loops));
[ replace (Sg ++ PRE_X Wd Hd sgct GCT rattr loops) with L; [exact H|];
unfold PRE_X, PRE_D; rewrite YI0j.raw_header_eq; unfold rn_pk; rewrite Hnet; rewrite ?app_nil_r, <- ?app_assoc; reflexivity | ] end end.
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_asan3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Lemma rn_DX : rn_fromX K MT B wfn hw ss_XX PRE_X -> rn_fromX K MT B wfn hw ss_DX PRE_D.
Proof.
rn_preludeX.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as (_ & [_ R8] & [_ R16] & [_ R24] & [_ R28] & [_ R30] & [_ R32] & [_ R34] & _).
cbn [fst snd N.to_nat Z.of_N] in R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
norm_ss HS. reshok_bx HS 35%nat.
paj_run_tok RUN HS HJ3 SHOK RBspan.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
psrr_branch_tok RUN BR HS SHOK RBspan.
-
xhas_net Hc.
paj_run_to_tok RUNTO HS HJ3 SHOK RBspan 0x4d0.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
all: try (oblR HJ3 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
rebaseE HS AG HEv. clear HEv.
xpre_X_sink.
rn_join HS ss_XX 871%nat rn_deads_X_X_unused.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKX | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
-
xhas_net Hc.
paj_run_to_tok RUNTO HS HJ3 SHOK RBspan 0x4d0.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
all: try (oblR HJ3 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
xnet19_facts HS.
wcb_siteX (13%bv : bv 5) HS HWX HGA HRAX HHVX HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
reshok_bx HS 35%nat. relow HS AG E10 E32 E10' E32'.
paj_run_to_tok RUNTO HS HJ3 SHOK RBspan 0x4d0.
all: try (oblFX HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
all: try (oblR HJ3 Rres E35 Hres_in).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrR AG fpos F EFA3.
xsink_stretch HFr HSINK. clear_frames.
rebaseE HS AG HEv. clear HEv.
xpre_X_sink.
rn_join HS ss_XX 871%nat rn_deads_X_X_unused.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ3 | split; [clear - Hk3; lia | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKX | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
Qed.
End d.
End c.
End b.
