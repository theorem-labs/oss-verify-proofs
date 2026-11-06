(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbk YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h YC8j YCbc YCbf YCbd.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe YCbg.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YCb9 YCb6 YCba YCb7 YCbb YCb4.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma rn_fact_In : forall segs E ss ms n af, st_ok segs E ss ms -> In (n, af) (f_atoms (ss_facts ss)) -> afact_ok E n af.
Proof.
intros segs E ss ms n af HS Hin. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & _ & _)).
pose proof (atoms_ok_incl E _ [(n, af)] ltac:(intros x [<-|[]]; exact Hin) Ha) as [H _]. exact H.
Qed.
Section h.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma U_addw_small : forall E a b, U E a + U E b < 2 ^ 31 -> U E (SAluw ALU_ADD a b) = U E a + U E b.
Proof.
intros E a b Hab. pose proof (U_range E a) as Ha. pose proof (U_range E b) as Hb. unfold M64 in Ha, Hb.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite !(Z.mod_small _ (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (U E a + U E b + 2 ^ 31)) by lia. replace (U E a + U E b + 2 ^ 31 - 2 ^ 31) with (U E a + U E b) by lia.
apply Z.mod_small. lia.
Qed.
Lemma mod64_negcoef : forall a s c, 0 <= s -> 0 <= c - (2 ^ 64 - a) * s -> c - (2 ^ 64 - a) * s < 2 ^ 64 ->
(a * s + c) mod 2 ^ 64 = c - (2 ^ 64 - a) * s.
Proof.
intros a s c Hs Hlo Hhi. replace (a * s + c) with ((c - (2 ^ 64 - a) * s) + s * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Ltac kill_ovf Hc E38 :=
exfalso;
lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev (SAluw ALU_ADD ?X ?Y)) (sv_denot _ ?A3) = true =>
let HX := fresh "HX" in let HY := fresh "HY" in let HA := fresh "HA" in let HU := fresh "HU" in
let lx := eval vm_compute in (lin_of X) in lazymatch lx with Some (?l, ?c) =>
pose proof (lin_of_sound Ev X l c ltac:(vm_compute; reflexivity)) as HX end;
let ly := eval vm_compute in (lin_of Y) in lazymatch ly with Some (?l, ?c) =>
pose proof (lin_of_sound Ev Y l c ltac:(vm_compute; reflexivity)) as HY end;
let la := eval vm_compute in (lin_of A3) in lazymatch la with Some (?l, ?c) =>
pose proof (lin_of_sound Ev A3 l c ltac:(vm_compute; reflexivity)) as HA end;
cbn [lin_denot] in HX, HY, HA; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HX, HY, HA; rewrite ?ew_ewset_other in HX, HY, HA by lia;
rewrite E38 in HX, HY, HA; rewrite ?unsigned_lit_small in HX, HY, HA by lia;
rewrite ?Z.add_0_r in HX; rewrite ?Z.add_0_r in HY; rewrite ?Z.add_0_r in HA;
unfold M64 in HX, HY, HA;
first [rewrite Z.mod_small in HX by lia | rewrite mod64_negcoef in HX by lia];
first [rewrite Z.mod_small in HY by lia | rewrite mod64_negcoef in HY by lia];
first [rewrite Z.mod_small in HA by lia | rewrite mod64_negcoef in HA by lia];
assert (HU : U Ev (SAluw ALU_ADD X Y) = U Ev A3) by (rewrite U_addw_small by (rewrite HX, HY; lia); rewrite HX, HY, HA; lia);
apply U_inj in HU; rewrite HU in Hc; unfold branch_taken in Hc; rewrite bv_eqb_unsigned, Z.eqb_refl in Hc; discriminate Hc
end.
Ltac eval_n Nx E38 HN :=
lazymatch Nx with U ?Ev (SAlu ALU_SRL ?inner (SLit 48)) =>
let HI := fresh "HI" in
let li := eval vm_compute in (lin_of inner) in lazymatch li with Some (?l, ?c) =>
pose proof (lin_of_sound Ev inner l c ltac:(vm_compute; reflexivity)) as HI end;
cbn [lin_denot] in HI; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HI; rewrite ?ew_ewset_other in HI by lia;
rewrite E38 in HI; rewrite ?unsigned_lit_small in HI by lia; rewrite ?Z.add_0_r in HI; unfold M64 in HI;
first [rewrite Z.mod_small in HI by lia | rewrite mod64_negcoef in HI by lia];
lazymatch type of HI with _ = ?v =>
assert (HN : Nx = v / 2 ^ 48)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite HI, U_SLit; change (Z.land (zcanon 48) 63) with 48;
rewrite Z.shiftr_div_pow2 by lia; apply zcanon_id; unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]) end;
lazymatch type of HN with _ = (?c - (2 ^ 64 - ?a) * ?sg) / _ =>
let q := eval vm_compute in (c / 2 ^ 48) in let m := eval vm_compute in ((2 ^ 64 - a) / 2 ^ 48) in
replace (c - (2 ^ 64 - a) * sg) with ((q - m * sg) * 2 ^ 48) in HN by lia; rewrite Z.div_mul in HN by lia end;
clear HI
end.
Ltac xdummy_facts HS :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let RF := lazymatch goal with H : ew _ 516 = Z_to_bv 64 _ |- _ => H end in
lazymatch type of RF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict ?Hw ?msx) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i0 := xidx_reg rsm 516%nat 0 in let i0 := eval vm_compute in i0 in let r0 := eval vm_compute in (nth i0 rsm got_regionP) in
let i2 := xidx_reg rsm 529%nat 0 in let i2 := eval vm_compute in i2 in let r2 := eval vm_compute in (nth i2 rsm got_regionP) in
let HR0 := fresh "HR0" in let HR2 := fresh "HR2" in let V4 := fresh "V4" in let Hsh4 := fresh "Hsh4" in let Hsa := fresh "Hsa" in
let Vpd := fresh "Vpd" in let HRApd := fresh "HRApd" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict] in HR0;
pose proof (st_ok_pi_region_nth Ev ssx (restrict Hw msx) i2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict] in HR2;
xbyte HR0 32 Vpd;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ev _ 529 (SB + Fv / 8) cs lo hi wlo whi 4 1%N (SLit 1) 1 HR2 ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4 end;
pose proof (aview_of_val_mem1 pa_segs _ _ _ _ V4 ltac:(lia)) as Hsh4;
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
assert (Hsa : shadow_of_addr SHADOW_OFF (Fv + 32) = SB + Fv / 8 + 4)
by (unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF; rewrite HFq at 1; rewrite HF8;
replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
assert (HRApd : range_addressable (aview pa_segs Hw (ms_mem msx)) SHADOW_OFF (Fv + 32) 1)
by (apply (block_shadow_range _ _ (Fv + 32) 1); [| lia | lia];
apply block_shadow_cells1; [rewrite HFq; replace (32 * (Fv / 32) + 32) with ((4 * (Fv / 32) + 4) * 8) by lia; apply Z_mod_mult | lia | rewrite Hsa; exact Hsh4]);
clear HR0 HR2 V4 Hsh4 Hsa end end.
Ltac xpre_D_sinkB :=
lazymatch goal with H : asink_at ?sg ?Kv ?m ?md ?f ?L |- _ =>
lazymatch L with context [?Sg ++ PRE_G ?Wd ?Hd ?sgct ?GCT ?rattr ?loops] =>
let HKs1 := lazymatch goal with Hk : sgct <= 2 ^ _ |- _ => Hk end in
lazymatch type of HKs1 with _ <= 2 ^ ?Kl =>
let HKlo := lazymatch goal with Hk : 0 <= Kl <= 8 |- _ => Hk end in
let HKs2 := lazymatch goal with Hk : 2 ^ Kl < 2 * sgct |- _ => Hk end in
let Hc := lazymatch goal with Hk : sgct <> 0 |- _ => Hk end in
let Hn0 := lazymatch goal with Hk : _ - _ * sgct = 0 |- _ => Hk | Hk : _ - _ * sgct <> 0 |- _ => Hk end in
let v := eval vm_compute in (2 ^ Z.max Kl 1) in
assert (HSINKD : asink_at sg Kv m md f (Sg ++ PRE_D Wd Hd sgct GCT rattr loops));
[ replace (Sg ++ PRE_D Wd Hd sgct GCT rattr loops) with L; [exact H|];
unfold PRE_D, PRE_G, PRE_C; rewrite (proj2 (Z.eqb_neq sgct 0) Hc); rewrite (gct_pad_K Kl sgct GCT HKlo ltac:(lia) HKs1 HKs2);
change (2 ^ Z.max Kl 1) with v;
lazymatch type of Hn0 with
| ?n = 0 => replace (3 * (v - sgct)) with 0 by (clear - Hn0; lia); cbn [Z.to_nat repeat]
| ?n <> 0 => replace (3 * (v - sgct)) with n by (clear; lia) end;
rewrite ?app_nil_r, <- ?app_assoc; reflexivity | ] end end end.
Section j.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
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
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_both3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Ltac rn_drop_ly ly3 EFA3 EFL3 :=
repeat match goal with H : context [ly3] |- _ => first [clear H | rewrite EFA3 in H | rewrite EFL3 in H | fail 2 "ly3 still used in" H] end.
Lemma rn_G1X_5 : rn_fromX K MT B wfn hw ss_DX PRE_D -> rn_fromX K MT B wfn hw ss_G1X_5 PRE_G.
Proof.
rn_preludeX.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
assert (Hc : sgct <> 0).
{ pose proof (st_ok_cond_In SEGS E _ _ (mkAC BC_NE (SOff 38 0) (SLit 0)) HS ltac:(cbn; left; reflexivity)) as Q.
unfold acond_ok, branch_taken in Q. cbn [ac_c ac_a ac_b sv_denot negb] in Q. rewrite bv_eqb_unsigned in Q.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Q by lia.
destruct (Z.eqb_spec sgct 0); [discriminate Q | lia]. }
pose proof HJ3 as HJ5.
assert (HKlo : 0 <= 5 <= 8) by lia.
pose proof (rn_fact_In SEGS E _ _ 38%nat (mkAF 17 32 0) HS ltac:(cbn; tauto)) as HK38.
unfold afact_ok in HK38. cbn [af_lo af_hi af_al2] in HK38. rewrite E38, unsigned_lit_small in HK38 by lia.
assert (HKs1 : sgct <= 2 ^ 5) by (clear - HK38; lia). assert (HKs2 : 2 ^ 5 < 2 * sgct) by (clear - HK38; lia).
assert (HKK1 : 2 ^ 5 <= 2 ^ Z.max 5 1) by (apply Z.pow_le_mono_r; lia). clear HK38.
pose proof HKlo as HKloX. pose proof HKs1 as HKs1X. pose proof HKs2 as HKs2X.
all: norm_ss HS; reshok_bx HS 35%nat; relow HS AG E10 E32 E10' E32'.
all: paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x3d8.
all: try (oblFX HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
all: try (awrR AG fpos F EFA3).
all: xsink_stretch HFr HSINK.
all: try clear_frames.
all: psrr_branch_tok RUN BR HS SHOK RBspan; [kill_ovf Hc0 E38 |].
all: paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x3d8.
all: try (oblFX HJ5 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ5 E32' E35 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
all: try (awrR AG fpos F EFA3).
all: xsink_stretch HFr HSINK.
all: try clear_frames.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres5 & HFSpres5); change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5;
change (256 / 8) with 32 in HFSpres5; rewrite !EFA3 in HFpres5, HFSpres5; fold F in HFpres5, HFSpres5.
all: fs_rw HS E529 HFSpres5.
all: (paj_run_to_sh RUNTOP HS HJ5 0x3e4; [awrR AG fpos F EFA3|]).
all: xsink_stretch HFr HSINK.
all: clear_frames.
all: fs_ro HS; reshok_bx HS 35%nat.
all: psrr_branch_tok RUN BR HS SHOK RBspan.
all: lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?Ev ?Nx) (sv_denot _ (SLit 0)) = _ |- _ =>
eval_n (U Ev Nx) E38 HN;
rewrite branch_eq_U, U_SLit, HN in Hb; change (zcanon 0) with 0 in Hb end.
all: match goal with Hb : (_ =? 0) = true |- _ => apply Z.eqb_eq in Hb; rename Hb into Hn0 | Hb : (_ =? 0) = false |- _ => apply Z.eqb_neq in Hb; rename Hb into Hn0 end.
all: lazymatch type of Hn0 with _ = 0 =>
paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x414; [awrR AG fpos F EFA3|]; xsink_stretch HFr HSINK; clear_frames;
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ5) Hfin3) as (_ & _ & HFpres6 & HFSpres6); change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6;
change (256 / 8) with 32 in HFSpres6; rewrite !EFA3 in HFpres6, HFSpres6; fold F in HFpres6, HFSpres6;
fs_rw HS E529 HFSpres6;
paj_run_to_sh RUNTOP HS HJ5 0x424; [awrR AG fpos F EFA3|]; xsink_stretch HFr HSINK; clear_frames;
fs_ro HS; rebaseE HS AG HEv; clear HEv;
xpre_D_sinkB;
rn_join HS ss_DX 771%nat rn_deads_D;
lazymatch type of HJ5 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ5 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKD | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end
| _ <> 0 => idtac end.
all: lazymatch type of Hn0 with ?n <> 0 => assert (Hn : 3 <= n <= 765) by (clear - Hn0 HKs1 Hc R32; lia) end.
all: paj_run_to_tok RUNTO HS HJ5 SHOK RBspan 0x3e8; [awrR AG fpos F EFA3|].
all: xsink_stretch HFr HSINK.
all: clear_frames.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 42 0) hw HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 44 0) pf HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as M64 end;
clear HRg | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 42 0) hw HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 44 0) pf HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 40 0) (bv_unsigned (ew Ex 40)) HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 40)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as M64 end;
clear HRg  end.
all: prreg HS (2%bv : bv 5) Q2; prreg HS (21%bv : bv 5) Q19; prreg HS (22%bv : bv 5) Q21; prreg HS (19%bv : bv 5) Q18; prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25; prreg HS (23%bv : bv 5) Q23.
all: xdummy_facts HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
lazymatch type of Hn0 with ?n <> 0 =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 21%bv) in
assert (Qn : getr (ms_regs msX) 21%bv = Z_to_bv 64 n);
[ rewrite (st_ok_restrict_reg SEGS _ _ _ _ 21%bv HS); change (sv_denot Ev e = Z_to_bv 64 n);
apply bv_eq; rewrite unsigned_lit_small by lia; change (bv_unsigned (sv_denot Ev e)) with (U Ev e); exact HN | ] end | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
lazymatch type of Hn0 with ?n <> 0 =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 21%bv) in
assert (Qn : getr (ms_regs msX) 21%bv = Z_to_bv 64 n);
[ rewrite (st_ok_restrict_reg SEGS _ _ _ _ 21%bv HS); change (sv_denot Ev e = Z_to_bv 64 n);
apply bv_eq; rewrite unsigned_lit_small by lia; change (bv_unsigned (sv_denot Ev e)) with (U Ev e); exact HN | ] end  end.
all: assert (Qal : (spZ regs - 192) mod 16 = 0) by
(pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D;
replace (32 * (spZ regs / 32) - 192) with ((2 * (spZ regs / 32) - 12) * 16) by lia; apply Z_mod_mult).
all: prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8.
all: assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Qa & Qb & _)]; [exfalso; exact (Hchne Hnil) | lia]).
all: assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
all: assert (Qceil : alloc_ceiling <= spZ regs) by lia.
all: assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
all: assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
all: assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in let i := idx_of_base rsm 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
pose proof HJ5 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5)
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end end.
all: clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
all: aconsts HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
all: rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc].
all: eapply SRr_bind;
[ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of Hn0 with ?n <> 0 =>
lazymatch type of HSINK with asink_at _ _ _ _ _ ?SG =>
eapply (rn_wdbX B LAWS wfn hw Rwfn Rhw K AIL WFNX (Z.to_nat n) n W3 (ms_regs msX) (ms_mem msX) mdX
(spZ regs - 192) ly3 S3 g (bv_unsigned (ew Ev 40)) ((spZ regs, raZ regs, s0Z regs) :: ch) pf (F + 32) fpos SG ltac:(clear - Hn; lia)) end;
[ eapply (ajournal_sub_init SEGS B TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)] ly3 S3 W3 _ _ k WDBX_STK (spZ regs - 192) (asink_fp pf) (-192));
[exact HJ5 | clear; lia | reflexivity | clear; lia | unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia | rewrite FFS; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia]
| rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal
| rewrite Q3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Q4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| unfold s0Z at 1; rewrite Q8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; exact Hch1
| exact Qn | clear - Hn; lia | exact Q21
| rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E41
| rewrite Q25; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64
| pose proof (bv_unsigned_in_range 64 (ew Ev 40)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q
| rewrite Q23; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG
| exact Vpd | exact Hfin3 | exact Hinf3 | exact Hp_ia
| rewrite !EFA3; fold F; apply xfacts_i; clear - XF HFal; unfold xfacts in XF; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK, TRAWNEW_STK in *; lia
| exact HRApd | exact HSINK
| let HGlen := fresh "HGlen" in destruct (HGCT Hc) as (_ & _ & _ & _ & HGlen); clear - HSmax Hn HGlen Hc R32; unfold PRE_G, YI0j.hdr13 in *;
rewrite !length_app, length_firstn in *; cbn [length] in *; rewrite Nat.min_l by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia); unfold HDR_OUT in HSmax; lia ] end end end
| ].
all: cbv beta; intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJw & (Ely6 & ES6) & HK19 & HK21 & HSINKw & Hrg6); subst ly6 S6.
all: pose proof (Permutation_refl (ablocks B ly3 S3)) as HPb6; clear HSINK Vpd HRApd; rename HSINKw into HSINK.
all: clear Q2 Q19 Q21 Q18 Q24 Q25 Qn M56 M80 M64 Q3 Q4 Q8 Vra Vs0 Hch1.
all: pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJw ltac:(rewrite FFS; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia) ltac:(clear; lia)
ltac:(intros aa Haa; left; exact Haa)) as HJ6.
all: cbn [app] in HJ6; replace (k + 0) with k in HJ6 by lia.
all: pose proof (proj1 HJ6) as HAR6.
all: pose proof Hfrs3 as Hfrs6; pose proof Hfin3 as Hfin6; pose proof HfinS3 as HfinS6; pose proof Eab3 as Eab6; pose proof Hres_in as Hres_in6; pose proof Hing3 as Hing6.
all: pose proof EFA3 as EFA6; pose proof EFL3 as EFL6.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6); change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6;
change (256 / 8) with 32 in HFSpres6; rewrite !EFA6 in HFpres6, HFSpres6; fold F in HFpres6, HFSpres6.
all: destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR6 Hres_in6) as (_ & _ & _ & _ & Hrpres6 & _); change (req_size 48) with 48 in Hrpres6.
all: aconsts HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
let n := eval vm_compute in (length (ss_mem ssx)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_stretch_keep_hi HS kk regs6 (mrestrict (w_H W6) mem6) WDB_CLOB 0x404 idxs HS2;
specialize (HS2 Hrg6);
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 2 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; lia
| xFP | intros aa Haa; apply (fun H => proj1 (HFpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 2 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; lia
| xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 534%nat lo hi wlo whi _ res 48 HJw);
[ evalE AG | exact Hres_in | exact Hres_in6 | lia | change (req_size 48) with 48; lia
| xFP | intros aa Haa; apply (fun H => proj1 (Hrpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub SEGS B); [exact HJw | exact HJ6 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat cfgp lo hi wlo whi _ cid pos HJw);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub SEGS B); [exact HJw | evalE AG | exact Hing3 | exact Hing6 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| xFP ]
| |- _ => keptI I I AG Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
end
| specialize (HS2 HRK); clear HRK ] end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv; clear HEv.
all: pose proof (st_ok_pi_pin_reg' _ _ _ 21%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: pose proof (st_ok_pi_pin_reg' _ _ _ 22%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK21) eq_refl) as HS3; clear HS; rename HS3 into HS.
all: norm_ss HS.
all: clear HJ3 HAR3 Hfin3 HfinS3 Hing3 Hres_in Eab3 Hfrs3 HFpres3 HFSpres3 Hrpres3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 HJ5 HJw HPb6 Hwle6 Hrg6 HK19 HK21.
all: clear EFA3 EFL3.
all: rename HAR6 into HAR3; rename Hfin6 into Hfin3; rename HfinS6 into HfinS3; rename Hing6 into Hing3; rename Hres_in6 into Hres_in.
all: rename Eab6 into Eab3; rename Hfrs6 into Hfrs3; rename EFA6 into EFA3; rename EFL6 into EFL3; rename HFpres6 into HFpres3; rename HFSpres6 into HFSpres3.
all: rename Hrpres6 into Hrpres3; rename Kgot6 into Kgot3; rename Kcell6 into Kcell3; rename Kguar6 into Kguar3; rename Kuar6 into Kuar3; rename Vgr6 into Vgr3.
all: reshok_bx HS 35%nat; relow HS AG E10 E32 E10' E32'.
all: (paj_run_to_tok RUNTO HS HJ6 SHOK RBspan 0x414; [awrR AG fpos F EFA3|]).
all: xsink_stretch HFr HSINK.
all: clear_frames.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin3) as (_ & _ & HFpres7 & HFSpres7); change (fs_frame_bytes 2) with 256 in HFpres7, HFSpres7;
change (256 / 8) with 32 in HFSpres7; rewrite !EFA3 in HFpres7, HFSpres7; fold F in HFpres7, HFSpres7.
all: fs_rw HS E529 HFSpres7.
all: (paj_run_to_sh RUNTOP HS HJ6 0x424; [awrR AG fpos F EFA3|]).
all: xsink_stretch HFr HSINK.
all: clear_frames.
all: fs_ro HS; rebaseE HS AG HEv; clear HEv.
all: xpre_D_sinkB.
all: rn_join HS ss_DX 771%nat rn_deads_D.
all: lazymatch type of HJ6 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx _ _ _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E0 Ev Wx lyx Sx msv _ k fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_EX_havoc; [clear; lia | repeat (apply rn_EX_ewset; [clear; lia|]); split; [repeat (split; [eassumption|]); eassumption | split; [exact E44 | exact E45]]]
| split; [exact HJ6 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [exact HSINKD | exact MLE]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end end.
Qed.
End j.
End h.
End d.
