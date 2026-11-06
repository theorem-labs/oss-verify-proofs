(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rn_C : rn_from B ss_D -> rn_from B ss_G -> rn_from B ss_C.
Proof.
intros RD. rn_prelude.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
assert (E32' : ew E 32 = Z_to_bv 64 g) by (rewrite (AG 32%nat) by lia; exact E32).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 2%nat) (-208) (-192) (-208) (-192) []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 2%nat) by lia; rewrite Usp; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
1: awrR AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan 0x891c4; [awrR AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
rn_join HS ss_D 300%nat rn_deads_D.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RD ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
-
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia.
rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan 0x890fc.
all: try (oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (oblG HJ3 E32' E35 Hing3).
1: awrR AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
rn_join HS ss_G 220%nat rn_deads_G.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msv) =>
eapply (RC ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos res);
[ exact HPRE | exact Hal32 | exact HROD | split; [exact Hfin | repeat (split; [eassumption|]); exact HRA] | exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| apply rn_E_havoc; [clear; lia | repeat (apply rn_E_ewset; [clear; lia|]); repeat (split; [eassumption|]); eassumption]
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
Qed.
End b.
End a.
