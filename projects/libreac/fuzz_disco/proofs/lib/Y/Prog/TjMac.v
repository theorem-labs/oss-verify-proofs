(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlLayBlock.v, with its module paths and module names changed; 1116 of its 1178 lines of code are new or changed and 882 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd AmemBlock8.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tjm_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tjm_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tjm_awr_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tjm_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tjm_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| fail 1 "tjm_awr: no rule for the head region" ];
tjm_awr_rec hd AG fpos F EFA
end.
Ltac tjm_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tjm_awr_rec hd AG fpos F EFA.
Ltac tjm_fact HS n f tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssv msv n f HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS end.
Ltac rrw HS r e' Utac :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
let e0 := eval vm_compute in (sr_get (ss_regs ssx) r) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_reg_fp Ex ssx (restrict Hh msx) r e' HS ltac:(vm_compute; reflexivity)
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg Hh Ex ssx msx r HS);
change (sr_get (ss_regs ssx) r) with e0; rewrite !(denot_lit_U Ex); f_equal; Utac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rebase HS AG :=
let HEv := fresh "HEv" in rebaseE HS AG HEv;
try (lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => rewrite <- HEv in SH end); clear HEv.
Ltac fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Local Ltac gadd H := let HG := fresh "HGq" in match goal with G : boxed _ |- _ => pose proof (conj G H) as HG; clear G; box HG end.
Local Ltac glia := first [match goal with HG : boxed _ |- _ => clear - HG; unbox; lia end | clear; lia | lia].
Local Ltac glia_with H := first [match goal with HG : boxed _ |- _ => clear - H HG; unbox; lia end | lia].
#[local] Ltac evalE AG ::=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by glia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by glia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; glia); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => glia | |- _ <= _ => glia | |- _ < _ => glia | |- _ <= _ < _ => glia | |- _ <= _ <= _ => glia | |- _ < _ <= _ => glia end
| idtac ].
Lemma tjm_garr8_u : forall segs (m : word -> option byte) (a k : Z) (n : nat) (T : list byte),
garr8 segs m a (map bv_unsigned T) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length T) ->
val_mem segs m (a + k) n (disco_table_c.u_at T k n) /\ 0 <= disco_table_c.u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros segs m a k n T HG Hk HkT.
assert (Hlen : length (disco_table_c.sub T k n) = n) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k n)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k n)) as H1. rewrite Hlen in H1.
split; [|unfold disco_table_c.u_at; lia].
intros j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte segs m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k n) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat n))) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma tjm_U_not : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit 18446744073709551615)) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv). rewrite U_lit by lia.
change 18446744073709551615 with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma tjm_age_U : forall E nn nl now ls, ew E nn = Z_to_bv 64 now -> ew E nl = Z_to_bv 64 ls -> 0 <= ls < now -> now < 2 ^ 64 ->
U E (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SOff nn 0) (SMd M_MUL (SOff nl 0) (SLit (-1)))) (SLit 4835703278458516699)) (SLit 18)) =
(now - ls) / 1000000.
Proof.
intros E nn nl now ls Hn Hl Hls Hnow.
rewrite U_SAlu, U_SMd, U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E nn now Hn ltac:(lia)), (U_atom E nl ls Hl ltac:(lia)), !U_SLit.
assert (Hm1 : zcanon (-1) = 2 ^ 64 - 1) by reflexivity.
assert (Hsub : zcanon (now + zcanon (ls * (2 ^ 64 - 1))) = now - ls).
{ unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace (now + ls * (2 ^ 64 - 1)) with ((now - ls) + ls * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite Hm1, Hsub.
change (zcanon 4835703278458516699) with 4835703278458516699. change (zcanon 18) with 18. change (Z.land 18 63) with 18.
pose proof (tj_lemmas.tj_quot_mach (now - ls) ltac:(lia)) as Q. unfold tj_lemmas.KDv in Q.
rewrite Z_to_bv_unsigned in Q. unfold bv_wrap, bv_modulus in Q. change (2 ^ Z.of_N 64) with (2 ^ 64) in Q.
unfold zcanon, M64. change (Z.of_N 64) with 64. rewrite Q.
apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma tjm_csub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 < l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjm_bltz_false : forall E x v, U E x = v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E x) (sv_denot E (SLit 0)) = true -> False.
Proof.
intros E x v HU Hv Hc. cbn [branch_taken] in Hc. unfold bv_lts in Hc.
assert (Hsx : bv_signed (sv_denot E x) = v) by (rewrite (YK11.bv_signed_small (sv_denot E x)); [exact HU | unfold U in HU; rewrite HU; lia]).
assert (Hs0 : bv_signed (sv_denot E (SLit 0)) = 0).
{ rewrite (YK11.bv_signed_small (sv_denot E (SLit 0)));
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)); rewrite U_SLit; change (zcanon 0) with 0; [reflexivity | lia]. }
rewrite Hsx, Hs0 in Hc. apply Z.ltb_lt in Hc. lia.
Qed.
Lemma tjm_hex2 : forall v, 0 <= v < 256 -> PfFacts.pf_hex2 v = hex2 v.
Proof.
intros v Hv.
assert (A : forallb (fun k => if list_eq_dec Z.eq_dec (PfFacts.pf_hex2 (Z.of_nat k)) (hex2 (Z.of_nat k)) then true else false)
(seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in A by lia. destruct (list_eq_dec Z.eq_dec _ _); [assumption | discriminate].
Qed.
Lemma tjm_P1_eq : forall (T : list byte), length T = 400%nat -> forall i, 0 <= i < 8 ->
P1 (Z.to_nat i) (reac_disco_table_json_c.tj_entry T i) = (if Nat.eqb (Z.to_nat i) 0 then [] else [44]) ++ [123; 34; 109; 97; 99; 34; 58; 34] ++
hex2 (disco_table_c.u_at T (48 * i + 0) 1) ++ [58] ++ hex2 (disco_table_c.u_at T (48 * i + 1) 1) ++ [58] ++
hex2 (disco_table_c.u_at T (48 * i + 2) 1) ++ [58] ++ hex2 (disco_table_c.u_at T (48 * i + 3) 1) ++ [58] ++
hex2 (disco_table_c.u_at T (48 * i + 4) 1) ++ [58] ++ hex2 (disco_table_c.u_at T (48 * i + 5) 1) ++ [34].
Proof.
intros T LT i Hi.
exact (tj_lemmas.tj_P1_eq 335160 341392 1 0 400000 3 T ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)
ltac:(lia) ltac:(lia) ltac:(lia) LT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) i Hi).
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Context {PRP : YXcalls.PARoPresent lib_both3_0_listing}.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Definition ss_tjMa : sstate :=
(mkSS 23788
[SLit 0; SOff 720 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 723 0; SOff 724 0; SOff 725 0; SOff 2 0; SOff 60 0; SOff 920 0; SOff 921 0; SOff 728 0; SOff 10 384; SOff 722 0; SOff 729 0; SOff 730 0; SOff 731 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 734 0; SOff 32 0; SOff 733 0; SOff 735 0; SOff 736 0; SOff 737 0; SOff 738 0; SOff 739 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 0 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(733%nat, mkAF 0 2147483647 0); (721%nat, mkAF 0 336 4); (740%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition INV_tjMa (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody B i cx E ly3 S3 W3 ms3 /\
exists acc : list Z,
ew E 733 = w64 (Z.of_nat (length acc)) /\ 0 < Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) = acc ++ tj_lemmas.tj_rest (c_T cx) (c_now cx) i /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ [0]).
Definition tjm_fromMa (i : Z) : Prop := tj_from0 B IMG ss_tjMa (INV_tjMa i).
Definition tjm_sepp (i : Z) : Z := if i =? 0 then VAL (A_OBJ 41) else VAL (A_OBJ 40).
Definition ss_tjMb : sstate :=
(mkSS 23824
[SLit 0; SOff 720 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 723 0; SOff 724 0; SOff 725 0; SOff 2 0; SOff 60 0; SAlu ALU_ADD (SOff 12 0) (SOff 733 0); SLit 1; SLit 1; SOff 960 0; SOff 722 0; SOff 729 0; SOff 730 0; SOff 731 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 734 0; SOff 32 0; SOff 733 0; SOff 735 0; SOff 736 0; SOff 737 0; SOff 738 0; SOff 739 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 0 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(733%nat, mkAF 0 2147483647 0); (721%nat, mkAF 0 336 4); (740%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition INV_tjMb (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody B i cx E ly3 S3 W3 ms3 /\ ew E 960 = w64 (tjm_sepp i) /\
exists acc : list Z,
ew E 733 = w64 (Z.of_nat (length acc)) /\ 0 < Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) = acc ++ tj_lemmas.tj_rest (c_T cx) (c_now cx) i /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ [0]).
Definition tjm_fromMb (i : Z) : Prop := tj_from0 B IMG ss_tjMb (INV_tjMb i).
Lemma tjm_keep_journal : forall (cx : tjcx) own ly' S' (W' : world SEGS) mem' md' k,
tj_baseX B IMG cx ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
own ly' S' W' mem' md' k ->
tj_keep B cx W' mem'.
Proof.
intros cx own ly' S' W' mem' md' k HB HJ.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HB. unfold tj_keep.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HB, HJ |- *.
destruct HB as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof Hobj as ((cid & pos & Hin & Hcid & Hal8 & Hflo & Hfhi) & Ht8 & Hra).
assert (HnF : forall x, inFP (tj_fp buf cap) x -> (x < kLowShadowBeg \/ kHighShadowEnd <= x) /\
~ (frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid)).
{ intros x Hx. unfold tj_fp in Hx. destruct (Z.ltb_spec cap 3) as [Hc|Hc]; [destruct Hx as (r & [] & _)|].
destruct (Hbuf Hc) as (Hbin & Hbsz).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md buf Nb cid pos HAR Hbin Hin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF.
destruct Hx as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
unfold in_app, kLowShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *. split; lia. }
split; [exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)|].
split.
- intros j Hj. destruct (Harr j Hj) as (Hv & Hr). split; [|exact Hr].
rewrite length_map, HlenT in Hj.
eapply val_mem_entry_frame; [exact HJ | exact Hin | lia | lia | | exact Hv].
intros x Hx HF. destruct (HnF x HF) as (_ & Hn). apply Hn. lia.
- split; [exists cid, pos; repeat split; assumption|]. split; [exact Ht8|].
eapply range_addressable_entry_frame; [exact LAWS | exact HJ | exact Hin | exact Hcid | exact Hflo | exact Hfhi | exact Hal8 | | exact HAR | exact Hra].
intros x HF. exact (proj1 (HnF x HF)).
Qed.
Lemma tjm_str : forall kk s ly S (W : world SEGS) mem md sp d n,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_ro_at kk s ->
IMG_TOP + 8 <= sp - SNPRINTF_STK ->
(d + n <= IMG_LO \/ IMG_TOP <= d) ->
pf_arg_asan (aview SEGS (w_H W) mem) (snp_out SNPRINTF_STK sp d n) (VAL (A_OBJ kk)) (APtr s) /\
fmt_at (aview SEGS (w_H W) mem) (snp_out SNPRINTF_STK sp d n) (VAL (A_OBJ kk)) s.
Proof.
intros kk s ly S W mem md sp d n HAR HROD Hro Hsp Hdn.
pose proof Hro as (Hg & Hrr & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (HIL : 0 < IMG_LO) by (unfold IMG_LO; lia).
assert (HIT : IMG_TOP + 64 < kLowMemEnd) by (unfold kLowMemEnd, IMG_TOP; lia).
set (w := VAL (A_OBJ kk)) in *. set (L := Z.of_nat (length s)) in *.
pose proof (Z.mod_pos_bound (w + L) 8 ltac:(lia)) as Hm.
assert (Hse : str_end w s <= w + L + 8 /\ w + L < str_end w s) by (unfold str_end; fold L; lia).
destruct (ro_read_ok_glob SEGS B tfib_globs ly S W mem md w (L + 1) w (L + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) Hlo ltac:(lia)) as [Hra Hhull].
assert (Hbytes : forall i, 0 <= i <= L -> aview SEGS (w_H W) mem (w + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)).
{ intros i Hi. rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ w (L + 1) (w + i) HROD (Hrr (w + i) ltac:(lia))
(tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hq. rewrite Z2Nat.id in Hq by lia. exact Hq. }
assert (Hdj : forall q, q <= L + 8 -> Forall (zdisjoint (w, q)) (snp_out SNPRINTF_STK sp d n)).
{ intros q Hq. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
split.
- unfold pf_arg_asan. split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [exact Hbytes|]. split.
{ intros x Hx. pose proof (tj_pad_ro kk s Hro x Hx) as Hp. unfold aview, mbyte.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)); [discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate | contradiction]. }
split; [apply Hdj; lia|]. split; [unfold amem_range; left; lia|]. split; assumption.
- unfold fmt_at. split; [lia|]. split; [exact Hbytes|]. split; [apply Hdj; lia|].
split; [unfold amem_range; left; lia|]. split; assumption.
Qed.
Lemma tjm_garr : forall (m : word -> option byte) (H : word -> bool) d (q : list Z),
(forall i, 0 <= i < Z.of_nat (length q) -> aview SEGS H m (d + i) = Some (nth (Z.to_nat i) q 0)) ->
aview SEGS H m (d + Z.of_nat (length q)) = Some 0 ->
garr8 SEGS (mrestrict H m) d (q ++ [0]).
Proof.
intros m H d q Hd Hz j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.ltb_spec j (length q)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt.
pose proof (Hd (Z.of_nat j) ltac:(lia)) as Hq. rewrite Nat2Z.id in Hq.
exact (val_mem1_of_aview SEGS H m (d + Z.of_nat j) _ Hq).
- assert (Hje : j = length q) by lia. subst j.
rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
exact (val_mem1_of_aview SEGS H m (d + Z.of_nat (length q)) 0 Hz).
Qed.
Ltac tjm_notw AG Ha :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG;
first [match goal with HG : boxed _ |- _ => clear - Ha HG; intros; unbox; lia end | intros Hrg; lia]|]);
destruct Hin.
Ltac tjm_kb AG HKB b c Wx msx HFr :=
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
let H := fresh "HKBn" in
assert (H : forall a, b <= a < b + c -> aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) (ms_mem msx) a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
etransitivity; [ eapply aview_kept_out; [exact HFr | glia_with Ha | tjm_notw AG Ha] | exact (HKB a Ha) ]);
clear HKB; rename H into HKB end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac tjm_kbm AG HKB b c Wx m00 HFr :=
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
let H := fresh "HKBn" in
assert (H : forall a, b <= a < b + c -> aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) m00 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
etransitivity; [ eapply aview_kept_out; [exact HFr | glia_with Ha | tjm_notw AG Ha] | exact (HKB a Ha) ]);
clear HKB; rename H into HKB end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac tjm_rw529 HS E529 Hp :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 529%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 32) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 32 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E529, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable _); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma tjm_seg1 : forall i, tjm_fromMa i -> tj_fromL B IMG i.
Proof.
intros i FMa. unfold tj_fromL, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
unfold INV_tjL in HINV.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0; pose proof HEX as HX0; unfold tj_baseX in HB0; unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
destruct HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG 33%nat) by glia; exact HE033).
assert (AG3 : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG; glia).
clear AG; rename AG3 into AG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity; assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; glia).
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBOK; pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia); clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS); pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS); pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *; set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(glia)) as Hob241; pose proof (pa_obj_img 1 ltac:(glia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(glia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar; pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres; fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh; fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img; rewrite EFA in HFhigh_img; fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(glia)); glia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by glia; rewrite Z.div_mul by glia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; glia).
assert (HF8hi : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; glia).
assert (HEsp0 : ew E0 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- HE02; symmetry; apply Z_to_bv_bv_unsigned).
destruct HINV as (Hk0 & Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & acc & E733 & Hacc & Htxt & Hgarr).
pose proof Hok as (HT1 & HT2 & HT3 & HT4); unfold disco_table_c.tbl_T1 in HT1.
assert (Hi8 : 0 <= i < 8) by glia.
unfold tj_keep in HKEEP; cbn [c_ly c_S c_t c_T] in HKEEP.
destruct HKEEP as (HROD3 & HgT & HobjT).
destruct HobjT as ((cid & pos & Hcin & Hcid & Hcal & Htlo & Hthi) & Ht8 & HraT).
assert (Hcin3 : In (cid, pos) (frames S3)) by (rewrite HFR; right; exact Hcin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hcin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hcin3) as HTimg; rewrite EFA in HTimg.
destruct (in_split _ _ Hcin) as (l2 & l3 & Hl23).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cid, pos) [] l2 l3 HAR3 ltac:(rewrite HFR, Hl23; reflexivity)) as HTsep.
unfold frame_rng, zdisjoint in HTsep; cbn [fst snd] in HTsep; rewrite !EFA in HTsep; fold F in HTsep; change (fs_frame_bytes 2) with 256 in HTsep.
set (TF := frame_addr ly cid pos) in *.
pose proof ASAN_CEIL_range as HAC.
assert (Ht : 4096 <= t /\ t + 400 <= 140737479966720) by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; glia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & HNbr).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep; fold F in Hbsep; change (fs_frame_bytes 2) with 256 in Hbsep; unfold zdisjoint in Hbsep; cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp; unfold off_img, IMG_LO, IMG_TOP in Hbimg.
pose proof (conj Hb4096 (conj Hbceil (conj Hbapp (conj Hbimg (conj Hbsep (conj Hcapb (conj HF4096 (conj HFceil (conj HFhigh (conj HFhigh_img (conj HF8lo (conj HF8hi (conj HFq (conj HF8 (conj HT4096 (conj HTceil (conj HTapp (conj HTimg (conj HTsep (conj Htlo (conj Hthi (conj Ht (conj HAC (conj Hsp1 (conj Hceil (conj Hslo (conj Hstk0 (conj Hshi (conj H47 (conj Hbot (conj Htop (conj Htop2 (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj HSK (conj HSNP (conj Hes (conj Hob241 (conj Hob242 (conj Hob253 (conj Huar (conj Hi8 (conj Hcap (conj Hcap3 (conj Hacc (conj HlenT Hk0))))))))))))))))))))))))))))))))))))))))))))))))) as HGB. box HGB.
assert (HKB : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
set (e := t + 48 * i). set (ls := disco_table_c.last_of T i). set (age := age_of now ls).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 740 Ev ssv msv [Z_to_bv 64 e; Z_to_bv 64 age] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 740%nat [Z_to_bv 64 e; Z_to_bv 64 age] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E740 : ew Ev 740 = Z_to_bv 64 e) by (rewrite HEv; exact (ew_havoc_new _ 740 [Z_to_bv 64 e; Z_to_bv 64 age] 0 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E741 : ew Ev 741 = Z_to_bv 64 age) by (rewrite HEv; exact (ew_havoc_new _ 740 [Z_to_bv 64 e; Z_to_bv 64 age] 1 (Z_to_bv 64 0) ltac:(cbn; glia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 906 Ev ssv msv [Z_to_bv 64 ls] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 906%nat [Z_to_bv 64 ls] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E906 : ew Ev 906 = Z_to_bv 64 ls) by (rewrite HEv; exact (ew_havoc_new _ 906 [Z_to_bv 64 ls] 0 (Z_to_bv 64 0) ltac:(cbn; glia))) end.
clear HEv.
destruct (tjm_garr8_u _ _ t (48 * i + 40) 8 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V40 & Rls).
change (disco_table_c.u_at T (48 * i + 40) 8) with ls in V40, Rls.
replace (t + (48 * i + 40)) with (e + 40) in V40 by (unfold e; glia).
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Rls.
assert (Rage : 0 <= age < 2 ^ 64) by (unfold age, age_of; destruct (ls <? now) eqn:X; [apply Z.ltb_lt in X; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; glia | glia]).
unfold w64 in E721, E722, E733.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 0 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 906 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; rewrite unsigned_lit_small by (unfold e; glia);
split; [unfold e; glia|]; split; [unfold e; glia|]; split; [intros o Ho; glia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 40 8 _ ls); [cbn [sv_denot]; rewrite E906, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V40]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740; rewrite unsigned_lit_small by (unfold e; glia); evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg Htlo Hthi HTsep Hi HT1;
unfold e, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
tjm_fact HS 740%nat (mkAF 4096 140737479966720 3) ltac:(rewrite E740, unsigned_lit_small by (unfold e; glia); change (2 ^ 3) with 8; unfold e; glia).
tjm_fact HS 721%nat (mkAF 0 336 4) ltac:(rewrite E721, unsigned_lit_small by glia; change (2 ^ 4) with 16; glia).
tjm_fact HS 733%nat (mkAF 0 2147483647 0) ltac:(rewrite E733, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
norm_ss HS.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (SH740 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 740 0 48));
[ apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) Ev (SOff 32 0) 740 t 400 e 0 48 HraT);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by glia; exact HE032 | unfold SB; glia]); reflexivity
| apply U_atom; [rewrite E740; reflexivity | unfold e; glia]
| unfold e; glia | unfold e; glia
| intros x Hx; clear - Hx HTapp Htlo Hthi Hi HT1; unfold e, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; cbn [Z.min Z.max] in Hx; lia ] | ];
assert (SH516 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 516 256 0));
[ apply (shent_app_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 Ev (SOff 32 0) 516 F 2 fpos 0 256 _ HAR3 Hfin);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by glia; exact HE032 | unfold SB; glia]); reflexivity
| apply U_atom; [rewrite E516; reflexivity | glia]
| rewrite EFA0; fold F; glia | glia | rewrite EFA0; fold F; change (fs_frame_bytes 2) with 256; glia ] | ];
shok_auto_with SHOK (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) [mkSHE 740 0 48]
ltac:(first [exact SH740 | exact SH516]) end.
clear SH740 SH516.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
assert (Q10 : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat) by glia; rewrite (HE0 10%nat 10%bv eq_refl); exact H10) end.
rewrite branch_ltu_U, (tjm_U_not _ 10 t Q10 ltac:(glia)), (U_atom _ 721 (48 * i) E721 ltac:(glia)) in Hc.
apply Z.ltb_lt in Hc. glia. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 23728. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Q10 : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat) by glia; rewrite (HE0 10%nat 10%bv eq_refl); exact H10) end.
rrw HS (23%bv : bv 5) (SOff 740 0)
ltac:(idtac; rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 10 t Q10), (U_atom _ 721 (48 * i) E721), (U_atom _ 740 e E740) by (unfold e; glia);
unfold e; rewrite zcanon_id by (unfold M64; glia); glia).
clear Q10.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Q11 : ew Ev 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat) by glia; rewrite (HE0 11%nat 11%bv eq_refl); exact H11) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_geu_U, (U_atom _ 906 ls E906 Rls), (U_atom _ 11 now Q11 Hnow) in Hc0.
apply negb_true_iff, Z.ltb_ge in Hc0.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 23788. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
rechunk_off HS 60%nat 144 (SOff 741 0) ltac:(rewrite !(denot_lit_U _); f_equal; rewrite (U_atom _ 741 age E741 Rage), U_lit by glia;
unfold age, age_of; destruct (Z.ltb_spec ls now); glia).
ra_join HS ss_tjMa 920%nat ([10; 11]%bv : list (bv 5)) idtac.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FMa (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wg msF mdF) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ.
+ exact HFR.
+ unfold INV_tjMa, tj_lbody; cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [glia|]. split.
{ split; [exact Hperm|]. split; [eapply tjm_keep_journal; [exact HBASE | exact HJ]|].
split; [glia|]. split; [glia|]. split; [assumption|]. split; [assumption|]. split; assumption. }
exists acc. split; [assumption|]. split; [glia|]. split; [exact Htxt|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) _ buf (acc ++ [0])); [|exact Hgarr].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HKB. glia.
+ exact HS.
- rewrite branch_geu_U, (U_atom _ 906 ls E906 Rls), (U_atom _ 11 now Q11 Hnow) in Hc0.
apply negb_false_iff, Z.ltb_lt in Hc0.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 23788. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Q11' : ew Ev 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat) by glia; rewrite (HE0 11%nat 11%bv eq_refl); exact H11) end.
rechunk_off HS 60%nat 144 (SOff 741 0) ltac:(rewrite !(denot_lit_U _); f_equal; rewrite (U_atom _ 741 age E741 Rage);
rewrite (tjm_age_U _ 11 906 now ls Q11' E906 ltac:(glia) ltac:(glia)); unfold age, age_of; rewrite (proj2 (Z.ltb_lt ls now) Hc0); reflexivity).
ra_join HS ss_tjMa 920%nat ([10; 11]%bv : list (bv 5)) idtac.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FMa (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wg msF mdF) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ.
+ exact HFR.
+ unfold INV_tjMa, tj_lbody; cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [glia|]. split.
{ split; [exact Hperm|]. split; [eapply tjm_keep_journal; [exact HBASE | exact HJ]|].
split; [glia|]. split; [glia|]. split; [assumption|]. split; [assumption|]. split; assumption. }
exists acc. split; [assumption|]. split; [glia|]. split; [exact Htxt|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) _ buf (acc ++ [0])); [|exact Hgarr].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HKB. glia.
+ exact HS.
Qed.
Lemma tjm_seg2 : forall i, tjm_fromMb i -> tjm_fromMa i.
Proof.
intros i FMb. unfold tjm_fromMa, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
unfold INV_tjMa, tj_lbody in HINV.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0; pose proof HEX as HX0; unfold tj_baseX in HB0; unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
destruct HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG 33%nat) by glia; exact HE033).
assert (AG3 : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG; glia).
clear AG; rename AG3 into AG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity; assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; glia).
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBOK; pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia); clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS); pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS); pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *; set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(glia)) as Hob241; pose proof (pa_obj_img 1 ltac:(glia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(glia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar; pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres; fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh; fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img; rewrite EFA in HFhigh_img; fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(glia)); glia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by glia; rewrite Z.div_mul by glia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; glia).
assert (HF8hi : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; glia).
assert (HEsp0 : ew E0 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- HE02; symmetry; apply Z_to_bv_bv_unsigned).
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & acc & E733 & Hacc & Htxt & Hgarr).
pose proof Hok as (HT1 & HT2 & HT3 & HT4); unfold disco_table_c.tbl_T1 in HT1.
assert (Hi8 : 0 <= i < 8) by glia.
unfold tj_keep in HKEEP; cbn [c_ly c_S c_t c_T] in HKEEP.
destruct HKEEP as (HROD3 & HgT & HobjT).
destruct HobjT as ((cid & pos & Hcin & Hcid & Hcal & Htlo & Hthi) & Ht8 & HraT).
assert (Hcin3 : In (cid, pos) (frames S3)) by (rewrite HFR; right; exact Hcin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hcin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hcin3) as HTimg; rewrite EFA in HTimg.
destruct (in_split _ _ Hcin) as (l2 & l3 & Hl23).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cid, pos) [] l2 l3 HAR3 ltac:(rewrite HFR, Hl23; reflexivity)) as HTsep.
unfold frame_rng, zdisjoint in HTsep; cbn [fst snd] in HTsep; rewrite !EFA in HTsep; fold F in HTsep; change (fs_frame_bytes 2) with 256 in HTsep.
set (TF := frame_addr ly cid pos) in *.
pose proof ASAN_CEIL_range as HAC.
assert (Ht : 4096 <= t /\ t + 400 <= 140737479966720) by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; glia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & HNbr).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep; fold F in Hbsep; change (fs_frame_bytes 2) with 256 in Hbsep; unfold zdisjoint in Hbsep; cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp; unfold off_img, IMG_LO, IMG_TOP in Hbimg.
pose proof (conj Hb4096 (conj Hbceil (conj Hbapp (conj Hbimg (conj Hbsep (conj Hcapb (conj HF4096 (conj HFceil (conj HFhigh (conj HFhigh_img (conj HF8lo (conj HF8hi (conj HFq (conj HF8 (conj HT4096 (conj HTceil (conj HTapp (conj HTimg (conj HTsep (conj Htlo (conj Hthi (conj Ht (conj HAC (conj Hsp1 (conj Hceil (conj Hslo (conj Hstk0 (conj Hshi (conj H47 (conj Hbot (conj Htop (conj Htop2 (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj HSK (conj HSNP (conj Hes (conj Hob241 (conj Hob242 (conj Hob253 (conj Huar (conj Hi8 (conj Hcap (conj Hcap3 (conj Hacc (conj HlenT Hk0))))))))))))))))))))))))))))))))))))))))))))))))) as HGB. box HGB.
assert (HKB : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
set (e := t + 48 * i) in *. set (ls := disco_table_c.last_of T i) in *. set (age := age_of now ls) in *.
unfold w64 in E721, E722, E740, E741, E733.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (SH516 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 516 256 0));
[ apply (shent_app_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 Ev (SOff 32 0) 516 F 2 fpos 0 256 _ HAR3 Hfin);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by glia; exact HE032 | unfold SB; glia]); reflexivity
| apply U_atom; [rewrite E516; reflexivity | glia]
| rewrite EFA0; fold F; glia | glia | rewrite EFA0; fold F; change (fs_frame_bytes 2) with 256; glia ] | ];
shok_auto_with SHOK (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (@nil shent)
ltac:(exact SH516) end.
clear SH516.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Qbuf : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by glia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
rewrite (U_atom _ 12 buf Qbuf ltac:(glia)), (U_atom _ 733 (Z.of_nat (length acc)) E733 ltac:(glia)) in Hc.
rewrite zcanon_id in Hc by (unfold M64; glia). apply Z.ltb_lt in Hc. glia. }
clear Qbuf Hc.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_eq_U, (U_atom _ 721 (48 * i) E721 ltac:(glia)), U_lit in Hc by glia.
apply Z.eqb_eq in Hc. assert (Hi0 : i = 0) by glia.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 23824. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
assert (E282 : ew Ev (A_OBJ 41) = Z_to_bv 64 (VAL (A_OBJ 41))) by (apply img_env_atomP; [assumption | unfold A_OBJ, A_TEXT, A_LIM; glia]);
prreg HS (13%bv : bv 5) R13;
assert (R13' : getr (ms_regs msx) 13%bv = w64 (tjm_sepp i)) by
(rewrite R13; change (A_OBJ 41) with 282%nat in E282; rewrite E282; unfold w64, tjm_sepp; rewrite (proj2 (Z.eqb_eq i 0) Hi0); reflexivity) end.
ra_join HS ss_tjMb 960%nat ([13]%bv : list (bv 5)) idtac.
ra_join_val HS 960%nat 0%nat R13' E960.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FMb (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wg msF mdF) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ.
+ exact HFR.
+ unfold INV_tjMb, tj_lbody; cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [glia|]. split.
{ split; [exact Hperm|]. split; [eapply tjm_keep_journal; [exact HBASE | exact HJ]|].
split; [glia|]. split; [glia|]. split; [assumption|]. split; [assumption|]. split; assumption. }
split; [exact E960|].
exists acc. split; [assumption|]. split; [glia|]. split; [exact Htxt|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) _ buf (acc ++ [0])); [|exact Hgarr].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HKB. glia.
+ exact HS.
- rewrite branch_eq_U, (U_atom _ 721 (48 * i) E721 ltac:(glia)), U_lit in Hc by glia.
apply Z.eqb_neq in Hc. assert (Hine : i <> 0) by glia_with Hc.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 23824. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
assert (E281 : ew Ev (A_OBJ 40) = Z_to_bv 64 (VAL (A_OBJ 40))) by (apply img_env_atomP; [assumption | unfold A_OBJ, A_TEXT, A_LIM; glia]);
prreg HS (13%bv : bv 5) R13;
assert (R13' : getr (ms_regs msx) 13%bv = w64 (tjm_sepp i)) by
(rewrite R13; change (A_OBJ 40) with 281%nat in E281; rewrite E281; unfold w64, tjm_sepp; rewrite (proj2 (Z.eqb_neq i 0) Hine); reflexivity) end.
ra_join HS ss_tjMb 960%nat ([13]%bv : list (bv 5)) idtac.
ra_join_val HS 960%nat 0%nat R13' E960.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FMb (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wg msF mdF) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ.
+ exact HFR.
+ unfold INV_tjMb, tj_lbody; cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [glia|]. split.
{ split; [exact Hperm|]. split; [eapply tjm_keep_journal; [exact HBASE | exact HJ]|].
split; [glia|]. split; [glia|]. split; [assumption|]. split; [assumption|]. split; assumption. }
split; [exact E960|].
exists acc. split; [assumption|]. split; [glia|]. split; [exact Htxt|].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) _ buf (acc ++ [0])); [|exact Hgarr].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HKB. glia.
+ exact HS.
Qed.
Lemma tjm_seg3 : forall i, tj_fromX B IMG -> tj_fromM B IMG i -> tjm_fromMb i.
Proof.
intros i FX FM. unfold tjm_fromMb, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
unfold INV_tjMb, tj_lbody in HINV.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0; pose proof HEX as HX0; unfold tj_baseX in HB0; unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
destruct HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG 33%nat) by glia; exact HE033).
assert (AG3 : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG; glia).
clear AG; rename AG3 into AG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity; assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; glia).
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBOK; pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia); clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS); pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS); pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *; set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(glia)) as Hob241; pose proof (pa_obj_img 1 ltac:(glia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(glia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar; pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres; fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh; fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img; rewrite EFA in HFhigh_img; fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(glia)); glia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by glia; rewrite Z.div_mul by glia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; glia).
assert (HF8hi : F / 8 <= 17592184995808) by (apply Z.div_le_upper_bound; glia).
assert (HEsp0 : ew E0 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- HE02; symmetry; apply Z_to_bv_bv_unsigned).
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E740 & E741) & E960 & acc & E733 & Hacc & Htxt & Hgarr).
pose proof Hok as (HT1 & HT2 & HT3 & HT4); unfold disco_table_c.tbl_T1 in HT1.
assert (Hi8 : 0 <= i < 8) by glia.
unfold tj_keep in HKEEP; cbn [c_ly c_S c_t c_T] in HKEEP.
destruct HKEEP as (HROD3 & HgT & HobjT).
destruct HobjT as ((cid & pos & Hcin & Hcid & Hcal & Htlo & Hthi) & Ht8 & HraT).
assert (Hcin3 : In (cid, pos) (frames S3)) by (rewrite HFR; right; exact Hcin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR3 Hcin3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hcin3) as HTimg; rewrite EFA in HTimg.
destruct (in_split _ _ Hcin) as (l2 & l3 & Hl23).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cid, pos) [] l2 l3 HAR3 ltac:(rewrite HFR, Hl23; reflexivity)) as HTsep.
unfold frame_rng, zdisjoint in HTsep; cbn [fst snd] in HTsep; rewrite !EFA in HTsep; fold F in HTsep; change (fs_frame_bytes 2) with 256 in HTsep.
set (TF := frame_addr ly cid pos) in *.
pose proof ASAN_CEIL_range as HAC.
assert (Ht : 4096 <= t /\ t + 400 <= 140737479966720) by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; glia).
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & HNbr).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep; fold F in Hbsep; change (fs_frame_bytes 2) with 256 in Hbsep; unfold zdisjoint in Hbsep; cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp; unfold off_img, IMG_LO, IMG_TOP in Hbimg.
pose proof (conj Hb4096 (conj Hbceil (conj Hbapp (conj Hbimg (conj Hbsep (conj Hcapb (conj HF4096 (conj HFceil (conj HFhigh (conj HFhigh_img (conj HF8lo (conj HF8hi (conj HFq (conj HF8 (conj HT4096 (conj HTceil (conj HTapp (conj HTimg (conj HTsep (conj Htlo (conj Hthi (conj Ht (conj HAC (conj Hsp1 (conj Hceil (conj Hslo (conj Hstk0 (conj Hshi (conj H47 (conj Hbot (conj Htop (conj Htop2 (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj HSK (conj HSNP (conj Hes (conj Hob241 (conj Hob242 (conj Hob253 (conj Huar (conj Hi8 (conj Hcap (conj Hcap3 (conj Hacc (conj HlenT Hk0))))))))))))))))))))))))))))))))))))))))))))))))) as HGB. box HGB.
assert (HKB : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
set (e := t + 48 * i) in *.
set (m0 := disco_table_c.u_at T (48 * i + 0) 1). set (m1 := disco_table_c.u_at T (48 * i + 1) 1).
set (m2 := disco_table_c.u_at T (48 * i + 2) 1). set (m3 := disco_table_c.u_at T (48 * i + 3) 1).
set (m4 := disco_table_c.u_at T (48 * i + 4) 1). set (m5 := disco_table_c.u_at T (48 * i + 5) 1).
unfold w64 in E721, E722, E740, E741, E733, E960.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 900 Ev ssv msv [Z_to_bv 64 m0; Z_to_bv 64 m1; Z_to_bv 64 m2; Z_to_bv 64 m3; Z_to_bv 64 m4; Z_to_bv 64 m5] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 900%nat [Z_to_bv 64 m0; Z_to_bv 64 m1; Z_to_bv 64 m2; Z_to_bv 64 m3; Z_to_bv 64 m4; Z_to_bv 64 m5] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => lazymatch type of HEv with _ = havoc _ _ ?ws =>
assert (E900 : ew Ev 900 = Z_to_bv 64 m0) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 0 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E901 : ew Ev 901 = Z_to_bv 64 m1) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 1 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E902 : ew Ev 902 = Z_to_bv 64 m2) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 2 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E903 : ew Ev 903 = Z_to_bv 64 m3) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 3 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E904 : ew Ev 904 = Z_to_bv 64 m4) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 4 (Z_to_bv 64 0) ltac:(cbn; glia)));
assert (E905 : ew Ev 905 = Z_to_bv 64 m5) by (rewrite HEv; exact (ew_havoc_new _ 900 ws 5 (Z_to_bv 64 0) ltac:(cbn; glia))) end end.
clear HEv.
destruct (tjm_garr8_u _ _ t (48 * i + 0) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V0 & Rm0).
destruct (tjm_garr8_u _ _ t (48 * i + 1) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V1 & Rm1).
destruct (tjm_garr8_u _ _ t (48 * i + 2) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V2 & Rm2).
destruct (tjm_garr8_u _ _ t (48 * i + 3) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V3 & Rm3).
destruct (tjm_garr8_u _ _ t (48 * i + 4) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V4 & Rm4).
destruct (tjm_garr8_u _ _ t (48 * i + 5) 1 T HgT ltac:(glia) ltac:(rewrite HlenT; glia)) as (V5 & Rm5).
fold m0 m1 m2 m3 m4 m5 in V0, V1, V2, V3, V4, V5, Rm0, Rm1, Rm2, Rm3, Rm4, Rm5.
replace (t + (48 * i + 0)) with (e + 0) in V0 by (unfold e; glia).
replace (t + (48 * i + 1)) with (e + 1) in V1 by (unfold e; glia).
replace (t + (48 * i + 2)) with (e + 2) in V2 by (unfold e; glia).
replace (t + (48 * i + 3)) with (e + 3) in V3 by (unfold e; glia).
replace (t + (48 * i + 4)) with (e + 4) in V4 by (unfold e; glia).
replace (t + (48 * i + 5)) with (e + 5) in V5 by (unfold e; glia).
change (2 ^ (8 * Z.of_nat 1)) with 256 in Rm0, Rm1, Rm2, Rm3, Rm4, Rm5.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 0 48 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 900 0)); YP09.mkChunk 1 (CVal 1 (SOff 901 0)); YP09.mkChunk 2 (CVal 1 (SOff 902 0)); YP09.mkChunk 3 (CVal 1 (SOff 903 0)); YP09.mkChunk 4 (CVal 1 (SOff 904 0)); YP09.mkChunk 5 (CVal 1 (SOff 905 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; rewrite unsigned_lit_small by (unfold e; glia);
split; [unfold e; glia|]; split; [unfold e; glia|]; split; [intros o Ho; glia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 0 1 _ m0); [cbn [sv_denot]; rewrite E900, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 1 1 _ m1); [cbn [sv_denot]; rewrite E901, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V1]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 2 1 _ m2); [cbn [sv_denot]; rewrite E902, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V2]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 3 1 _ m3); [cbn [sv_denot]; rewrite E903, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V3]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 4 1 _ m4); [cbn [sv_denot]; rewrite E904, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V4]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ e 5 1 _ m5); [cbn [sv_denot]; rewrite E905, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; glia | cbn; glia | exact V5]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740; rewrite unsigned_lit_small by (unfold e; glia); evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg Htlo Hthi HTsep Hi HT1;
unfold e, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 HSK C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres3; clear - Ho Hsp1 HSK; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E740; rewrite ?unsigned_lit_small by (unfold e; glia); evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi Hob241 Hob242 Hob253 Huar
HT4096 HTceil HTapp HTimg Htlo Hthi Hi HT1;
unfold e, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, SB in *; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
tjm_fact HS 900%nat (mkAF 0 255 0) ltac:(rewrite E900, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
tjm_fact HS 901%nat (mkAF 0 255 0) ltac:(rewrite E901, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
tjm_fact HS 902%nat (mkAF 0 255 0) ltac:(rewrite E902, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
tjm_fact HS 903%nat (mkAF 0 255 0) ltac:(rewrite E903, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
tjm_fact HS 904%nat (mkAF 0 255 0) ltac:(rewrite E904, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
tjm_fact HS 905%nat (mkAF 0 255 0) ltac:(rewrite E905, unsigned_lit_small by glia; rewrite Z.pow_0_r, Z.mod_1_r; glia).
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (SH740 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 740 0 48));
[ apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) Ev (SOff 32 0) 740 t 400 e 0 48 HraT);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by glia; exact HE032 | unfold SB; glia]); reflexivity
| apply U_atom; [rewrite E740; reflexivity | unfold e; glia]
| unfold e; glia | unfold e; glia
| intros x Hx; clear - Hx HTapp Htlo Hthi Hi HT1; unfold e, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg in *; cbn [Z.min Z.max] in Hx; lia ] | ];
assert (SH516 : shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE 516 256 0));
[ apply (shent_app_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 Ev (SOff 32 0) 516 F 2 fpos 0 256 _ HAR3 Hfin);
[ rewrite (U_atom Ev 32 SB) by (first [rewrite (AG 32%nat) by glia; exact HE032 | unfold SB; glia]); reflexivity
| apply U_atom; [rewrite E516; reflexivity | glia]
| rewrite EFA0; fold F; glia | glia | rewrite EFA0; fold F; change (fs_frame_bytes 2) with 256; glia ] | ];
shok_auto_with SHOK (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem ms3)) [mkSHE 740 0 48]
ltac:(first [exact SH740 | exact SH516]) end.
clear SH740 SH516.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kb AG HKB buf cap W3 ms3 HFr. rebase HS AG.
set (L := Z.of_nat (length acc)) in *.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Q12 : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by glia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12);
assert (Q13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (E283 : ew Ev (A_OBJ 42) = Z_to_bv 64 (VAL (A_OBJ 42))) by (apply img_env_atomP; [assumption | unfold A_OBJ, A_TEXT, A_LIM; glia]) end.
rregU HS (10%bv : bv 5) (buf + L) ltac:(idtac; rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 12 buf Q12), (U_atom _ 733 L E733) by glia; apply zcanon_id; unfold M64; glia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(idtac; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom _ 13 cap Q13), (U_atom _ 733 L E733), U_SLit by glia; apply tjm_csub; [reflexivity | glia | glia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4. prreg HS (15%bv : bv 5) Qa5.
prreg HS (16%bv : bv 5) Qa6. prreg HS (17%bv : bv 5) Qa7.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
pose proof (st_ok_region_nth Ev ssx (restrict (w_H W3) msx) 0 (YP09.mkRegion (Some 60%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 905 0)); YP09.mkChunk (-16) (CVal 8 (SOff 904 0))]) HS eq_refl) as HR60 end.
cbn [ms_mem restrict] in HR60.
assert (WD4 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (sp1 - 16) = Some m4).
{ apply rdword_of_val_mem; [|glia].
replace (sp1 - 16) with (sp1 + -16) by glia.
exact (field_of_region _ _ 60%nat sp1 _ (-16) 0 (-16) 0 (-16) 8%N (SOff 904 0) m4 HR60
ltac:(rewrite E60; apply unsigned_lit_small; glia) ltac:(right; left; reflexivity)
ltac:(cbn [sv_denot]; rewrite E904, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; glia) ltac:(cbn; glia)). }
assert (WD5 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (sp1 - 8) = Some m5).
{ apply rdword_of_val_mem; [|glia].
replace (sp1 - 8) with (sp1 + -8) by glia.
exact (field_of_region _ _ 60%nat sp1 _ (-16) 0 (-16) 0 (-8) 8%N (SOff 905 0) m5 HR60
ltac:(rewrite E60; apply unsigned_lit_small; glia) ltac:(left; reflexivity)
ltac:(cbn [sv_denot]; rewrite E905, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; glia) ltac:(cbn; glia)). }
clear HR60.
pmkst HS. rewrite HSNPC.
set (seps := if i =? 0 then tj_s_empty else tj_s_comma).
set (TT := seps ++ [123; 34; 109; 97; 99; 34; 58; 34] ++ pf_hex2 m0 ++ [58] ++ pf_hex2 m1 ++ [58] ++ pf_hex2 m2 ++ [58] ++ pf_hex2 m3 ++ [58] ++ pf_hex2 m4 ++ [58] ++ pf_hex2 m5 ++ [34]).
pose proof (proj1 HJ) as HARc.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
gadd (conj Hgc1 (conj Hgc2 (conj Hgv1 Hgv2))).
pose proof TJS as (_ & _ & Hfm & _ & _ & _ & _ & _ & _ & _ & Hcm & Hem & _).
assert (PSP : IMG_TOP + 8 <= (spZ regs + (sp1 - 16 - spZ regs)) - SNPRINTF_STK) by (unfold IMG_TOP; rewrite HSNP; clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia).
assert (PDN : buf + L + (cap - L) <= IMG_LO \/ IMG_TOP <= buf + L) by (unfold IMG_LO, IMG_TOP; glia).
assert (A3 : argZ (ms_regs ms) 3 = tjm_sepp i).
{ unfold argZ. lazymatch type of Qa3 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 3)) with r by (apply bv_eq; vm_compute; reflexivity) end.
rewrite Qa3, E960. apply unsigned_lit_small. unfold tjm_sepp. pose proof (pa_val_range (A_OBJ 41)). pose proof (pa_val_range (A_OBJ 40)). destruct (i =? 0); glia. }
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq)
W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k
(buf + L) (cap - L) (VAL (A_OBJ 42)) tj_f_mac
[Ps; PLit 123; PLit 34; PLit 109; PLit 97; PLit 99; PLit 34; PLit 58; PLit 34; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 34]
[m4; m5] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ [m4; m5])
[APtr seps; AInt m0; AInt m1; AInt m2; AInt m3; AInt m4; AInt m5] TT cval (sp1 - 16 - spZ regs) (Z_to_bv 64 (BASE + 23996)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60. rewrite (unsigned_lit_small sp1) by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia). rewrite (unsigned_lit_small (sp1 + -16)) by (clear - Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47; lia). glia. }
{ glia. }
{ glia. }
{ unfold REAC_DISCO_TABLE_JSON_STK. glia. }
{ rewrite Qgp, (AG 3%nat) by glia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp, (AG 4%nat) by glia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [glia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2. exact E283. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. clear - Hr; lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia_with Hr). }
{ exact HG1. }
{ exact HG2. }
{ glia. }
{ glia. }
{ glia. }
{ glia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ exact (proj2 (tjm_str 42 tj_f_mac _ _ _ _ _ (spZ regs + (sp1 - 16 - spZ regs)) (buf + L) (cap - L) HARc HRODc Hfm PSP PDN)). }
{ exact (tj_ro_fmt_rng 42 tj_f_mac Hfm ltac:(cbv; glia)). }
{ unfold tj_f_mac. discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity|].
replace (spZ regs + (sp1 - 16 - spZ regs)) with (sp1 - 16) by glia.
intros j Hj. cbn [length] in Hj.
destruct j as [|[|j]]; [| |glia].
+ cbn [nth]. replace (sp1 - 16 + 8 * Z.of_nat 0) with (sp1 - 16) by glia. exact WD4.
+ cbn [nth]. replace (sp1 - 16 + 8 * Z.of_nat 1) with (sp1 - 8) by glia. exact WD5. }
{ cbn [length Z.of_nat]. glia. }
{ unfold snp_out. cbn [length Z.of_nat]. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; glia). }
{ cbn [map app pf_args_asan].
assert (A4 : argZ (ms_regs ms) 4 = m0) by (unfold argZ; lazymatch type of Qa4 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 4)) with r by (apply bv_eq; vm_compute; reflexivity) end; rewrite Qa4, E900; apply unsigned_lit_small; glia).
assert (A5 : argZ (ms_regs ms) 5 = m1) by (unfold argZ; lazymatch type of Qa5 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 5)) with r by (apply bv_eq; vm_compute; reflexivity) end; rewrite Qa5, E901; apply unsigned_lit_small; glia).
assert (A6 : argZ (ms_regs ms) 6 = m2) by (unfold argZ; lazymatch type of Qa6 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 6)) with r by (apply bv_eq; vm_compute; reflexivity) end; rewrite Qa6, E902; apply unsigned_lit_small; glia).
assert (A7 : argZ (ms_regs ms) 7 = m3) by (unfold argZ; lazymatch type of Qa7 with getr _ ?r = _ => replace (Z_to_bv 5 (10 + 7)) with r by (apply bv_eq; vm_compute; reflexivity) end; rewrite Qa7, E903; apply unsigned_lit_small; glia).
rewrite A3, A4, A5, A6, A7.
split.
{ destruct (Z.eq_dec i 0) as [Hi0|Hi0].
- unfold seps, tjm_sepp. rewrite (proj2 (Z.eqb_eq i 0) Hi0).
exact (proj1 (tjm_str 41 tj_s_empty _ _ _ _ _ (spZ regs + (sp1 - 16 - spZ regs)) (buf + L) (cap - L) HARc HRODc Hem PSP PDN)).
- unfold seps, tjm_sepp. rewrite (proj2 (Z.eqb_neq i 0) Hi0).
exact (proj1 (tjm_str 40 tj_s_comma _ _ _ _ _ (spZ regs + (sp1 - 16 - spZ regs)) (buf + L) (cap - L) HARc HRODc Hcm PSP PDN)). }
split; [split; [glia | reflexivity]|].
split; [split; [glia | reflexivity]|].
split; [split; [glia | reflexivity]|].
split; [split; [glia | reflexivity]|].
split; [split; [glia | reflexivity]|].
split; [split; [glia | reflexivity]|].
exact I. }
{ cbn [map app SnFF.pf_args_amem]. rewrite A3. split; [|exact I]. unfold seps, tjm_sepp.
destruct (i =? 0); [exact (tj_ro_amem8 41 tj_s_empty Hem) | exact (tj_ro_amem8 40 tj_s_comma Hcm)]. }
{ reflexivity. }
{ glia. }
{ unfold TT.
rewrite (tjm_hex2 m0) by glia. rewrite (tjm_hex2 m1) by glia.
rewrite (tjm_hex2 m2) by glia. rewrite (tjm_hex2 m3) by glia.
rewrite (tjm_hex2 m4) by glia. rewrite (tjm_hex2 m5) by glia.
unfold hex2. rewrite !length_app. cbn [length]. unfold seps. destruct (i =? 0); cbn [length tj_s_empty tj_s_comma]; glia. }
{ glia. }
{ glia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; glia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|glia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; glia].
+ exists buf, Nb. split; [exact Hinb | glia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); glia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | glia | glia]. }
{ exact Hfrm. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - 16 - spZ regs)) with (sp1 - 16) in Hfr by glia. rewrite HSNP in Hfr.
assert (HTP : TT = P1 (Z.to_nat i) (reac_disco_table_json_c.tj_entry T i)).
{ rewrite (tjm_P1_eq T HlenT i ltac:(glia)).
unfold TT, seps. rewrite !tjm_hex2 by glia.
destruct (Z.eq_dec i 0) as [Hi0|Hi0].
- rewrite (proj2 (Z.eqb_eq i 0) Hi0). replace (Nat.eqb (Z.to_nat i) 0) with true by (rewrite Hi0; reflexivity). reflexivity.
- rewrite (proj2 (Z.eqb_neq i 0) Hi0). replace (Nat.eqb (Z.to_nat i) 0) with false by (symmetry; apply Nat.eqb_neq; glia_with Hi0). reflexivity. }
assert (HTL : Z.of_nat (length TT) <= 27).
{ unfold TT, seps. rewrite !tjm_hex2 by glia. unfold hex2. rewrite !length_app. cbn [length].
destruct (i =? 0); cbn [length tj_s_empty tj_s_comma]; glia. }
clearbody TT seps.
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM (SOff 32 0) [] ss) end in
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W3) mem2) HP2 [2; 3; 4; 5; 6; 7; 8; 9]%nat HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr;
clear - Ha HTL Hsp1 Hceil Hslo Hstk0 HSK C1 C3 Hshi H47 Hbapp Hbceil Hcapb Hacc Hb4096 Hbsep Hbimg HF4096 HFceil HF8lo HF8hi HFhigh_img Hob241 Hob242 Hob253 Huar HAC;
unfold SB, in_app, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, ASAN_CEIL in *; lia | exact Hpres2])
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx') B LAWS); pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS); pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
rebase HS AG.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
assert (HtxtP : reac_disco_table_json_c.tj_text T now =
(acc ++ TT) ++ tj_after1 (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
{ rewrite Htxt, (tj_lemmas.tj_rest_step T now i) by glia.
unfold obj_text, tj_after1, tj_after2, tj_after4, tj_e. cbn [c_T c_now]. rewrite HTP. rewrite <- !app_assoc. reflexivity. }
assert (Hlen : L + Z.of_nat (length TT) <= tj_len T now).
{ unfold tj_len. rewrite HtxtP, !length_app, !Nat2Z.inj_add. unfold L. glia. }
lazymatch type of Qr0 with ew ?Ev ?na = _ =>
assert (G13 : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by glia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 733 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap G13), (U_atom Ev 733 L E733) by glia;
rewrite U_SLit; apply tjm_csub; [reflexivity | glia | glia]);
assert (U0 : U Ev (SOff na 0) = Z.of_nat (length TT)) by (apply U_atom; [exact Qr0 | glia]) end.
assert (HKB2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem2 a) by (intros; reflexivity).
paj_run_to_shc RUNTOP HS HJ2 24000. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kbm AG HKB2 buf cap W3 mem2 HFr.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of U0 with U _ ?x = _ => lazymatch type of Hc with branch_taken BC_LT (sv_denot ?Eb _) _ = _ =>
exact (tjm_bltz_false Eb x (Z.of_nat (length TT)) U0 ltac:(glia) Hc) end end. }
clear Hc.
paj_run_to_shc RUNTOP HS HJ2 24004. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kbm AG HKB2 buf cap W3 mem2 HFr.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 25204. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kbm AG HKB2 buf cap W3 mem2 HFr.
pose proof (proj1 HJ2) as HARx.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite EFA0 in HFSx. fold F in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
tjm_rw529 HS E529 HFSx.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
prreg HS (23%bv : bv 5) R23;
assert (R23' : getr (ms_regs msx) 23%bv = w64 (-1)) by (rewrite R23; first [reflexivity | apply bv_eq; vm_compute; reflexivity]) end.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23' E653.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ2.
+ exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
split; [glia|]. split; [exact Hperm|]. exists (-1). split; [exact E653|].
split; [intros _; reflexivity|]. split; [intros _ Hlt'; exfalso; glia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 24008. { tjm_awr ltac:(idtac; tjm_hd AG HSK) AG fpos F EFA0. }
tjm_kbm AG HKB2 buf cap W3 mem2 HFr.
pose proof (proj1 HJ2) as HARx.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite EFA0 in HFSx. fold F in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
tjm_rw529 HS E529 HFSx.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
prreg HS (10%bv : bv 5) R10;
assert (R10' : getr (ms_regs msx) 10%bv = w64 (Z.of_nat (length TT))) by (rewrite R10; exact Qr0) end.
ra_join HS ss_tjM 760%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 760%nat 4%nat R10' E764.
hei_havoc HS. rebase HS AG.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FM (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+
unfold tj_EX, tj_F, tj_FL; cbn [c_ly c_fpos c_E0 c_sp1]; fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; clear - Hn Hn33; lia]|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption | assumption].
+ exact HJ2.
+ exact HFR.
+ unfold INV_tjM, tj_lbody, tj_split, tj_wrote. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [glia|]. split.
{ split; [exact Hperm|]. split; [exact (tjm_keep_journal (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ2)|].
split; [glia|]. split; [glia|]. split; [assumption|]. split; [assumption|]. split; assumption. }
exists (acc ++ TT). split.
{ exists L, (Z.of_nat (length TT)). split; [assumption|]. split; [exact E764|]. split; [glia|]. split; [glia|].
rewrite length_app, Nat2Z.inj_add. unfold L. glia. }
split; [rewrite length_app, Nat2Z.inj_add; unfold L in *; glia|].
split; [exact HtxtP|].
rewrite <- app_assoc.
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite !length_app in Ha. cbn [length] in Ha. apply HKB2. unfold L in *. glia. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc).
- intros a Ha. rewrite Hfr by (clear - Ha Hsp1 Hceil Hslo Hstk0 HSK C1 Hshi H47 Hbapp Hbceil Hcapb Hacc Hb4096 HAC; unfold L, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
apply HKB. unfold L in *. glia.
- exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)). }
fold L.
apply tjm_garr.
* intros j Hj. apply Hwr. glia.
* rewrite Z.min_l in Hnul by glia. exact Hnul.
+ exact HS.
Qed.
Theorem pb_tj_mac : tj_seg_mac B IMG.
Proof.
intros i FX FM. exact (tjm_seg1 i (tjm_seg2 i (tjm_seg3 i FX FM))).
Qed.
End h.
End f.
End d.
