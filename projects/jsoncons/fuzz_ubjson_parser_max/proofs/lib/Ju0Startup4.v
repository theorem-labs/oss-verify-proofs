(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: section P now takes a ProcInput record with launch hypotheses, adds rnd_facts_here, and rewrites rnd_w, argc_w, J_aux and D_libc uses over inp as in fuzz_bigint's copy; encoded statements and fin_c6/fin_c7 section blocks become plain lemmas; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Ub0Startup4.v, 163 lines within its lines 15-381. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Ju0Img Ju0StartupDefs.
Import ListNotations.
Open Scope bv_scope.
Local Set Default Proof Using "All".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Section FPX_1. Context {fx : PropExec.FPState}.
Section P.
Variable v : VaSize.
Variable inp : ProcInput.
Variable mbase entry : word.
Variable sp0 brk : word.
Variable rdraw : EntryDraw.
Variable Jb : word -> option byte.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Local Notation uid := (in_uid inp) (only parsing).
Local Notation hw := (in_hwcap inp) (only parsing).
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation RND := (ed_random rdraw) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).
Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.
Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma rnd_facts_here :
(bv_unsigned sp0
<= bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev))%Z
/\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) + 16
<= bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)))%Z
/\ (bv_unsigned sp0 + Z.of_nat (length (entry_stack_image inp mbase RPH entry sp0 rdraw)) < 2^64)%Z
/\ (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) mod 8 = 0)%Z
/\ (forall j n, (j + n <= 16)%nat ->
rdn SEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw))
(Z_to_bv 64 (bv_unsigned (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev)
+ Z.of_nat j)) n
= Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
Proof.
eapply rnd_facts;
first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal].
Qed.
Lemma rnd_bounds :
(bv_unsigned sp0 <= bv_unsigned (rnd_w inp sp0))%Z
/\ (bv_unsigned (rnd_w inp sp0) + 16 < 2^64)%Z
/\ (bv_unsigned (rnd_w inp sp0) mod 8 = 0)%Z.
Proof.
destruct rnd_facts_here as (A & B & C & D & _).
unfold rnd_w. repeat split; lia.
Qed.
Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + Z.of_nat j)) n
= Some (firstn n (skipn j (at_random_bytes (ed_random rdraw)))).
Proof.
intros J D j n Hjn.
destruct rnd_facts_here as (A & B & C & D' & E).
unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.
Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof. intros; subst; reflexivity. Qed.
Ltac RD_RND j :=
eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
| cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].
Ltac RD_GUARD :=
rewrite rdn_cmem_data by region_side;
lazymatch goal with
| |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
let H := fresh in
pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
cbn [Z.add Pos.add Pos.succ] in H; exact H
end.
Lemma slli_argc : v_slli (argc_w inp) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
Proof.
pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN inp Hva).
f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.
Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 822448 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 822448 ->
getr regs' 19 = Z_to_bv 64 0 ->
getr regs' 20 = Z_to_bv 64 0 ->
getr regs' 21 = Z_to_bv 64 0 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
G (mkst regs' (0x992d4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x992cc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x992cc%Z)) (ltac:(oD' 0x992cc%Z)) (word_to_le_bytes 8 (rnd_w inp sp0)) (rnd_w inp sp0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x992d0%Z)) (ltac:(oD' 0x992d0%Z)).
sv (ltac:(oF' 0x99c7c%Z)) (ltac:(oD' 0x99c7c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 432)).
stw (ltac:(oF' 0x99c80%Z)) (ltac:(oD' 0x99c80%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 627412) ltac:(ok_win HJ).
stepb_ft (ltac:(oF' 0x99c84%Z)) (ltac:(oD' 0x99c84%Z)) ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
sv (ltac:(oF' 0x99c88%Z)) (ltac:(oD' 0x99c88%Z)) (rnd_w inp sp0).
sn (ltac:(oF' 0x99c8c%Z)) (ltac:(oD' 0x99c8c%Z)).
ld_step (ltac:(oF' 0x99c90%Z)) (ltac:(oD' 0x99c90%Z)) (word_to_le_bytes 8 (Z_to_bv 64 954144)) (Z_to_bv 64 954144) ltac:(rd_img img_b5f18_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99c94%Z)) (ltac:(oD' 0x99c94%Z)).
sn (ltac:(oF' 0x99c98%Z)) (ltac:(oD' 0x99c98%Z)).
stepiv (ltac:(oF' 0xaa1b4%Z)) (ltac:(oD' 0xaa1b4%Z)) (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
stepb_tk (ltac:(oF' 0xaa1b8%Z)) (ltac:(oD' 0xaa1b8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa2c8%Z)) (ltac:(oD' 0xaa2c8%Z)).
sn (ltac:(oF' 0xaa2cc%Z)) (ltac:(oD' 0xaa2cc%Z)).
stepb_ft (ltac:(oF' 0xaa2d0%Z)) (ltac:(oD' 0xaa2d0%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa2d4%Z)) (ltac:(oD' 0xaa2d4%Z)).
stepb_tk (ltac:(oF' 0xaa2d8%Z)) (ltac:(oD' 0xaa2d8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa310%Z)) (ltac:(oD' 0xaa310%Z)).
stepb_ft (ltac:(oF' 0xaa314%Z)) (ltac:(oD' 0xaa314%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0xaa318%Z)) (ltac:(oD' 0xaa318%Z)) (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
ld_step (ltac:(oF' 0xaa31c%Z)) (ltac:(oD' 0xaa31c%Z)) (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
stw (ltac:(oF' 0xaa320%Z)) (ltac:(oD' 0xaa320%Z)) (Z_to_bv 64 954144) (rlw RND 0) ltac:(ok_data).
stw (ltac:(oF' 0xaa324%Z)) (ltac:(oD' 0xaa324%Z)) (Z_to_bv 64 954148) (rlw RND 4) ltac:(ok_data).
sn (ltac:(oF' 0xaa328%Z)) (ltac:(oD' 0xaa328%Z)).
sv (ltac:(oF' 0xaa32c%Z)) (ltac:(oD' 0xaa32c%Z)) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 8)).
sn (ltac:(oF' 0xaa330%Z)) (ltac:(oD' 0xaa330%Z)).
stepb_tk (ltac:(oF' 0xaa334%Z)) (ltac:(oD' 0xaa334%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa574%Z)) (ltac:(oD' 0xaa574%Z)).
stepb_ft (ltac:(oF' 0xaa578%Z)) (ltac:(oD' 0xaa578%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xaa57c%Z)) (ltac:(oD' 0xaa57c%Z)).
stepb_ft (ltac:(oF' 0xaa580%Z)) (ltac:(oD' 0xaa580%Z)) ltac:(pin; cond_compute).
stepret (ltac:(oF' 0xaa584%Z)) (ltac:(oD' 0xaa584%Z)) (0x99c9c : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99c9c%Z)) (ltac:(oD' 0x99c9c%Z)).
sn (ltac:(oF' 0x99cb8%Z)) (ltac:(oD' 0x99cb8%Z)).
ld_step (ltac:(oF' 0x99cbc%Z)) (ltac:(oD' 0x99cbc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 954144)) (Z_to_bv 64 954144) ltac:(rd_img img_b5f18_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x99cc0%Z)) (ltac:(oD' 0x99cc0%Z)) (Z_to_bv 64 954145) (Z_to_bv 64 0) ltac:(ok_data).
ld_step (ltac:(oF' 0x99cc4%Z)) (ltac:(oD' 0x99cc4%Z)) (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
sn (ltac:(oF' 0x99cc8%Z)) (ltac:(oD' 0x99cc8%Z)).
stw (ltac:(oF' 0x99ccc%Z)) (ltac:(oD' 0x99ccc%Z)) (Z_to_bv 64 822432) (canary_w RND) ltac:(ok_data).
ld_step (ltac:(oF' 0x99cd0%Z)) (ltac:(oD' 0x99cd0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627412)) (Z_to_bv 64 627412) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x99cd4%Z)) (ltac:(oD' 0x99cd4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret (ltac:(oF' 0x99cd8%Z)) (ltac:(oD' 0x99cd8%Z)) (0x992d4 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 822448 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 1 = Z_to_bv 64 0 ->
getr regs' 2 = sp0 ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 822448 ->
getr regs' 8 = Z_to_bv 64 0 ->
getr regs' 9 = Z_to_bv 64 0 ->
getr regs' 10 = Z_to_bv 64 212508 ->
getr regs' 11 = (argc_w inp) ->
getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs' 18 = Z_to_bv 64 0 ->
getr regs' 19 = Z_to_bv 64 0 ->
getr regs' 20 = Z_to_bv 64 0 ->
getr regs' 21 = Z_to_bv 64 0 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
G (mkst regs' (0x99494 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x992d4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x992d4%Z)) (ltac:(oD' 0x992d4%Z)) (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x992d8%Z)) (ltac:(oD' 0x992d8%Z)) (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x992dc%Z)) (ltac:(oD' 0x992dc%Z)) ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step (ltac:(oF' 0x992e0%Z)) (ltac:(oD' 0x992e0%Z)) (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x992e4%Z)) (ltac:(oD' 0x992e4%Z)) (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x992e8%Z)) (ltac:(oD' 0x992e8%Z)) ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step (ltac:(oF' 0x992ec%Z)) (ltac:(oD' 0x992ec%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x992f0%Z)) (ltac:(oD' 0x992f0%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x993d0%Z)) (ltac:(oD' 0x993d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627816)) (Z_to_bv 64 627816) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993d4%Z)) (ltac:(oD' 0x993d4%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993d8%Z)) (ltac:(oD' 0x993d8%Z)) (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x993dc%Z)) (ltac:(oD' 0x993dc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 212508)) (Z_to_bv 64 212508) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x993e0%Z)) (ltac:(oD' 0x993e0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stepret (ltac:(oF' 0x993e4%Z)) (ltac:(oD' 0x993e4%Z)) (0x99468 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99468%Z)) (ltac:(oD' 0x99468%Z)).
sn (ltac:(oF' 0x9946c%Z)) (ltac:(oD' 0x9946c%Z)).
sn (ltac:(oF' 0x99470%Z)) (ltac:(oD' 0x99470%Z)).
sv (ltac:(oF' 0x99474%Z)) (ltac:(oD' 0x99474%Z)) (argc_w inp).
sv (ltac:(oF' 0x99478%Z)) (ltac:(oD' 0x99478%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
ld_step (ltac:(oF' 0x9947c%Z)) (ltac:(oD' 0x9947c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99480%Z)) (ltac:(oD' 0x99480%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99484%Z)) (ltac:(oD' 0x99484%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99488%Z)) (ltac:(oD' 0x99488%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x9948c%Z)) (ltac:(oD' 0x9948c%Z)) sp0.
stepret (ltac:(oF' 0x99490%Z)) (ltac:(oD' 0x99490%Z)) (0x99494 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 0 ->
getr regs 2 = sp0 ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 822448 ->
getr regs 8 = Z_to_bv 64 0 ->
getr regs 9 = Z_to_bv 64 0 ->
getr regs 10 = Z_to_bv 64 212508 ->
getr regs 11 = (argc_w inp) ->
getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs 18 = Z_to_bv 64 0 ->
getr regs 19 = Z_to_bv 64 0 ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 1 = Z_to_bv 64 627736 ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 822448 ->
getr regs' 8 = Z_to_bv 64 721440 ->
getr regs' 9 = Z_to_bv 64 721432 ->
getr regs' 18 = Z_to_bv 64 212508 ->
getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
getr regs' 20 = Z_to_bv 64 0 ->
getr regs' 21 = Z_to_bv 64 0 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
G (mkst regs' (0x33d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 627912))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x99494 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x99494%Z)) (ltac:(oD' 0x99494%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stw (ltac:(oF' 0x99498%Z)) (ltac:(oD' 0x99498%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x9949c%Z)) (ltac:(oD' 0x9949c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a0%Z)) (ltac:(oD' 0x994a0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a4%Z)) (ltac:(oD' 0x994a4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994a8%Z)) (ltac:(oD' 0x994a8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sv (ltac:(oF' 0x994ac%Z)) (ltac:(oD' 0x994ac%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x994b0%Z)) (ltac:(oD' 0x994b0%Z)) (argc_w inp).
sn (ltac:(oF' 0x994b4%Z)) (ltac:(oD' 0x994b4%Z)).
stepiv (ltac:(oF' 0x994b8%Z)) (ltac:(oD' 0x994b8%Z)) (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
sv (ltac:(oF' 0x994bc%Z)) (ltac:(oD' 0x994bc%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
sv (ltac:(oF' 0x994c0%Z)) (ltac:(oD' 0x994c0%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
sn (ltac:(oF' 0x994c4%Z)) (ltac:(oD' 0x994c4%Z)).
sv (ltac:(oF' 0x993e8%Z)) (ltac:(oD' 0x993e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stw (ltac:(oF' 0x993ec%Z)) (ltac:(oD' 0x993ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 627912) ltac:(ok_win HJ).
stw (ltac:(oF' 0x993f0%Z)) (ltac:(oD' 0x993f0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw (ltac:(oF' 0x993f4%Z)) (ltac:(oD' 0x993f4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
sn (ltac:(oF' 0x993f8%Z)) (ltac:(oD' 0x993f8%Z)).
stepret (ltac:(oF' 0x991b8%Z)) (ltac:(oD' 0x991b8%Z)) (0x993fc : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x993fc%Z)) (ltac:(oD' 0x993fc%Z)).
sn (ltac:(oF' 0x99400%Z)) (ltac:(oD' 0x99400%Z)).
ld_step (ltac:(oF' 0x99404%Z)) (ltac:(oD' 0x99404%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721440)) (Z_to_bv 64 721440) ltac:(rd_img img_b5f08_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99408%Z)) (ltac:(oD' 0x99408%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721432)) (Z_to_bv 64 721432) ltac:(rd_img img_b5f10_8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x9940c%Z)) (ltac:(oD' 0x9940c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99410%Z)) (ltac:(oD' 0x99410%Z)) (word_to_le_bytes 8 (Z_to_bv 64 212248)) (Z_to_bv 64 212248) ltac:(rd_img img_b0218_8) ltac:(apply bytes_le_to_Z_8).
stepjr (ltac:(oF' 0x99414%Z)) (ltac:(oD' 0x99414%Z)) (0x33d18 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 627736 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 822448 ->
getr regs 8 = Z_to_bv 64 721440 ->
getr regs 9 = Z_to_bv 64 721432 ->
getr regs 18 = Z_to_bv 64 212508 ->
getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
getr regs 20 = Z_to_bv 64 0 ->
getr regs 21 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 1 = Z_to_bv 64 627928 ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 822448 ->
getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs' 9 = (argc_w inp) ->
getr regs' 10 = (argc_w inp) ->
getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
getr regs' 18 = Z_to_bv 64 212508 ->
getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
getr regs' 20 = Z_to_bv 64 0 ->
getr regs' 21 = Z_to_bv 64 0 ->
getr regs' 22 = Z_to_bv 64 0 ->
getr regs' 23 = Z_to_bv 64 0 ->
getr regs' 24 = Z_to_bv 64 0 ->
getr regs' 25 = Z_to_bv 64 0 ->
getr regs' 26 = Z_to_bv 64 0 ->
getr regs' 27 = Z_to_bv 64 0 ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
G (mkst regs' (0x33e1c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 627912))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 627736))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 721440))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 750128) ([Z_to_bv 8 1]))) rom)) ->
G (mkst regs (0x33d18 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627412))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 627912))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 954144) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 954148) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 954145) ([Z_to_bv 8 0])) (Z_to_bv 64 822432) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x33d18%Z)) (ltac:(oD' 0x33d18%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)).
stw (ltac:(oF' 0x33d1c%Z)) (ltac:(oD' 0x33d1c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 627736) ltac:(ok_win HJ).
stw (ltac:(oF' 0x33d20%Z)) (ltac:(oD' 0x33d20%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 721440) ltac:(ok_win HJ).
sv (ltac:(oF' 0x33d24%Z)) (ltac:(oD' 0x33d24%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
sn (ltac:(oF' 0x33d28%Z)) (ltac:(oD' 0x33d28%Z)).
sn (ltac:(oF' 0x33d2c%Z)) (ltac:(oD' 0x33d2c%Z)).
lb_step (ltac:(oF' 0x33d30%Z)) (ltac:(oD' 0x33d30%Z)) (Z_to_bv 8 0) ltac:(rd_img img_b7230_1).
sn (ltac:(oF' 0x33d34%Z)) (ltac:(oD' 0x33d34%Z)).
stepb_tk (ltac:(oF' 0x33d38%Z)) (ltac:(oD' 0x33d38%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x33d44%Z)) (ltac:(oD' 0x33d44%Z)).
sn (ltac:(oF' 0x33d48%Z)) (ltac:(oD' 0x33d48%Z)).
sn (ltac:(oF' 0x33d4c%Z)) (ltac:(oD' 0x33d4c%Z)).
stw (ltac:(oF' 0x33d50%Z)) (ltac:(oD' 0x33d50%Z)) (Z_to_bv 64 750128) (Z_to_bv 64 1) ltac:(ok_data).
sn (ltac:(oF' 0x33d54%Z)) (ltac:(oD' 0x33d54%Z)).
ld_step (ltac:(oF' 0x33d58%Z)) (ltac:(oD' 0x33d58%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b5da8_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x33d5c%Z)) (ltac:(oD' 0x33d5c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x33d7c%Z)) (ltac:(oD' 0x33d7c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627736)) (Z_to_bv 64 627736) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x33d80%Z)) (ltac:(oD' 0x33d80%Z)) (word_to_le_bytes 8 (Z_to_bv 64 721440)) (Z_to_bv 64 721440) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x33d84%Z)) (ltac:(oD' 0x33d84%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stepret (ltac:(oF' 0x33d88%Z)) (ltac:(oD' 0x33d88%Z)) (0x99418 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x99418%Z)) (ltac:(oD' 0x99418%Z)).
stepb_ft (ltac:(oF' 0x9941c%Z)) (ltac:(oD' 0x9941c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99420%Z)) (ltac:(oD' 0x99420%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627912)) (Z_to_bv 64 627912) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99424%Z)) (ltac:(oD' 0x99424%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99428%Z)) (ltac:(oD' 0x99428%Z)) (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x9942c%Z)) (ltac:(oD' 0x9942c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stepret (ltac:(oF' 0x99430%Z)) (ltac:(oD' 0x99430%Z)) (0x994c8 : word) ltac:(pin; first [reflexivity | bveq]).
sv (ltac:(oF' 0x994c8%Z)) (ltac:(oD' 0x994c8%Z)) (argc_w inp).
sv (ltac:(oF' 0x994cc%Z)) (ltac:(oD' 0x994cc%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x994d0%Z)) (ltac:(oD' 0x994d0%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
stepjr (ltac:(oF' 0x994d4%Z)) (ltac:(oD' 0x994d4%Z)) (0x33e1c : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
