(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: decoded encoded statements such as len_av, rd_rnd, slli_argc, fin_c6 and fin_c7 into plain lemmas, dropping the TCodec name table and SE sections, and reparametrised section P over a ProcInput launch record with new rnd_facts_here; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Src0Startup4.v, 163 lines within its lines 15-381. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
StartupTac ArgvEnv RefLayout Js0Img Js0StartupDefs.
Import ListNotations.
Open Scope bv_scope.
Local Set Default Proof Using "All".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments) pc.
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
getr regs 4 = Z_to_bv 64 818272 ->
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
getr regs' 4 = Z_to_bv 64 818272 ->
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
G (mkst regs' (0x98280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x98278 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x98278%Z)) (ltac:(oD' 0x98278%Z)) (word_to_le_bytes 8 (rnd_w inp sp0)) (rnd_w inp sp0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x9827c%Z)) (ltac:(oD' 0x9827c%Z)).
sv (ltac:(oF' 0x98c28%Z)) (ltac:(oD' 0x98c28%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 432)).
stw (ltac:(oF' 0x98c2c%Z)) (ltac:(oD' 0x98c2c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 623232) ltac:(ok_win HJ).
stepb_ft (ltac:(oF' 0x98c30%Z)) (ltac:(oD' 0x98c30%Z)) ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
sv (ltac:(oF' 0x98c34%Z)) (ltac:(oD' 0x98c34%Z)) (rnd_w inp sp0).
sn (ltac:(oF' 0x98c38%Z)) (ltac:(oD' 0x98c38%Z)).
ld_step (ltac:(oF' 0x98c3c%Z)) (ltac:(oD' 0x98c3c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 949968)) (Z_to_bv 64 949968) ltac:(rd_img img_b4ec8_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x98c40%Z)) (ltac:(oD' 0x98c40%Z)).
sn (ltac:(oF' 0x98c44%Z)) (ltac:(oD' 0x98c44%Z)).
stepiv (ltac:(oF' 0xa9160%Z)) (ltac:(oD' 0xa9160%Z)) (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
stepb_tk (ltac:(oF' 0xa9164%Z)) (ltac:(oD' 0xa9164%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa9274%Z)) (ltac:(oD' 0xa9274%Z)).
sn (ltac:(oF' 0xa9278%Z)) (ltac:(oD' 0xa9278%Z)).
stepb_ft (ltac:(oF' 0xa927c%Z)) (ltac:(oD' 0xa927c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa9280%Z)) (ltac:(oD' 0xa9280%Z)).
stepb_tk (ltac:(oF' 0xa9284%Z)) (ltac:(oD' 0xa9284%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa92bc%Z)) (ltac:(oD' 0xa92bc%Z)).
stepb_ft (ltac:(oF' 0xa92c0%Z)) (ltac:(oD' 0xa92c0%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0xa92c4%Z)) (ltac:(oD' 0xa92c4%Z)) (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
ld_step (ltac:(oF' 0xa92c8%Z)) (ltac:(oD' 0xa92c8%Z)) (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
stw (ltac:(oF' 0xa92cc%Z)) (ltac:(oD' 0xa92cc%Z)) (Z_to_bv 64 949968) (rlw RND 0) ltac:(ok_data).
stw (ltac:(oF' 0xa92d0%Z)) (ltac:(oD' 0xa92d0%Z)) (Z_to_bv 64 949972) (rlw RND 4) ltac:(ok_data).
sn (ltac:(oF' 0xa92d4%Z)) (ltac:(oD' 0xa92d4%Z)).
sv (ltac:(oF' 0xa92d8%Z)) (ltac:(oD' 0xa92d8%Z)) (Z_to_bv 64 (bv_unsigned (rnd_w inp sp0) + 8)).
sn (ltac:(oF' 0xa92dc%Z)) (ltac:(oD' 0xa92dc%Z)).
stepb_tk (ltac:(oF' 0xa92e0%Z)) (ltac:(oD' 0xa92e0%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa9520%Z)) (ltac:(oD' 0xa9520%Z)).
stepb_ft (ltac:(oF' 0xa9524%Z)) (ltac:(oD' 0xa9524%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0xa9528%Z)) (ltac:(oD' 0xa9528%Z)).
stepb_ft (ltac:(oF' 0xa952c%Z)) (ltac:(oD' 0xa952c%Z)) ltac:(pin; cond_compute).
stepret (ltac:(oF' 0xa9530%Z)) (ltac:(oD' 0xa9530%Z)) (0x98c48 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x98c48%Z)) (ltac:(oD' 0x98c48%Z)).
sn (ltac:(oF' 0x98c64%Z)) (ltac:(oD' 0x98c64%Z)).
ld_step (ltac:(oF' 0x98c68%Z)) (ltac:(oD' 0x98c68%Z)) (word_to_le_bytes 8 (Z_to_bv 64 949968)) (Z_to_bv 64 949968) ltac:(rd_img img_b4ec8_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x98c6c%Z)) (ltac:(oD' 0x98c6c%Z)) (Z_to_bv 64 949969) (Z_to_bv 64 0) ltac:(ok_data).
ld_step (ltac:(oF' 0x98c70%Z)) (ltac:(oD' 0x98c70%Z)) (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
sn (ltac:(oF' 0x98c74%Z)) (ltac:(oD' 0x98c74%Z)).
stw (ltac:(oF' 0x98c78%Z)) (ltac:(oD' 0x98c78%Z)) (Z_to_bv 64 818256) (canary_w RND) ltac:(ok_data).
ld_step (ltac:(oF' 0x98c7c%Z)) (ltac:(oD' 0x98c7c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 623232)) (Z_to_bv 64 623232) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x98c80%Z)) (ltac:(oD' 0x98c80%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret (ltac:(oF' 0x98c84%Z)) (ltac:(oD' 0x98c84%Z)) (0x98280 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 818272 ->
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
getr regs' 4 = Z_to_bv 64 818272 ->
getr regs' 8 = Z_to_bv 64 0 ->
getr regs' 9 = Z_to_bv 64 0 ->
getr regs' 10 = Z_to_bv 64 211884 ->
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
G (mkst regs' (0x98440 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x98280 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x98280%Z)) (ltac:(oD' 0x98280%Z)) (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98284%Z)) (ltac:(oD' 0x98284%Z)) (word_to_le_bytes 8 uid) (in_uid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x98288%Z)) (ltac:(oD' 0x98288%Z)) ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step (ltac:(oF' 0x9828c%Z)) (ltac:(oD' 0x9828c%Z)) (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98290%Z)) (ltac:(oD' 0x98290%Z)) (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x98294%Z)) (ltac:(oD' 0x98294%Z)) ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step (ltac:(oF' 0x98298%Z)) (ltac:(oD' 0x98298%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x9829c%Z)) (ltac:(oD' 0x9829c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x9837c%Z)) (ltac:(oD' 0x9837c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 623636)) (Z_to_bv 64 623636) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98380%Z)) (ltac:(oD' 0x98380%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98384%Z)) (ltac:(oD' 0x98384%Z)) (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98388%Z)) (ltac:(oD' 0x98388%Z)) (word_to_le_bytes 8 (Z_to_bv 64 211884)) (Z_to_bv 64 211884) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x9838c%Z)) (ltac:(oD' 0x9838c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stepret (ltac:(oF' 0x98390%Z)) (ltac:(oD' 0x98390%Z)) (0x98414 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x98414%Z)) (ltac:(oD' 0x98414%Z)).
sn (ltac:(oF' 0x98418%Z)) (ltac:(oD' 0x98418%Z)).
sn (ltac:(oF' 0x9841c%Z)) (ltac:(oD' 0x9841c%Z)).
sv (ltac:(oF' 0x98420%Z)) (ltac:(oD' 0x98420%Z)) (argc_w inp).
sv (ltac:(oF' 0x98424%Z)) (ltac:(oD' 0x98424%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
ld_step (ltac:(oF' 0x98428%Z)) (ltac:(oD' 0x98428%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9842c%Z)) (ltac:(oD' 0x9842c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98430%Z)) (ltac:(oD' 0x98430%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98434%Z)) (ltac:(oD' 0x98434%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x98438%Z)) (ltac:(oD' 0x98438%Z)) sp0.
stepret (ltac:(oF' 0x9843c%Z)) (ltac:(oD' 0x9843c%Z)) (0x98440 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 0 ->
getr regs 2 = sp0 ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 818272 ->
getr regs 8 = Z_to_bv 64 0 ->
getr regs 9 = Z_to_bv 64 0 ->
getr regs 10 = Z_to_bv 64 211884 ->
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
getr regs' 1 = Z_to_bv 64 623556 ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 818272 ->
getr regs' 8 = Z_to_bv 64 717264 ->
getr regs' 9 = Z_to_bv 64 717256 ->
getr regs' 18 = Z_to_bv 64 211884 ->
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
G (mkst regs' (0x33aa8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 623732))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
G (mkst regs (0x98440 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x98440%Z)) (ltac:(oD' 0x98440%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stw (ltac:(oF' 0x98444%Z)) (ltac:(oD' 0x98444%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98448%Z)) (ltac:(oD' 0x98448%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x9844c%Z)) (ltac:(oD' 0x9844c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98450%Z)) (ltac:(oD' 0x98450%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98454%Z)) (ltac:(oD' 0x98454%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sv (ltac:(oF' 0x98458%Z)) (ltac:(oD' 0x98458%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x9845c%Z)) (ltac:(oD' 0x9845c%Z)) (argc_w inp).
sn (ltac:(oF' 0x98460%Z)) (ltac:(oD' 0x98460%Z)).
stepiv (ltac:(oF' 0x98464%Z)) (ltac:(oD' 0x98464%Z)) (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
sv (ltac:(oF' 0x98468%Z)) (ltac:(oD' 0x98468%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
sv (ltac:(oF' 0x9846c%Z)) (ltac:(oD' 0x9846c%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
sn (ltac:(oF' 0x98470%Z)) (ltac:(oD' 0x98470%Z)).
sv (ltac:(oF' 0x98394%Z)) (ltac:(oD' 0x98394%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stw (ltac:(oF' 0x98398%Z)) (ltac:(oD' 0x98398%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 623732) ltac:(ok_win HJ).
stw (ltac:(oF' 0x9839c%Z)) (ltac:(oD' 0x9839c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw (ltac:(oF' 0x983a0%Z)) (ltac:(oD' 0x983a0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w inp) ltac:(ok_win HJ).
sn (ltac:(oF' 0x983a4%Z)) (ltac:(oD' 0x983a4%Z)).
stepret (ltac:(oF' 0x98164%Z)) (ltac:(oD' 0x98164%Z)) (0x983a8 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x983a8%Z)) (ltac:(oD' 0x983a8%Z)).
sn (ltac:(oF' 0x983ac%Z)) (ltac:(oD' 0x983ac%Z)).
ld_step (ltac:(oF' 0x983b0%Z)) (ltac:(oD' 0x983b0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 717264)) (Z_to_bv 64 717264) ltac:(rd_img img_b4eb8_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x983b4%Z)) (ltac:(oD' 0x983b4%Z)) (word_to_le_bytes 8 (Z_to_bv 64 717256)) (Z_to_bv 64 717256) ltac:(rd_img img_b4ec0_8) ltac:(apply bytes_le_to_Z_8).
stepb_ft (ltac:(oF' 0x983b8%Z)) (ltac:(oD' 0x983b8%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x983bc%Z)) (ltac:(oD' 0x983bc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 211624)) (Z_to_bv 64 211624) ltac:(rd_img img_af1c8_8) ltac:(apply bytes_le_to_Z_8).
stepjr (ltac:(oF' 0x983c0%Z)) (ltac:(oD' 0x983c0%Z)) (0x33aa8 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 623556 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 818272 ->
getr regs 8 = Z_to_bv 64 717264 ->
getr regs 9 = Z_to_bv 64 717256 ->
getr regs 18 = Z_to_bv 64 211884 ->
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
getr regs' 1 = Z_to_bv 64 623748 ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
getr regs' 3 = Z_to_bv 64 67584 ->
getr regs' 4 = Z_to_bv 64 818272 ->
getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs' 9 = (argc_w inp) ->
getr regs' 10 = (argc_w inp) ->
getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
getr regs' 18 = Z_to_bv 64 211884 ->
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
G (mkst regs' (0x33bac : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 623732))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 623556))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 717264))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 745952) ([Z_to_bv 8 1]))) rom)) ->
G (mkst regs (0x33aa8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux inp mbase entry sp0 rdraw (J_lsm inp sp0 Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w inp rdraw))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623232))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 623732))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w inp))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc inp sp0 rdraw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949968) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 949972) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 949969) ([Z_to_bv 8 0])) (Z_to_bv 64 818256) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof.
intros G.
intros HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x33aa8%Z)) (ltac:(oD' 0x33aa8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)).
stw (ltac:(oF' 0x33aac%Z)) (ltac:(oD' 0x33aac%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 623556) ltac:(ok_win HJ).
stw (ltac:(oF' 0x33ab0%Z)) (ltac:(oD' 0x33ab0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 717264) ltac:(ok_win HJ).
sv (ltac:(oF' 0x33ab4%Z)) (ltac:(oD' 0x33ab4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
sn (ltac:(oF' 0x33ab8%Z)) (ltac:(oD' 0x33ab8%Z)).
sn (ltac:(oF' 0x33abc%Z)) (ltac:(oD' 0x33abc%Z)).
lb_step (ltac:(oF' 0x33ac0%Z)) (ltac:(oD' 0x33ac0%Z)) (Z_to_bv 8 0) ltac:(rd_img img_b61e0_1).
sn (ltac:(oF' 0x33ac4%Z)) (ltac:(oD' 0x33ac4%Z)).
stepb_tk (ltac:(oF' 0x33ac8%Z)) (ltac:(oD' 0x33ac8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x33ad4%Z)) (ltac:(oD' 0x33ad4%Z)).
sn (ltac:(oF' 0x33ad8%Z)) (ltac:(oD' 0x33ad8%Z)).
sn (ltac:(oF' 0x33adc%Z)) (ltac:(oD' 0x33adc%Z)).
stw (ltac:(oF' 0x33ae0%Z)) (ltac:(oD' 0x33ae0%Z)) (Z_to_bv 64 745952) (Z_to_bv 64 1) ltac:(ok_data).
sn (ltac:(oF' 0x33ae4%Z)) (ltac:(oD' 0x33ae4%Z)).
ld_step (ltac:(oF' 0x33ae8%Z)) (ltac:(oD' 0x33ae8%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b4d58_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x33aec%Z)) (ltac:(oD' 0x33aec%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x33b0c%Z)) (ltac:(oD' 0x33b0c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 623556)) (Z_to_bv 64 623556) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x33b10%Z)) (ltac:(oD' 0x33b10%Z)) (word_to_le_bytes 8 (Z_to_bv 64 717264)) (Z_to_bv 64 717264) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x33b14%Z)) (ltac:(oD' 0x33b14%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stepret (ltac:(oF' 0x33b18%Z)) (ltac:(oD' 0x33b18%Z)) (0x983c4 : word) ltac:(pin; first [reflexivity | bveq]).
sn (ltac:(oF' 0x983c4%Z)) (ltac:(oD' 0x983c4%Z)).
stepb_ft (ltac:(oF' 0x983c8%Z)) (ltac:(oD' 0x983c8%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x983cc%Z)) (ltac:(oD' 0x983cc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 623732)) (Z_to_bv 64 623732) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x983d0%Z)) (ltac:(oD' 0x983d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x983d4%Z)) (ltac:(oD' 0x983d4%Z)) (word_to_le_bytes 8 (argc_w inp)) (argc_w inp) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x983d8%Z)) (ltac:(oD' 0x983d8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stepret (ltac:(oF' 0x983dc%Z)) (ltac:(oD' 0x983dc%Z)) (0x98474 : word) ltac:(pin; first [reflexivity | bveq]).
sv (ltac:(oF' 0x98474%Z)) (ltac:(oD' 0x98474%Z)) (argc_w inp).
sv (ltac:(oF' 0x98478%Z)) (ltac:(oD' 0x98478%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv (ltac:(oF' 0x9847c%Z)) (ltac:(oD' 0x9847c%Z)) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
stepjr (ltac:(oF' 0x98480%Z)) (ltac:(oD' 0x98480%Z)) (0x33bac : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End P.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
