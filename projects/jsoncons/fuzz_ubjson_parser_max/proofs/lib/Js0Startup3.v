(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0Startup3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "3add"; "4le"; "5firstn"; "5skipn"; "6Z"; "0D"]; ["0G"; "0J"; "0Jb"; "7Segment"; "8machine_state"; "8word_to_le_bytes"; "9at_random_bytes"; "9ed_random"; ":sp_window_hi"; ":sp_window_lo"; ";bvmap"; "<wbytes"; "=regs_agree"; ">D_libc"; ">J_aux"; ">J_lsm"]; [">argc_w"; ">pn_w"; ">rnd_w"; "?cmem"; "?wfJ"; "@getr"; "@mkst"; "@rdn"; "@v_slli"; "@wrap_mem"; "Abwd"; "Bloaded_segments"; "Bphdrs"; "CIn"; "Dadd"; "Dle"]; ["Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0a"; "0a'"; "0av"; "0ev"; "0fx"; "0hw"; "0j"; "0m"; "0n"; "0r"]; ["0rdraw"; "0regs"; "0regs'"; "0rom"; "0s1v"; "0segs"; "0sp0"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0tid"; "0uid"]]).
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
Variable sp0 : word.
Variable Jb : word -> option byte.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rdraw : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
Local Notation RND := (ed_random rdraw) (only parsing).
Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
Lemma Hsp_lo' : ltac2:(TCodec.tc2 tcn__Js0Startup3 "7&Q?&I&R:yR0vR6%3221%6251"). Proof. exact Hlo. Qed.
Lemma Hsp_hi' : ltac2:(TCodec.tc2 tcn__Js0Startup3 "7&Q?&R:yR0vR6%3221&H%6221"). Proof. exact Hhi. Qed.
Lemma len_av : ltac2:(TCodec.tc2 tcn__Js0Startup3 "A'8&Q?+1&QC&2'3'R9y8%211%411vQH%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma rnd_bounds : ltac2:(TCodec.tc2 tcn__Js0Startup3 "N'8&Q?&R:yR0vR6%3221&Q2vQHvQI%33521%8271%:261&Q@&Q>+@%2251&QD+2+R0%3221%8251'9'>&QA+8%22?1z%63521%L281%M2B1").
Proof.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
unfold rnd_w. repeat split; lia.
Qed.
Lemma rd_rnd : ltac2:(TCodec.tc2 tcn__Js0Startup3 "QO'R9yR0%211'6y8%511%311p051'4';&:r2r1%3221u@%6221'9'3%11=%@11&Q7&Q;&Q3vR6&Q9&Q<vQHvQIvR<vQKvR0%776854321r5r4%<4;321&R8&Q>&R:&Q2%13@=<%32Q71&QCr3%211%8241%:2Q<1%J4I<1Q3(0&<&=&F&G%11F%311%53QA<1%73QBQ<1%92Q61%Q93Q6;1p0Q;1pSNQC1pSJQD1pQ0QF1pQ4QG1").
Proof.
intros J D j n Hjn.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.
Lemma rdn_addr : ltac2:(TCodec.tc2 tcn__Js0Startup3 "Q5'3'C%211'R9yR0%211'6y8%511%311p051'4%<14%711'9&Q7r6r5r3r2%544321r1%83921r4%:3C71r8r7%<421;4%>3?1:p051p081pT0B1pSNE1pS@L1pS>M1pSLI1pT<Q21").
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
Lemma slli_argc : ltac2:(TCodec.tc2 tcn__Js0Startup3 "H'9'R9yR0%211&Q8&Q0vQH%211+3%5221&R8&QB+8&QC&2'3y8%@11%311%521=%711%:291%<2D1%G3D>1").
Proof.
pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_tls_c1 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 623224 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 950000 ->
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
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 950000) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 949352) ->
getr regs' 13 = (Z_to_bv 64 10) ->
getr regs' 15 = (Z_to_bv 64 65600) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65600) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
G (mkst regs' (0x98510 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x98488 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c1) 0%nat 0%nat).
Lemma tls_c1 : ltac:(sec_stmt2 constr:(SEC_T_tls_c1) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x98488%Z)) (ltac:(oD' 0x98488%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw (ltac:(oF' 0x9848c%Z)) (ltac:(oD' 0x9848c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 623224) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98490%Z)) (ltac:(oD' 0x98490%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw (ltac:(oF' 0x98494%Z)) (ltac:(oD' 0x98494%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw (ltac:(oF' 0x98498%Z)) (ltac:(oD' 0x98498%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 950000) ltac:(ok_win HJ).
stw (ltac:(oF' 0x9849c%Z)) (ltac:(oD' 0x9849c%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x984a0%Z)) (ltac:(oD' 0x984a0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x984a4%Z)) (ltac:(oD' 0x984a4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step (ltac:(oF' 0x984a8%Z)) (ltac:(oD' 0x984a8%Z)) (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x984ac%Z)) (ltac:(oD' 0x984ac%Z)).
sn (ltac:(oF' 0x984b0%Z)) (ltac:(oD' 0x984b0%Z)).
sn (ltac:(oF' 0x984b4%Z)) (ltac:(oD' 0x984b4%Z)).
sn (ltac:(oF' 0x984b8%Z)) (ltac:(oD' 0x984b8%Z)).
stepb_ft (ltac:(oF' 0x984bc%Z)) (ltac:(oD' 0x984bc%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x984c0%Z)) (ltac:(oD' 0x984c0%Z)).
sn (ltac:(oF' 0x984c4%Z)) (ltac:(oD' 0x984c4%Z)).
sn (ltac:(oF' 0x984c8%Z)) (ltac:(oD' 0x984c8%Z)).
ld_step (ltac:(oF' 0x984cc%Z)) (ltac:(oD' 0x984cc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x984d0%Z)) (ltac:(oD' 0x984d0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x984d4%Z)) (ltac:(oD' 0x984d4%Z)).
sn (ltac:(oF' 0x984d8%Z)) (ltac:(oD' 0x984d8%Z)).
ld_step (ltac:(oF' 0x984dc%Z)) (ltac:(oD' 0x984dc%Z)) (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_b61c0_4) ltac:(vm_compute; reflexivity).
ld_step (ltac:(oF' 0x984e0%Z)) (ltac:(oD' 0x984e0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b4d38_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x984e4%Z)) (ltac:(oD' 0x984e4%Z)).
sn (ltac:(oF' 0x984e8%Z)) (ltac:(oD' 0x984e8%Z)).
sn (ltac:(oF' 0x984ec%Z)) (ltac:(oD' 0x984ec%Z)).
sn (ltac:(oF' 0x984f0%Z)) (ltac:(oD' 0x984f0%Z)).
sn (ltac:(oF' 0x984f4%Z)) (ltac:(oD' 0x984f4%Z)).
sn (ltac:(oF' 0x984f8%Z)) (ltac:(oD' 0x984f8%Z)).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_tls_c2 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 950000 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 949352 ->
getr regs 13 = Z_to_bv 64 10 ->
getr regs 15 = Z_to_bv 64 65600 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65600 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 5 = (Z_to_bv 64 0) ->
getr regs' 7 = (Z_to_bv 64 7) ->
getr regs' 9 = (Z_to_bv 64 950000) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 949352) ->
getr regs' 13 = (Z_to_bv 64 4) ->
getr regs' 16 = (Z_to_bv 64 6) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
getr regs' 28 = (Z_to_bv 64 1685382481) ->
getr regs' 29 = (Z_to_bv 64 65936) ->
getr regs' 30 = (Z_to_bv 64 131072) ->
regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x98510 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x98510 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c2) 0%nat 0%nat).
Lemma tls_c2 : ltac:(sec_stmt2 constr:(SEC_T_tls_c2) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x984fc%Z)) (ltac:(oD' 0x984fc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x98500%Z)) (ltac:(oD' 0x98500%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_tls_c3 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 5 = Z_to_bv 64 0 ->
getr regs 7 = Z_to_bv 64 7 ->
getr regs 9 = Z_to_bv 64 950000 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 949352 ->
getr regs 13 = Z_to_bv 64 4 ->
getr regs 16 = Z_to_bv 64 6 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
getr regs 28 = Z_to_bv 64 1685382481 ->
getr regs 29 = Z_to_bv 64 65936 ->
getr regs 30 = Z_to_bv 64 131072 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 9 = (Z_to_bv 64 950000) ->
getr regs' 11 = (Z_to_bv 64 949352) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x98560 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x98510 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c3) 0%nat 0%nat).
Lemma tls_c3 : ltac:(sec_stmt2 constr:(SEC_T_tls_c3) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_ft (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x9853c%Z)) (ltac:(oD' 0x9853c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x98540%Z)) (ltac:(oD' 0x98540%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_ft (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98510%Z)) (ltac:(oD' 0x98510%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x98514%Z)) (ltac:(oD' 0x98514%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x98518%Z)) (ltac:(oD' 0x98518%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9852c%Z)) (ltac:(oD' 0x9852c%Z)).
stepb_ft (ltac:(oF' 0x98530%Z)) (ltac:(oD' 0x98530%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98534%Z)) (ltac:(oD' 0x98534%Z)).
stepb_tk (ltac:(oF' 0x98538%Z)) (ltac:(oD' 0x98538%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98558%Z)) (ltac:(oD' 0x98558%Z)).
sn (ltac:(oF' 0x9855c%Z)) (ltac:(oD' 0x9855c%Z)).
sn (ltac:(oF' 0x98504%Z)) (ltac:(oD' 0x98504%Z)).
sn (ltac:(oF' 0x98508%Z)) (ltac:(oD' 0x98508%Z)).
stepb_tk (ltac:(oF' 0x9850c%Z)) (ltac:(oD' 0x9850c%Z)) ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_tls_c4 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 9 = Z_to_bv 64 950000 ->
getr regs 11 = Z_to_bv 64 949352 ->
getr regs 17 = Z_to_bv 64 0 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 480)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 818272) ->
getr regs' 10 = (Z_to_bv 64 949352) ->
getr regs' 11 = (Z_to_bv 64 950056) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 818064) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073708733344) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 818072) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x986e4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x98560 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c4) 0%nat 0%nat).
Lemma tls_c4 : ltac:(sec_stmt2 constr:(SEC_T_tls_c4) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk (ltac:(oF' 0x98560%Z)) (ltac:(oD' 0x98560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x98598%Z)) (ltac:(oD' 0x98598%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7c78_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9859c%Z)) (ltac:(oD' 0x9859c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7c88_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x985a0%Z)) (ltac:(oD' 0x985a0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7c90_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x985a4%Z)) (ltac:(oD' 0x985a4%Z)).
sn (ltac:(oF' 0x985a8%Z)) (ltac:(oD' 0x985a8%Z)).
sn (ltac:(oF' 0x985ac%Z)) (ltac:(oD' 0x985ac%Z)).
sn (ltac:(oF' 0x985b0%Z)) (ltac:(oD' 0x985b0%Z)).
sn (ltac:(oF' 0x985b4%Z)) (ltac:(oD' 0x985b4%Z)).
sn (ltac:(oF' 0x985b8%Z)) (ltac:(oD' 0x985b8%Z)).
sn (ltac:(oF' 0x985bc%Z)) (ltac:(oD' 0x985bc%Z)).
stw (ltac:(oF' 0x985c0%Z)) (ltac:(oD' 0x985c0%Z)) (Z_to_bv 64 949384) (Z_to_bv 64 0) ltac:(ok_data).
stw (ltac:(oF' 0x985c4%Z)) (ltac:(oD' 0x985c4%Z)) (Z_to_bv 64 949400) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft (ltac:(oF' 0x985c8%Z)) (ltac:(oD' 0x985c8%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x985cc%Z)) (ltac:(oD' 0x985cc%Z)).
stw (ltac:(oF' 0x985d0%Z)) (ltac:(oD' 0x985d0%Z)) (Z_to_bv 64 949392) (Z_to_bv 64 8) ltac:(ok_data).
sn (ltac:(oF' 0x985d4%Z)) (ltac:(oD' 0x985d4%Z)).
sn (ltac:(oF' 0x985d8%Z)) (ltac:(oD' 0x985d8%Z)).
sn (ltac:(oF' 0x985dc%Z)) (ltac:(oD' 0x985dc%Z)).
sn (ltac:(oF' 0x985e0%Z)) (ltac:(oD' 0x985e0%Z)).
sn (ltac:(oF' 0x985e4%Z)) (ltac:(oD' 0x985e4%Z)).
sn (ltac:(oF' 0x985e8%Z)) (ltac:(oD' 0x985e8%Z)).
stw (ltac:(oF' 0x985ec%Z)) (ltac:(oD' 0x985ec%Z)) (Z_to_bv 64 950024) (Z_to_bv 64 224) ltac:(ok_data).
stw (ltac:(oF' 0x985f0%Z)) (ltac:(oD' 0x985f0%Z)) (Z_to_bv 64 950032) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk (ltac:(oF' 0x985f4%Z)) (ltac:(oD' 0x985f4%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x98628%Z)) (ltac:(oD' 0x98628%Z)).
ld_step (ltac:(oF' 0x9862c%Z)) (ltac:(oD' 0x9862c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7f00_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98630%Z)) (ltac:(oD' 0x98630%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7f18_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x98634%Z)) (ltac:(oD' 0x98634%Z)).
sn (ltac:(oF' 0x98638%Z)) (ltac:(oD' 0x98638%Z)).
sn (ltac:(oF' 0x9863c%Z)) (ltac:(oD' 0x9863c%Z)).
sn (ltac:(oF' 0x98640%Z)) (ltac:(oD' 0x98640%Z)).
sn (ltac:(oF' 0x98644%Z)) (ltac:(oD' 0x98644%Z)).
sn (ltac:(oF' 0x98648%Z)) (ltac:(oD' 0x98648%Z)).
sn (ltac:(oF' 0x9864c%Z)) (ltac:(oD' 0x9864c%Z)).
sn (ltac:(oF' 0x98650%Z)) (ltac:(oD' 0x98650%Z)).
sn (ltac:(oF' 0x98654%Z)) (ltac:(oD' 0x98654%Z)).
sn (ltac:(oF' 0x98658%Z)) (ltac:(oD' 0x98658%Z)).
sn (ltac:(oF' 0x9865c%Z)) (ltac:(oD' 0x9865c%Z)).
stepb_tk (ltac:(oF' 0x98660%Z)) (ltac:(oD' 0x98660%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0x986a8%Z)) (ltac:(oD' 0x986a8%Z)) (Z_to_bv 64 818288) (Z_to_bv 64 0) ltac:(ok_data).
stw (ltac:(oF' 0x986ac%Z)) (ltac:(oD' 0x986ac%Z)) (Z_to_bv 64 818264) (Z_to_bv 64 818288) ltac:(ok_data).
stw (ltac:(oF' 0x986b0%Z)) (ltac:(oD' 0x986b0%Z)) (Z_to_bv 64 818072) (Z_to_bv 64 818072) ltac:(ok_data).
sn (ltac:(oF' 0x986b4%Z)) (ltac:(oD' 0x986b4%Z)).
sn (ltac:(oF' 0x986b8%Z)) (ltac:(oD' 0x986b8%Z)).
sn (ltac:(oF' 0xab820%Z)) (ltac:(oD' 0xab820%Z)).
sn (ltac:(oF' 0xab824%Z)) (ltac:(oD' 0xab824%Z)).
stepret (ltac:(oF' 0xab828%Z)) (ltac:(oD' 0xab828%Z)) (0x986bc : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft (ltac:(oF' 0x986bc%Z)) (ltac:(oD' 0x986bc%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x986c0%Z)) (ltac:(oD' 0x986c0%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x986c4%Z)) (ltac:(oD' 0x986c4%Z)).
stw (ltac:(oF' 0x986c8%Z)) (ltac:(oD' 0x986c8%Z)) (Z_to_bv 64 950000) (Z_to_bv 64 1) ltac:(ok_data).
sn (ltac:(oF' 0x986cc%Z)) (ltac:(oD' 0x986cc%Z)).
sn (ltac:(oF' 0x986d0%Z)) (ltac:(oD' 0x986d0%Z)).
stw (ltac:(oF' 0x986d4%Z)) (ltac:(oD' 0x986d4%Z)) (Z_to_bv 64 818112) (Z_to_bv 64 2) ltac:(ok_data).
sn (ltac:(oF' 0x986d8%Z)) (ltac:(oD' 0x986d8%Z)).
sn (ltac:(oF' 0x986dc%Z)) (ltac:(oD' 0x986dc%Z)).
sn (ltac:(oF' 0x986e0%Z)) (ltac:(oD' 0x986e0%Z)).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_tls_c5 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 4 = Z_to_bv 64 818272 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 950056 ->
getr regs 18 = Z_to_bv 64 818072 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 818272) ->
getr regs' 19 = (Z_to_bv 64 0) ->
getr regs' 20 = (Z_to_bv 64 0) ->
getr regs' 21 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
G (mkst regs' (0x98278 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 818104) (word_to_le_bytes 4 tid)) (Z_to_bv 64 818224) (word_to_le_bytes 8 (Z_to_bv 64 950056))) (Z_to_bv 64 818192) (word_to_le_bytes 8 (Z_to_bv 64 818192))) (Z_to_bv 64 818080) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818088) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 818096) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x986e8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 623224))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 950000))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 949384) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949400) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 949392) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 950024) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 950032) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 818288) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 818264) (word_to_le_bytes 8 (Z_to_bv 64 818288))) (Z_to_bv 64 818072) (word_to_le_bytes 8 (Z_to_bv 64 818072))) (Z_to_bv 64 950000) ([Z_to_bv 8 1])) (Z_to_bv 64 818112) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c5) 0%nat 0%nat).
Lemma tls_c5 : ltac:(sec_stmt2 constr:(SEC_T_tls_c5) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn (ltac:(oF' 0x986e8%Z)) (ltac:(oD' 0x986e8%Z)).
stw (ltac:(oF' 0x986ec%Z)) (ltac:(oD' 0x986ec%Z)) (Z_to_bv 64 818104) tid ltac:(ok_data).
stw (ltac:(oF' 0x986f0%Z)) (ltac:(oD' 0x986f0%Z)) (Z_to_bv 64 818224) (Z_to_bv 64 950056) ltac:(ok_data).
stw (ltac:(oF' 0x986f4%Z)) (ltac:(oD' 0x986f4%Z)) (Z_to_bv 64 818192) (Z_to_bv 64 818192) ltac:(ok_data).
sn (ltac:(oF' 0x986f8%Z)) (ltac:(oD' 0x986f8%Z)).
ld_step (ltac:(oF' 0x986fc%Z)) (ltac:(oD' 0x986fc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e7ed8_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x98700%Z)) (ltac:(oD' 0x98700%Z)) (Z_to_bv 64 818080) (Z_to_bv 64 818072) ltac:(ok_data).
stw (ltac:(oF' 0x98704%Z)) (ltac:(oD' 0x98704%Z)) (Z_to_bv 64 818088) (Z_to_bv 64 818072) ltac:(ok_data).
stw (ltac:(oF' 0x98708%Z)) (ltac:(oD' 0x98708%Z)) (Z_to_bv 64 818096) (Z_to_bv 64 0) ltac:(ok_data).
sn (ltac:(oF' 0x9870c%Z)) (ltac:(oD' 0x9870c%Z)).
ld_step (ltac:(oF' 0x98714%Z)) (ltac:(oD' 0x98714%Z)) (word_to_le_bytes 8 (Z_to_bv 64 623224)) (Z_to_bv 64 623224) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98718%Z)) (ltac:(oD' 0x98718%Z)) (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9871c%Z)) (ltac:(oD' 0x9871c%Z)) (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98720%Z)) (ltac:(oD' 0x98720%Z)) (word_to_le_bytes 8 (Z_to_bv 64 950000)) (Z_to_bv 64 950000) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98724%Z)) (ltac:(oD' 0x98724%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x98728%Z)) (ltac:(oD' 0x98728%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9872c%Z)) (ltac:(oD' 0x9872c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x98730%Z)) (ltac:(oD' 0x98730%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret (ltac:(oF' 0x98734%Z)) (ltac:(oD' 0x98734%Z)) (0x98278 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
End P.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
