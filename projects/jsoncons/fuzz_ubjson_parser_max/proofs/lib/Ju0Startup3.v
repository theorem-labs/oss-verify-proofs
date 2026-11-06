(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Startup3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0StartupDefs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MemSplit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StartupTac."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "3add"; "4le"; "5firstn"; "5skipn"; "6Z"; "0D"]; ["0G"; "0J"; "0Jb"; "7Segment"; "8machine_state"; "8word_to_le_bytes"; "9at_random_bytes"; "9ed_random"; ":sp_window_hi"; ":sp_window_lo"; ";bvmap"; "<wbytes"; "=regs_agree"; ">D_libc"; ">J_aux"; ">J_lsm"]; [">argc_w"; ">pn_w"; ">rnd_w"; "?cmem"; "?wfJ"; "@getr"; "@mkst"; "@rdn"; "@v_slli"; "@wrap_mem"; "Abwd"; "Bloaded_segments"; "Bphdrs"; "CIn"; "Dadd"; "Dle"]; ["Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0a"; "0a'"; "0av"; "0ev"; "0fx"; "0hw"; "0j"; "0m"; "0n"; "0r"]; ["0rdraw"; "0regs"; "0regs'"; "0rom"; "0s1v"; "0segs"; "0sp0"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0tid"; "0uid"]]).
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
Lemma Hsp_lo' : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "7&Q?&I&R:yR0vR6%3221%6251"). Proof. exact Hlo. Qed.
Lemma Hsp_hi' : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "7&Q?&R:yR0vR6%3221&H%6221"). Proof. exact Hhi. Qed.
Lemma len_av : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "A'8&Q?+1&QC&2'3'R9y8%211%411vQH%7221%911%<2;1+QP0%>231%@231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma rnd_bounds : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "N'8&Q?&R:yR0vR6%3221&Q2vQHvQI%33521%8271%:261&Q@&Q>+@%2251&QD+2+R0%3221%8251'9'>&QA+8%22?1z%63521%L281%M2B1").
Proof.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
unfold rnd_w. repeat split; lia.
Qed.
Lemma rd_rnd : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "QO'R9yR0%211'6y8%511%311p051'4';&:r2r1%3221u@%6221'9'3%11=%@11&Q7&Q;&Q3vR6&Q9&Q<vQHvQIvR<vQKvR0%776854321r5r4%<4;321&R8&Q>&R:&Q2%13@=<%32Q71&QCr3%211%8241%:2Q<1%J4I<1Q3(0&<&=&F&G%11F%311%53QA<1%73QBQ<1%92Q61%Q93Q6;1p0Q;1pSNQC1pSJQD1pQ0QF1pQ4QG1").
Proof.
intros J D j n Hjn.
destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.
Lemma rdn_addr : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "Q5'3'C%211'R9yR0%211'6y8%511%311p051'4%<14%711'9&Q7r6r5r3r2%544321r1%83921r4%:3C71r8r7%<421;4%>3?1:p051p081pT0B1pSNE1pS@L1pS>M1pSLI1pT<Q21").
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
Lemma slli_argc : ltac2:(TCodec.tc2 tcn__Ju0Startup3 "H'9'R9yR0%211&Q8&Q0vQH%211+3%5221&R8&QB+8&QC&2'3y8%@11%311%521=%711%:291%<2D1%G3D>1").
Proof.
pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_tls_c1 := (forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
wfJ sp0 Jb ->
getr regs 1 = Z_to_bv 64 627404 ->
getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
getr regs 3 = Z_to_bv 64 67584 ->
getr regs 8 = pn_w sp0 av ev ->
getr regs 9 = s1v ->
getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
getr regs 18 = Z_to_bv 64 954176 ->
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
getr regs' 9 = (Z_to_bv 64 954176) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 953528) ->
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
G (mkst regs' (0x99564 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x994dc : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c1) 0%nat 0%nat).
Lemma tls_c1 : ltac:(sec_stmt2 constr:(SEC_T_tls_c1) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv (ltac:(oF' 0x994dc%Z)) (ltac:(oD' 0x994dc%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw (ltac:(oF' 0x994e0%Z)) (ltac:(oD' 0x994e0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 627404) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994e4%Z)) (ltac:(oD' 0x994e4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994e8%Z)) (ltac:(oD' 0x994e8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw (ltac:(oF' 0x994ec%Z)) (ltac:(oD' 0x994ec%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 954176) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994f0%Z)) (ltac:(oD' 0x994f0%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994f4%Z)) (ltac:(oD' 0x994f4%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw (ltac:(oF' 0x994f8%Z)) (ltac:(oD' 0x994f8%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step (ltac:(oF' 0x994fc%Z)) (ltac:(oD' 0x994fc%Z)) (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99500%Z)) (ltac:(oD' 0x99500%Z)).
sn (ltac:(oF' 0x99504%Z)) (ltac:(oD' 0x99504%Z)).
sn (ltac:(oF' 0x99508%Z)) (ltac:(oD' 0x99508%Z)).
sn (ltac:(oF' 0x9950c%Z)) (ltac:(oD' 0x9950c%Z)).
stepb_ft (ltac:(oF' 0x99510%Z)) (ltac:(oD' 0x99510%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99514%Z)) (ltac:(oD' 0x99514%Z)).
sn (ltac:(oF' 0x99518%Z)) (ltac:(oD' 0x99518%Z)).
sn (ltac:(oF' 0x9951c%Z)) (ltac:(oD' 0x9951c%Z)).
ld_step (ltac:(oF' 0x99520%Z)) (ltac:(oD' 0x99520%Z)) (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99524%Z)) (ltac:(oD' 0x99524%Z)) (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99528%Z)) (ltac:(oD' 0x99528%Z)).
sn (ltac:(oF' 0x9952c%Z)) (ltac:(oD' 0x9952c%Z)).
ld_step (ltac:(oF' 0x99530%Z)) (ltac:(oD' 0x99530%Z)) (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_b7210_4) ltac:(vm_compute; reflexivity).
ld_step (ltac:(oF' 0x99534%Z)) (ltac:(oD' 0x99534%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_b5d88_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99538%Z)) (ltac:(oD' 0x99538%Z)).
sn (ltac:(oF' 0x9953c%Z)) (ltac:(oD' 0x9953c%Z)).
sn (ltac:(oF' 0x99540%Z)) (ltac:(oD' 0x99540%Z)).
sn (ltac:(oF' 0x99544%Z)) (ltac:(oD' 0x99544%Z)).
sn (ltac:(oF' 0x99548%Z)) (ltac:(oD' 0x99548%Z)).
sn (ltac:(oF' 0x9954c%Z)) (ltac:(oD' 0x9954c%Z)).
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
getr regs 9 = Z_to_bv 64 954176 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 953528 ->
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
getr regs' 9 = (Z_to_bv 64 954176) ->
getr regs' 10 = (Z_to_bv 64 56) ->
getr regs' 11 = (Z_to_bv 64 953528) ->
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
G (mkst regs' (0x99564 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x99564 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c2) 0%nat 0%nat).
Lemma tls_c2 : ltac:(sec_stmt2 constr:(SEC_T_tls_c2) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99550%Z)) (ltac:(oD' 0x99550%Z)) (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99554%Z)) (ltac:(oD' 0x99554%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 954176 ->
getr regs 10 = Z_to_bv 64 56 ->
getr regs 11 = Z_to_bv 64 953528 ->
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
getr regs' 9 = (Z_to_bv 64 954176) ->
getr regs' 11 = (Z_to_bv 64 953528) ->
getr regs' 17 = (Z_to_bv 64 0) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
G (mkst regs' (0x995b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
G (mkst regs (0x99564 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c3) 0%nat 0%nat).
Lemma tls_c3 : ltac:(sec_stmt2 constr:(SEC_T_tls_c3) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_ft (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99590%Z)) (ltac:(oD' 0x99590%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk (ltac:(oF' 0x99594%Z)) (ltac:(oD' 0x99594%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_ft (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x99564%Z)) (ltac:(oD' 0x99564%Z)) (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft (ltac:(oF' 0x99568%Z)) (ltac:(oD' 0x99568%Z)) ltac:(pin; cond_compute).
stepb_tk (ltac:(oF' 0x9956c%Z)) (ltac:(oD' 0x9956c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99580%Z)) (ltac:(oD' 0x99580%Z)).
stepb_ft (ltac:(oF' 0x99584%Z)) (ltac:(oD' 0x99584%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99588%Z)) (ltac:(oD' 0x99588%Z)).
stepb_tk (ltac:(oF' 0x9958c%Z)) (ltac:(oD' 0x9958c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x995ac%Z)) (ltac:(oD' 0x995ac%Z)).
sn (ltac:(oF' 0x995b0%Z)) (ltac:(oD' 0x995b0%Z)).
sn (ltac:(oF' 0x99558%Z)) (ltac:(oD' 0x99558%Z)).
sn (ltac:(oF' 0x9955c%Z)) (ltac:(oD' 0x9955c%Z)).
stepb_tk (ltac:(oF' 0x99560%Z)) (ltac:(oD' 0x99560%Z)) ltac:(pin; cond_compute).
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
getr regs 9 = Z_to_bv 64 954176 ->
getr regs 11 = Z_to_bv 64 953528 ->
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
getr regs' 4 = (Z_to_bv 64 822448) ->
getr regs' 10 = (Z_to_bv 64 953528) ->
getr regs' 11 = (Z_to_bv 64 954232) ->
getr regs' 12 = (Z_to_bv 64 0) ->
getr regs' 13 = (Z_to_bv 64 822240) ->
getr regs' 14 = (Z_to_bv 64 0) ->
getr regs' 15 = (Z_to_bv 64 18446744073708729168) ->
getr regs' 17 = (Z_to_bv 64 96) ->
getr regs' 18 = (Z_to_bv 64 822248) ->
getr regs' 22 = (Z_to_bv 64 0) ->
getr regs' 23 = (Z_to_bv 64 0) ->
getr regs' 24 = (Z_to_bv 64 0) ->
getr regs' 25 = (Z_to_bv 64 0) ->
getr regs' 26 = (Z_to_bv 64 0) ->
getr regs' 27 = (Z_to_bv 64 0) ->
regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
G (mkst regs' (0x99738 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
G (mkst regs (0x995b4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c4) 0%nat 0%nat).
Lemma tls_c4 : ltac:(sec_stmt2 constr:(SEC_T_tls_c4) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk (ltac:(oF' 0x995b4%Z)) (ltac:(oD' 0x995b4%Z)) ltac:(pin; cond_compute).
ld_step (ltac:(oF' 0x995ec%Z)) (ltac:(oD' 0x995ec%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8cc8_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x995f0%Z)) (ltac:(oD' 0x995f0%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8cd8_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x995f4%Z)) (ltac:(oD' 0x995f4%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8ce0_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x995f8%Z)) (ltac:(oD' 0x995f8%Z)).
sn (ltac:(oF' 0x995fc%Z)) (ltac:(oD' 0x995fc%Z)).
sn (ltac:(oF' 0x99600%Z)) (ltac:(oD' 0x99600%Z)).
sn (ltac:(oF' 0x99604%Z)) (ltac:(oD' 0x99604%Z)).
sn (ltac:(oF' 0x99608%Z)) (ltac:(oD' 0x99608%Z)).
sn (ltac:(oF' 0x9960c%Z)) (ltac:(oD' 0x9960c%Z)).
sn (ltac:(oF' 0x99610%Z)) (ltac:(oD' 0x99610%Z)).
stw (ltac:(oF' 0x99614%Z)) (ltac:(oD' 0x99614%Z)) (Z_to_bv 64 953560) (Z_to_bv 64 0) ltac:(ok_data).
stw (ltac:(oF' 0x99618%Z)) (ltac:(oD' 0x99618%Z)) (Z_to_bv 64 953576) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft (ltac:(oF' 0x9961c%Z)) (ltac:(oD' 0x9961c%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99620%Z)) (ltac:(oD' 0x99620%Z)).
stw (ltac:(oF' 0x99624%Z)) (ltac:(oD' 0x99624%Z)) (Z_to_bv 64 953568) (Z_to_bv 64 8) ltac:(ok_data).
sn (ltac:(oF' 0x99628%Z)) (ltac:(oD' 0x99628%Z)).
sn (ltac:(oF' 0x9962c%Z)) (ltac:(oD' 0x9962c%Z)).
sn (ltac:(oF' 0x99630%Z)) (ltac:(oD' 0x99630%Z)).
sn (ltac:(oF' 0x99634%Z)) (ltac:(oD' 0x99634%Z)).
sn (ltac:(oF' 0x99638%Z)) (ltac:(oD' 0x99638%Z)).
sn (ltac:(oF' 0x9963c%Z)) (ltac:(oD' 0x9963c%Z)).
stw (ltac:(oF' 0x99640%Z)) (ltac:(oD' 0x99640%Z)) (Z_to_bv 64 954200) (Z_to_bv 64 224) ltac:(ok_data).
stw (ltac:(oF' 0x99644%Z)) (ltac:(oD' 0x99644%Z)) (Z_to_bv 64 954208) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk (ltac:(oF' 0x99648%Z)) (ltac:(oD' 0x99648%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x9967c%Z)) (ltac:(oD' 0x9967c%Z)).
ld_step (ltac:(oF' 0x99680%Z)) (ltac:(oD' 0x99680%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8f50_8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99684%Z)) (ltac:(oD' 0x99684%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8f68_8) ltac:(apply bytes_le_to_Z_8).
sn (ltac:(oF' 0x99688%Z)) (ltac:(oD' 0x99688%Z)).
sn (ltac:(oF' 0x9968c%Z)) (ltac:(oD' 0x9968c%Z)).
sn (ltac:(oF' 0x99690%Z)) (ltac:(oD' 0x99690%Z)).
sn (ltac:(oF' 0x99694%Z)) (ltac:(oD' 0x99694%Z)).
sn (ltac:(oF' 0x99698%Z)) (ltac:(oD' 0x99698%Z)).
sn (ltac:(oF' 0x9969c%Z)) (ltac:(oD' 0x9969c%Z)).
sn (ltac:(oF' 0x996a0%Z)) (ltac:(oD' 0x996a0%Z)).
sn (ltac:(oF' 0x996a4%Z)) (ltac:(oD' 0x996a4%Z)).
sn (ltac:(oF' 0x996a8%Z)) (ltac:(oD' 0x996a8%Z)).
sn (ltac:(oF' 0x996ac%Z)) (ltac:(oD' 0x996ac%Z)).
sn (ltac:(oF' 0x996b0%Z)) (ltac:(oD' 0x996b0%Z)).
stepb_tk (ltac:(oF' 0x996b4%Z)) (ltac:(oD' 0x996b4%Z)) ltac:(pin; cond_compute).
stw (ltac:(oF' 0x996fc%Z)) (ltac:(oD' 0x996fc%Z)) (Z_to_bv 64 822464) (Z_to_bv 64 0) ltac:(ok_data).
stw (ltac:(oF' 0x99700%Z)) (ltac:(oD' 0x99700%Z)) (Z_to_bv 64 822440) (Z_to_bv 64 822464) ltac:(ok_data).
stw (ltac:(oF' 0x99704%Z)) (ltac:(oD' 0x99704%Z)) (Z_to_bv 64 822248) (Z_to_bv 64 822248) ltac:(ok_data).
sn (ltac:(oF' 0x99708%Z)) (ltac:(oD' 0x99708%Z)).
sn (ltac:(oF' 0x9970c%Z)) (ltac:(oD' 0x9970c%Z)).
sn (ltac:(oF' 0xac874%Z)) (ltac:(oD' 0xac874%Z)).
sn (ltac:(oF' 0xac878%Z)) (ltac:(oD' 0xac878%Z)).
stepret (ltac:(oF' 0xac87c%Z)) (ltac:(oD' 0xac87c%Z)) (0x99710 : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft (ltac:(oF' 0x99710%Z)) (ltac:(oD' 0x99710%Z)) ltac:(pin; cond_compute).
stepb_ft (ltac:(oF' 0x99714%Z)) (ltac:(oD' 0x99714%Z)) ltac:(pin; cond_compute).
sn (ltac:(oF' 0x99718%Z)) (ltac:(oD' 0x99718%Z)).
stw (ltac:(oF' 0x9971c%Z)) (ltac:(oD' 0x9971c%Z)) (Z_to_bv 64 954176) (Z_to_bv 64 1) ltac:(ok_data).
sn (ltac:(oF' 0x99720%Z)) (ltac:(oD' 0x99720%Z)).
sn (ltac:(oF' 0x99724%Z)) (ltac:(oD' 0x99724%Z)).
stw (ltac:(oF' 0x99728%Z)) (ltac:(oD' 0x99728%Z)) (Z_to_bv 64 822288) (Z_to_bv 64 2) ltac:(ok_data).
sn (ltac:(oF' 0x9972c%Z)) (ltac:(oD' 0x9972c%Z)).
sn (ltac:(oF' 0x99730%Z)) (ltac:(oD' 0x99730%Z)).
sn (ltac:(oF' 0x99734%Z)) (ltac:(oD' 0x99734%Z)).
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
getr regs 4 = Z_to_bv 64 822448 ->
getr regs 10 = tid ->
getr regs 11 = Z_to_bv 64 954232 ->
getr regs 18 = Z_to_bv 64 822248 ->
getr regs 22 = Z_to_bv 64 0 ->
getr regs 23 = Z_to_bv 64 0 ->
getr regs 24 = Z_to_bv 64 0 ->
getr regs 25 = Z_to_bv 64 0 ->
getr regs 26 = Z_to_bv 64 0 ->
getr regs 27 = Z_to_bv 64 0 ->
(forall regs',
getr regs' 2 = (Z_to_bv 64 (bv_unsigned sp0 - 416)) ->
getr regs' 3 = (Z_to_bv 64 67584) ->
getr regs' 4 = (Z_to_bv 64 822448) ->
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
G (mkst regs' (0x992cc : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 822280) (word_to_le_bytes 4 tid)) (Z_to_bv 64 822400) (word_to_le_bytes 8 (Z_to_bv 64 954232))) (Z_to_bv 64 822368) (word_to_le_bytes 8 (Z_to_bv 64 822368))) (Z_to_bv 64 822256) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822264) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 822272) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
G (mkst regs (0x9973c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 627404))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 954176))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 953560) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953576) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 953568) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 954200) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 954208) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 822464) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 822440) (word_to_le_bytes 8 (Z_to_bv 64 822464))) (Z_to_bv 64 822248) (word_to_le_bytes 8 (Z_to_bv 64 822248))) (Z_to_bv 64 954176) ([Z_to_bv 8 1])) (Z_to_bv 64 822288) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) (only parsing).
Variable G : ltac:(sec_ty2 constr:(SEC_T_tls_c5) 0%nat 0%nat).
Lemma tls_c5 : ltac:(sec_stmt2 constr:(SEC_T_tls_c5) 1%nat 0%nat).
Proof.
intros HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn (ltac:(oF' 0x9973c%Z)) (ltac:(oD' 0x9973c%Z)).
stw (ltac:(oF' 0x99740%Z)) (ltac:(oD' 0x99740%Z)) (Z_to_bv 64 822280) tid ltac:(ok_data).
stw (ltac:(oF' 0x99744%Z)) (ltac:(oD' 0x99744%Z)) (Z_to_bv 64 822400) (Z_to_bv 64 954232) ltac:(ok_data).
stw (ltac:(oF' 0x99748%Z)) (ltac:(oD' 0x99748%Z)) (Z_to_bv 64 822368) (Z_to_bv 64 822368) ltac:(ok_data).
sn (ltac:(oF' 0x9974c%Z)) (ltac:(oD' 0x9974c%Z)).
ld_step (ltac:(oF' 0x99750%Z)) (ltac:(oD' 0x99750%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_e8f28_8) ltac:(apply bytes_le_to_Z_8).
stw (ltac:(oF' 0x99754%Z)) (ltac:(oD' 0x99754%Z)) (Z_to_bv 64 822256) (Z_to_bv 64 822248) ltac:(ok_data).
stw (ltac:(oF' 0x99758%Z)) (ltac:(oD' 0x99758%Z)) (Z_to_bv 64 822264) (Z_to_bv 64 822248) ltac:(ok_data).
stw (ltac:(oF' 0x9975c%Z)) (ltac:(oD' 0x9975c%Z)) (Z_to_bv 64 822272) (Z_to_bv 64 0) ltac:(ok_data).
sn (ltac:(oF' 0x99760%Z)) (ltac:(oD' 0x99760%Z)).
ld_step (ltac:(oF' 0x99768%Z)) (ltac:(oD' 0x99768%Z)) (word_to_le_bytes 8 (Z_to_bv 64 627404)) (Z_to_bv 64 627404) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9976c%Z)) (ltac:(oD' 0x9976c%Z)) (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99770%Z)) (ltac:(oD' 0x99770%Z)) (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99774%Z)) (ltac:(oD' 0x99774%Z)) (word_to_le_bytes 8 (Z_to_bv 64 954176)) (Z_to_bv 64 954176) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99778%Z)) (ltac:(oD' 0x99778%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x9977c%Z)) (ltac:(oD' 0x9977c%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step (ltac:(oF' 0x99780%Z)) (ltac:(oD' 0x99780%Z)) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv (ltac:(oF' 0x99784%Z)) (ltac:(oD' 0x99784%Z)) (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret (ltac:(oF' 0x99788%Z)) (ltac:(oD' 0x99788%Z)) (0x992cc : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.
End SE.
End P.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
