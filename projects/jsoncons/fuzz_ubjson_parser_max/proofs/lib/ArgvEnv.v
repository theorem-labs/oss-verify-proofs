(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ArgvEnv () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArgvEnv.Scaffold."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "3add"; "3mul"; "4lt"; "5nth"; "6Z"; "7nat_to_word"; "7word_le8"; "8entry_stack_image"]; ["9build_stack_bytes"; "9stack_to_mem"; ":argcN"; ":envp_ptr"; ":wmem"; ";cat_argv_ptr"; "<rdn"; "<v_add"; "<v_addi"; "<v_slli"; "=add"; "=le"; "=lt"; "=of_nat"; "=pow"; "0a"]; ["0av"; "0ev"; "0hw"; "0k"; "0n"; "0ph"; "0rnd"; "0segs"; "0sp"; ">Z_to_bv"; ">bv"; ">bv_add"; ">bv_unsigned"; "0uid"]]).
Section Scaffold.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rnd : EntryDraw.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
Lemma sp_lo_num : ltac2:(TCodec.tc2 tcn__ArgvEnv "7&K+SoonPPPPP0&Q<yR0vQ8%3221%6251").
Proof. exact Hsp_lo. Qed.
Lemma sp_hi_num : ltac2:(TCodec.tc2 tcn__ArgvEnv "7&K&Q<yR0vQ8%3221+TPPPPPPPP0%6221").
Proof. exact Hsp_hi. Qed.
Definition argcN : word := len_word av.
Lemma u_argcN : ltac2:(TCodec.tc2 tcn__ArgvEnv "A'7'<&Q<yR0&B%3221&M&1'2'Q:y8%211%411vQ0%7221%911%@3?;1").
Proof.
pose proof (valid_argv_len av Hva).
unfold argcN, len_word. apply u_Z2bv; lia.
Qed.
Lemma bsb_nw : ltac2:(TCodec.tc2 tcn__ArgvEnv "K&L&J&Q<yR0vQ8%3221&M&1'Q:y8%211&@vQ5vQ0vQ1vQ=vQ2vQ6%776>54321%<291%>11%D2@1&N+2+R0%3221%J251").
Proof.
pose proof (bsb_bound ph sp av ev uid hw rnd Hva Hve). pose proof sp_hi_num. lia.
Qed.
Definition envp_ptr : word :=
Z_to_bv 64 (bv_unsigned sp + 8 + 8 * Z.of_nat (length av) + 8).
Lemma envp_ptr_eq : ltac2:(TCodec.tc2 tcn__ArgvEnv "F'7'Q:yR0%211&H&G&Q9&J&Q<vQ8%2281+8%5221%72;1&I&B+3%3221%=251%?218&C%E3B21").
Proof.
pose proof sp_hi_num. pose proof sp_lo_num.
pose proof (valid_argv_len av Hva) as Hlen.
apply bv_eq. unfold envp_ptr, v_addi.
rewrite !Z_to_bv_unsigned.
rewrite v_add_small
by (rewrite u_Z2bv by lia; rewrite v_slli_3 by (rewrite u_argcN; lia);
rewrite u_argcN; lia).
rewrite u_Z2bv by lia.
rewrite v_slli_3 by (rewrite u_argcN; lia).
rewrite u_argcN.
f_equal; lia.
Qed.
Definition wmem : word -> option byte := wrap_mem ph sp av ev uid hw rnd.
Lemma rdn_wmem_stack : ltac2:(TCodec.tc2 tcn__ArgvEnv "QB'Q:yR0%211'3&K&Q<vQ8%2261r2%4281%6231&Jr3%82<1&M%117%5231&N+2+R0%3221%A251'7'5'2y8%J11%311%511&FvQ7&Dr4%44321E&A&?vQ5vQ0vQ1vQ=vQ2vQ6%776Q454321%92Q51%?4>1<Q0%G3A<1p0I1p0Q51pR:Q=1pR0Q?1").
Proof. intros a n Ha Hn. unfold wmem. apply rdn_wrap_stack_above; assumption. Qed.
Lemma read_argc_w : ltac2:(TCodec.tc2 tcn__ArgvEnv "D'7'5'2'Q:y8%211%411%611&FvQ7&DvQ8u8%544321(0&>&B%211%42<1%C3<61").
Proof.
pose proof sp_hi_num.
rewrite rdn_wmem_stack by lia.
apply read_argc. exact bsb_nw.
Qed.
Lemma argv_ptr_bounds_at : ltac2:(TCodec.tc2 tcn__ArgvEnv "Q<'3&:r1&1'2'Q:y8%211%411vQ0%7221%:291'6&K&Q<yR0vQ8%3221&EvQ1r2%345<21%8271%:261&L&J&M&;(4%11F%34F:E1%L2H1%611%82;1+1%:221&N+2+R0%3221%@251%M2B1p0O1pR8Q;1").
Proof.
intros k Hk. apply argv_ptr_bounds; try assumption.
pose proof sp_hi_num. unfold argv_layout_slack. lia.
Qed.
Lemma read_argv_ptr_w : ltac2:(TCodec.tc2 tcn__ArgvEnv "Q9'3&:r1&1'2'Q:y8%211%411vQ0%7221%:291'7'5%116&FvQ7&D&Q;yR0vQ8&=&8u8&9r2%2231%5241%711%;3:91%?4>=17(0&>&EvQ1%24?J1:%411%62M1%J3H81p0L1pR8Q81").
Proof.
intros k Hk. pose proof sp_lo_num. pose proof sp_hi_num.
pose proof (valid_argv_len av Hva) as Hal.
rewrite rdn_wmem_stack by (rewrite word_add_nat; u_norm; lia).
apply read_argv_ptr_k; [ exact Hk | exact bsb_nw ].
Qed.
End Scaffold.
