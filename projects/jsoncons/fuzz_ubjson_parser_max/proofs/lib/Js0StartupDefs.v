(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import StartupTac ArgvEnv RefLayout RefMemcpyLib.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Js0StartupDefs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Js0StartupDefs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2eq"; "3add"; "4le"; "5firstn"; "5skipn"; "6Z"; "0D"]; ["7bytes_le_to_Z"; "8Segment"; "9word_to_le_bytes"; ":at_random_bytes"; ";wbytes"; "<after_last_slash"; "<canary_w"; "<guard_bytes"; "<progname_off"; "<rlw"; "<rnd4"; "<rnd4w"; "=rdn"; ">sub"; "?add"; "?le"]; ["?lt"; "?pow"; "0acc"; "0g"; "0i"; "0j"; "0n"; "0rnd"; "0s"; "0segs"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0v"; "0w0"; "0w4"]]).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}.
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
match s with
| [] => acc
| b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.
Lemma after_last_slash_le : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "G'5'Q;y8%211%411'6';r1r2%3221&Er4r3%33215&:&4%12=5%3251%<251p0:1pR6?1pR:@1pRBB1").
Proof.
induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.
Lemma progname_off_le : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "='5'Q;y8%211%411';&Hr1%211&4%1273%6231pRB81").
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.
Definition rnd4 (rnd : bv 128) (j : nat) : list byte := firstn 4 (skipn j (at_random_bytes rnd)).
Definition rnd4w (rnd : bv 128) (j : nat) : word := Z_to_bv 64 (bytes_le_to_Z (rnd4 rnd j)).
Definition rlw (rnd : bv 128) (j : nat) : word := v_lw (rnd4w rnd j).
Definition guard_bytes (rnd : bv 128) : list byte :=
firstn 1 (word_to_le_bytes 4 (rlw rnd 0)) ++ [Z_to_bv 8 0] ++ sub (word_to_le_bytes 4 (rlw rnd 0)) 2 2
++ word_to_le_bytes 4 (rlw rnd 4).
Definition canary_w (rnd : bv 128) : word := Z_to_bv 64 (bytes_le_to_Z (guard_bytes rnd)).
Lemma rnd4_eq : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "G'Q;yT0%211'6'9'5y8%711%311&<u4&=r1&Cr2%211%53941%83:71&J%1257%@3<31pR<B1pR@D1").
Proof. reflexivity. Qed.
Lemma length_rnd4 : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "H'Q;yT0%211'6';&:r1u4%3221u@%6221'9&4y8%>11&Jr3r2%3221%7251%93A1=p0;1pR<C1pR@E1").
Proof. intros rnd j Hj. unfold rnd4. rewrite length_firstn, length_skipn, length_at_random_bytes. lia. Qed.
Lemma rnd4_val : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "D'Q;yT0%211'6'9'>&@&Jr2r1%3221%511&Q<yR0&K%1276%4231%=3<61pR<?1pR@A1").
Proof.
intros rnd j. unfold rnd4w. symmetry.
pose proof (bytes_le_to_Z_nonneg (rnd4 rnd j)). pose proof (bytes_le_to_Z_bound (rnd4 rnd j)) as Hb.
assert (Hl : (length (rnd4 rnd j) <= 4)%nat).
{ unfold rnd4. rewrite length_firstn. lia. }
assert (2 ^ (8 * Z.of_nat (length (rnd4 rnd j))) <= 2 ^ 32)%Z by (apply Z.pow_le_mono_r; lia).
apply u_Z2bv; lia.
Qed.
Lemma length_word_to_le_bytes : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "@'6'Q;yR0%211'9&4y8%611&Br2r1%3221%7251%93=14pRL;1pR>?1").
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.
Lemma length_guard_bytes : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "?'Q;yT0%211'9'6&4y8%711&Gr1%211%6241u8%:3921pR@<1").
Proof.
intro rnd. unfold guard_bytes, sub. rewrite !length_app, !length_firstn, length_skipn, !length_word_to_le_bytes. reflexivity.
Qed.
Lemma canary_val : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "A'Q;yT0%211'9'>&@&Gr1%211%411&Q<yR0&F%116%4231%<3;61pR@>1").
Proof.
intro rnd. unfold canary_w. symmetry.
pose proof (bytes_le_to_Z_nonneg (guard_bytes rnd)). pose proof (bytes_le_to_Z_bound (guard_bytes rnd)) as Hb.
rewrite length_guard_bytes in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in Hb. apply u_Z2bv; lia.
Qed.
Lemma canary_bytes : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "B'Q;yT0%211'9'5y8%611%311&Bu8&Fr1%211%5241&G%114%=3931pR@?1").
Proof.
intro rnd. unfold canary_w, word_to_le_bytes.
pose proof (canary_val rnd) as Hv. unfold canary_w in Hv. rewrite <- Hv.
rewrite <- (length_guard_bytes rnd) at 1. apply Z_to_le_bytes_lez.
Qed.
Lemma rd_guard_gen : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "RA'5'A%211'Q;yR0%211'8y8%511%311p051%;13'>'9'6&4r3%2291u4%63521&Oz%2216&Q0&Nr4+8%3221&Q1+2+R0%3221%9251%K1F&Lr9&Dr8&Q:r5%22Q41r7%63521+4%D251%72Q91r6%;3521+1%I2:1%<2Q>1(3%>2Q=O(7%11Q>%43Q?31%D3961u8%H4G2B1(1&2&<u1%23QG1F&Mu2%24QJI11%73QK1E%83QL=1%93QM61%;2QK1%QJ3Q6=1p0Q81p0QC1p0QG1p0QH1pR8R01pS0R21pRNR31pQ0R51pRDR>1").
Proof.
intros segs D w0 w4 g L0 L4 Hg0 Hg1.
assert (U : forall k, (0 <= k <= 8)%Z -> bv_unsigned (Z_to_bv 64 (g + k)) = (g + k)%Z) by (intros; apply u_Z2bv; lia).
assert (U0 : bv_unsigned (Z_to_bv 64 g) = g) by (apply u_Z2bv; lia).
assert (A : forall k j z, (0 <= k)%Z -> (k + Z.of_nat j <= 8)%Z -> (z = k + Z.of_nat j)%Z ->
(Z_to_bv 64 (g + k) + nat_to_word j)%bv = Z_to_bv 64 (g + z)).
{ intros k j z Hk Hj ->. rewrite at_nat. unfold at_. rewrite U by lia. f_equal. lia. }
change 8%nat with (1 + (1 + (2 + 4)))%nat.
apply rdn_app.
{ rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U, ?U0; lia).
rewrite rdn_wbytes_out by (rewrite ?U, ?U0, ?L4; lia).
apply (rdn_firstn segs _ 4); [|lia]. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
replace (Z_to_bv 64 g + nat_to_word 1)%bv with (Z_to_bv 64 (g + 1))
by (rewrite at_nat; unfold at_; rewrite U0; reflexivity).
apply rdn_app.
{ apply (rdn_wbytes_hit segs [Z_to_bv 8 0]). cbn [length]. rewrite U; lia. }
rewrite (A 1%Z 1%nat 2%Z) by lia.
apply rdn_app.
{ rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
rewrite rdn_wbytes_out by (rewrite ?U, ?L4; lia).
replace (Z_to_bv 64 (g + 2)) with (at_ (Z_to_bv 64 g) (Z.of_nat 2)) by (unfold at_; rewrite U0; reflexivity).
apply (rdn_sub segs _ 4). 2: lia. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
rewrite (A 2%Z 2%nat 4%Z) by lia.
rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
rewrite <- L4 at 1. apply rdn_wbytes_hit. rewrite U, L4; lia.
Qed.
Lemma rd_guard_at : ltac2:(TCodec.tc2 tcn__Js0StartupDefs "R:'5'A%211'Q;yR0%211'8y8%511%311p051yT0%911'>&Ozr1%3221&Q0&Nr2+8%3221&Q1+2+R0%3221%9251'9%M1E%H11&Lr6&Dr5&Q:r3%22Q11&Bu4&Ir4(0%3221%6251%<3;81+4%L2;1%=2Q<1%928:%<2;1%B3631+1%Q22A1%C2QB1(3%E2QAQ9(7%11QB%43QC31%K3961u8%O4N2I1(1&G%11H%32Q51%Q73Q551p0Q91p0QD1pR8QI1pR@QK1pQ0QN1pRDR71").
Proof.
intros. unfold guard_bytes. apply rd_guard_gen; try assumption; apply length_word_to_le_bytes.
Qed.
Section Defs.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Variable rnd : bv 128.
Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
Definition auxv_w : word :=
Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
Definition argc_w : word := argcN av.
Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
Definition progname_w : word :=
Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
Definition rnd_w : word := at_random_ptr sp0 av ev.
Definition D_libc : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
(Z_to_bv 64 0xc7b90) (word_to_le_bytes 8 envp_w))
(Z_to_bv 64 0xe7ef8) (word_to_le_bytes 8 auxv_w))
(Z_to_bv 64 0xe7f58) (word_to_le_bytes 8 hw))
(Z_to_bv 64 0xe7f20) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
(Z_to_bv 64 0xe7ee8) (word_to_le_bytes 8 pn_w))
(Z_to_bv 64 0xe7ee0) (word_to_le_bytes 8 progname_w).
Definition J_lsm (J : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes
(wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x98414)))
(Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x33bac)).
Definition J_aux (Jf : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
(wbytes Jf aux_base (zeros 304))
(Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))
(Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))
(Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))
(Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))
(Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))
(Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))
(Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))
(Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).
Definition D_tlsA (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0xe7c88) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0xe7c98) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0xe7c90) (word_to_le_bytes 8 (Z_to_bv 64 8)))
(Z_to_bv 64 0xe7f08) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))
(Z_to_bv 64 0xe7f10) (word_to_le_bytes 8 (Z_to_bv 64 8)))
(Z_to_bv 64 0xc7c70) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 0xc7c58) (word_to_le_bytes 8 (Z_to_bv 64 0xc7c70)))
(Z_to_bv 64 0xc7b98) (word_to_le_bytes 8 (Z_to_bv 64 0xc7b98)))
(Z_to_bv 64 0xe7ef0) [Z_to_bv 8 1])
(Z_to_bv 64 0xc7bc0) (word_to_le_bytes 4 (Z_to_bv 64 2)).
Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0xc7bb8) (word_to_le_bytes 4 tid))
(Z_to_bv 64 0xc7c30) (word_to_le_bytes 8 (Z_to_bv 64 0xe7f28)))
(Z_to_bv 64 0xc7c10) (word_to_le_bytes 8 (Z_to_bv 64 0xc7c10)))
(Z_to_bv 64 0xc7ba0) (word_to_le_bytes 8 (Z_to_bv 64 0xc7b98)))
(Z_to_bv 64 0xc7ba8) (word_to_le_bytes 8 (Z_to_bv 64 0xc7b98)))
(Z_to_bv 64 0xc7bb0) (word_to_le_bytes 8 (Z_to_bv 64 0)).
Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
D_tlsB tid (D_tlsA D).
Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
(Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
(Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
(Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
(Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
(Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).
Definition D_ssp (D : word -> option byte) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes D
(Z_to_bv 64 0xe7ed0) (word_to_le_bytes 4 (rlw rnd 0)))
(Z_to_bv 64 0xe7ed4) (word_to_le_bytes 4 (rlw rnd 4)))
(Z_to_bv 64 0xe7ed1) [Z_to_bv 8 0])
(Z_to_bv 64 0xc7c50) (word_to_le_bytes 8 (canary_w rnd)).
Definition D_fd (D : word -> option byte) : word -> option byte :=
wbytes D (Z_to_bv 64 0xb61e0) [Z_to_bv 8 1].
Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).
End Defs.
End FPX_1.
