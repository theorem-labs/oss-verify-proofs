(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceAJx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__ShadowRLaws () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShadowRLaws.Laws."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0M"; "0M'"; "4S"; "4byte_at"; "4in_shadow_of"; "4shadow_blk"; "5shadow_blkR"; "6shadow_tby"; "7add"]; ["7div"; "7le"; "7lt"; "7modulo"; "0a"; "0i"; "0j"; "0n"; "8Z_to_bv"; "8bv"; "0u"; "0v"]]).
Section Laws.
Variables M M' : word -> option byte.
Definition shadow_tby (u n : Z) : Prop :=
forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u + j) v -> byte_at M' (HeapIfaceA.S u + j) v.
Lemma shadow_blk_tby : ltac2:(TCodec.tc2 tcn__ShadowRLaws "E'6&Bzr1%3221&>r3r2%3221&<v7r4%33216v8r5%63214p041p091p0>1pQ@C1pQFD1").
Proof. intros u n.
intros Hn TBY (Z0 & P0). split.
- intros j Hj. apply TBY; [lia|left; lia|exact (Z0 j Hj)].
- intros Hm. apply TBY; [apply Z.div_pos; lia|right; split; [reflexivity|exact Hm]|exact (P0 Hm)].
Qed.
Lemma shadow_blkR_tby : ltac2:(TCodec.tc2 tcn__ShadowRLaws "E'6&Bzr1%3221&>r3r2%3221&=v7r4%33216v8r5%63214p041p091p0>1pQ@C1pQFD1").
Proof. intros u n.
intros Hn TBY [SB|(H8 & m & Hm & Hm8 & Z0 & F0)].
- left. exact (shadow_blk_tby u n Hn TBY SB).
- right. split; [exact H8|]. exists m. split; [exact Hm|]. split; [exact Hm8|].
assert (MN : m / 8 <= n / 8) by (apply Z.div_le_mono; lia).
assert (M0 : 0 <= m / 8) by (apply Z.div_pos; lia).
split.
+ intros j Hj. apply TBY; [lia|left; lia|exact (Z0 j Hj)].
+ intros j Hj. apply TBY; [lia|left; lia|exact (F0 j Hj)].
Qed.
Lemma shadow_tby_in : ltac2:(TCodec.tc2 tcn__ShadowRLaws "Q<'6&Azr3%3221'2&Cr4+8%3221%53:18&B%12:5%<2;6'5r5&@r6%221:%8241'1%@3E63&4%A26?%C3H1F%311%6251%=281&;r8r7&?&9%114%321A%73651p091p0H1p0J1p0M1p0Q41pQ>Q91pQ@Q:1pQFQ;1").
Proof. intros u n j.
intros Hu H8 Hn Hj0 Hj. unfold in_shadow_of, HeapIfaceA.S.
pose proof (Z.div_mod u 8 ltac:(lia)) as DU. rewrite H8, Z.add_0_r in DU.
pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as RN.
assert (HI : u / 8 + j <= (u + n - 1) / 8) by (apply Z.div_le_lower_bound; lia).
lia.
Qed.
Lemma shadow_blkR_frame : ltac2:(TCodec.tc2 tcn__ShadowRLaws "Q<'6&Azr2%3221'2&Cr3+8%3221%53:18&B%12:5&;r6r5r1%43321'0'Iy8%211%411v8&HyR0%221G%411v7%113%I3831p0>1pQ:Q01&=%136DCr7%33=1Fp031p061p0K1p0N1p0Q51pQ@Q:1pQFQ;1").
Proof. intros u n.
intros Hu H8 Hn AG. apply shadow_blkR_tby; [exact Hn|]. intros j Hj0 Hj v Bt. unfold byte_at in *. rewrite AG; [exact Bt|].
exact (shadow_tby_in u n j Hu H8 Hn Hj0 Hj).
Qed.
Lemma shadow_blk_frame : ltac2:(TCodec.tc2 tcn__ShadowRLaws "Q<'6&Azr2%3221'2&Cr3+8%3221%53:18&B%12:5&;r6r5r1%43321'0'Iy8%211%411v8&HyR0%221G%411v7%113%I3831p0>1pQ:Q01&<%136DCr7%33=1Fp031p061p0K1p0N1p0Q51pQ@Q:1pQFQ;1").
Proof. intros u n.
intros Hu H8 Hn AG. apply shadow_blk_tby; [exact Hn|]. intros j Hj0 Hj v Bt. unfold byte_at in *. rewrite AG; [exact Bt|].
exact (shadow_tby_in u n j Hu H8 Hn Hj0 Hj).
Qed.
End Laws.
Lemma shadow_blkR_bytes : ltac2:(TCodec.tc2 tcn__ShadowRLaws "QG'IyR0%211'0y8%511%311p051'6&Bzr1%3221&=r4r3r2%43321&A%1298'5&@r5+8%3221%@291'1'2%13D<4&4&C%1298%53H1F%411%8261%?2:1'3&:r9&?&9r8%211%421M%7361Q1qQHQ51%:2Q61p0<1p0M1pQ<Q91p0Q11p0Q71pQ@Q<1pQFQ=1p@Q?1").
Proof. intros M u n.
intros Hn [(Z0 & P0)|(H8 & m & Hm & Hm8 & Z0 & F0)] i Hi0 Hi.
- destruct Hi as [Hi|(Ei & Hm')]; [eexists; exact (Z0 i ltac:(lia))|]. rewrite Ei. eexists. exact (P0 Hm').
- destruct Hi as [Hi|(_ & Hm')]; [|contradiction].
destruct (Z_lt_ge_dec i (m / 8)) as [Lo|Hi']; [eexists; exact (Z0 i ltac:(lia))|]. eexists. exact (F0 i ltac:(lia)).
Qed.
