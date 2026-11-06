(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA L5DefsA JatIfaceLaws JatIfaceInst.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatIfaceLayout () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatIfaceInst."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatIfaceLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1pair"; "1prod"; "2and"; "2not"; "3Z"; "4hl_rt_ro"; "4hl_rt_static"; "5art_C"; "5art_L"; "6art_img_client"; "6art_img_w"; "7as0_layout"; "8In"; "9le"; "9lt"; "0a"]; ["0hi"; "0lo"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Definition art_img_client : list (Z * Z) :=
[(0x10000, 0x134000); (0x136d58, 0x137640); (0x65d350, 0x66ed28); (0x66ed30, 0x66ed78); (0x66ed94, 0x66eda8); (0x66edb0, 0x690238); (0x690240, 0x691000)].
Definition art_img_w : list (Z * Z) :=
[(0x136e40, 0x137140); (0x65d350, 0x66ed28); (0x66ed30, 0x66ed78); (0x66ed94, 0x66eda8); (0x66edb0, 0x690238); (0x690240, 0x691000)].
Lemma art_L_client : ltac2:(TCodec.tc2 tcn__JatIfaceLayout "K'4&<'1%1233(0r3r2%347721&9%83621'2&=r4%2217&>%129:%6231&3&6&8%221?%411p061p0>1pQ0H1pQ2I1pQ4J1").
Proof.
intros lo hi a Hin Ha S. cbn [art_L hl_rt_static] in S. unfold art_static in S. unfold art_img_client in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma art_L_w_not_ro : ltac2:(TCodec.tc2 tcn__JatIfaceLayout "K'4&<'1%1233(0r3r2%347721&:%83621'2&=r4%2217&>%129:%6231&3&5&8%221?%411p061p0>1pQ0H1pQ2I1pQ4J1").
Proof.
intros lo hi a Hin Ha S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. unfold art_img_w in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma art_L_ro_img : ltac2:(TCodec.tc2 tcn__JatIfaceLayout "@'4&5&8r1%3221'2&=+RPP0r2%3221&>+VbTP0%2241%8241p0:1pQ0?1").
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Lemma art_L_static_img : ltac2:(TCodec.tc2 tcn__JatIfaceLayout "@'4&6&8r1%3221'2&=+QV`P0r2%3221&>+VbTP0%2241%8241p0:1pQ0?1").
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
Lemma art_as0_layout : ltac2:(TCodec.tc2 tcn__JatIfaceLayout "4';&8&7%3221").
Proof.
constructor; try reflexivity.
- cbn [art_C art_statics_cells asc_cells]. apply incl_appl. apply incl_refl.
- intros a S. pose proof (art_L_static_img a S). lia.
- exact art_L_ro_img.
- intros a S. pose proof (art_L_static_img a S). lia.
- cbn. lia.
Qed.
