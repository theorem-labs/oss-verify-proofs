(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem JatCls JatCellEx JatDepot ArtBridge JatInv JatInvMalloc JatLift JatWrapKit
JatFsInv JatFsInvLaws JatIfaceLaws JatWrapC JatWrapVis JatWrapC2 JatIfaceFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatSmallocKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFsInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0BASE"; "0BUDGET"; "1None"; "1Some"; "1list"; "1nat"; "1option"; "1prod"; "2and"; "2eq"; "2not"; "3Z"; "0G"; "0LB"; "4word_to_le_bytes"]; ["5Model"; "0M"; "0MAPS0"; "0Mr"; "0NOACC0"; "0RESV0"; "6BInv"; "7FS_BYTES"; "7S"; "7ar_fs"; "8art_fsg"; "9art_alloc_rep"; "9art_alloc_zone"; "9art_gs"; "9art_kn_ok"; "9g_log"]; ["9rn_HI"; "9rn_ar"; ":rdn"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<of_nat"; "<pow"; "<sub"; "0a"; "0model"; "0n"; "0rn"; "=Z_to_bv"; "=bv"]; ["=bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_rdn_none_img : ltac2:(TCodec.tc2 tcn__JatSmallocKit "QN'Q?yR0%211'7y8%511%311p051'<'6&Q5zr2%3221&Q4r3&Q7%115%4231&Q8+2+R0%3221%=251'9r5&Q@r1%22K1%C241&Q6r4%@11%C281%4261%;261':r7%11J(3%11Q3%53Q331p071pS4Q91'5%11Q8%Q;11&Q2&Q3r6&Q>%12QBJ%54431Eq0QC=%74613G%C3931p0=1p0Q21p0Q=1pRJQB1pRFQD1pQ4QF1").
Proof.
intros M a n Ha Hn N. destruct n as [|n]; [reflexivity|]. apply rdn_ext.
- rewrite art_u_lit by lia. lia.
- intros x Hx. rewrite art_u_lit in Hx by lia. apply N. exact Hx.
Qed.
Lemma art_desc_md : ltac2:(TCodec.tc2 tcn__JatSmallocKit "K':'7'5'Q?y8%211%411%611&Q2&Q3yR0%811(3%118q031&Q>+QV]Q@%2271u8%;4:521(4&?+1%82=1%3261%52C1%J3C71").
Proof. vm_compute. first [reflexivity | f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. Qed.
Lemma art_desc_off : ltac2:(TCodec.tc2 tcn__JatSmallocKit "Q4':'7'5'Q?y8%211%411%611&Q2&Q3yR0%811(3%118q031&Q>&Q4+QV]Q@+8%3221%52:1u8%>4=821(4&?&Q9&Q8+2+R0%3221+RP0%6221%A2F1%92<1%;2L1%Q33L=1").
Proof. vm_compute. first [reflexivity | f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity]. Qed.
Section Kit.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).
#[using="Type"] Lemma art_zone_off_fs_shadow : ltac2:(TCodec.tc2 tcn__JatSmallocKit "R8'M'J%211'5'8'<%2211%411'Q?yR0%211'7y8%511%311p051'@&KvQ=r7r6r3%55E4321&NvBvE%33218'F&Q3vD&Q0%11=v1v2&Or9%22Q31r4%;;:>=97652CB1&Lr:%24Q8G14&;'9&Q5&H&I&Q1%11N%311%511r5%8221&Q6&Q4&G%2271%<11%5271%@271%B11p0D1p0H1p0Q51p0Q:1pS4QL1pRHQB1pQ8QD1pQ4QE1p2QN1pNQO1pLR51").
Proof.
intros G LB A M Mr model x REP KN B0 Z X. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
destruct Fapp as (Fa0 & Fap & Fa47). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
assert (SR : 0x7fff8000 <= x < 0x10007fff8000).
{ pose proof (art_S_lo (ar_fs (rn_ar rn)) Fa0). assert ((ar_fs (rn_ar rn) + FS_BYTES) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - X H H0. lia. }
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart, FS_BYTES in *.
destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
- unfold art_zone_statics in Z. clear - Z SR. lia.
- unfold art_zone_thread in Z. clear - Z SR G10. lia.
- clear - Z SR G16. lia.
- unfold art_zone_kspace in Z. clear - Z SR Khi. lia.
- destruct Z as [Z | (p & Hp & Z)]; [clear - Z SR Papp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & _). clear - Z SR L4. lia.
- unfold art_zone_depot, dprivD in Z. clear - Z SR Al2s Abs. lia.
- destruct Z as [Z | (p & Hp & Z)].
+ destruct Afkb as [AF | AF].
* pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
* pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
+ destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
specialize (L5 (ar_fs (rn_ar rn), 11571200) ltac:(unfold art_objs; do 6 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5.
destruct L5 as [AF | AF].
* pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
* pose proof (art_S_mono _ _ AF). clear - Z X H. lia.
- clear - Z SR. lia.
- clear - Z SR G20. lia.
- clear - Z SR G22 Hkey. lia.
- clear - Z SR. lia.
- clear - Z SR. lia.
Qed.
End Kit.
