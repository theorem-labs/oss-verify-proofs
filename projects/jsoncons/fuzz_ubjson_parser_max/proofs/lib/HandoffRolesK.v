(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec AgentLib AsanAcct BackingAlgebra AxSymExec3K AxSymExec3SoundK AxSymRun3K
AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK HandoffBridgeK HandoffLedgerK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__HandoffRolesK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HandoffRolesK."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2not"; "2or"; "3lt"; "4nth"; "5Z"]; ["0E"; "0FS0"; "0FULL"; "0L"; "0LIMIT"; "6Model"; "6m_vmmaps"; "6vm_maps"; "7bvmap"; "0R"; "8a_maps"; "8acs"; "8am_len"; "8amap"; "8e_sp0"; "8img_hi"]; ["8img_lo"; "8no_fog"; "9amap_den"; "9cs_ok"; "9iv_disjoint"; "9seps"; "9uE"; ":ELit"; ":env"; ":expr"; ";AM_DUMMY"; ";rbase"; ";rlen"; ";role"; "0SEGS"; "0SINV"]; ["<In"; "<rev"; "=add"; "=le"; "=lt"; "=modulo"; "=pow"; "=sub"; "0argH"; "0cs"; "0d"; "0i"; "0j"; "0l"; "0model"; "0q"]; [">bv"; ">bv_unsigned"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition AM_DUMMY : amap := {| am_base := ELit 0; am_len := ELit 0; am_kind := KRW |}.
Definition role (cs : acs) (i : nat) : amap := nth i (rev (a_maps cs)) AM_DUMMY.
Definition rbase (E : env) (cs : acs) (i : nat) : Z := uE E (am_base (role cs i)).
Definition rlen (E : env) (cs : acs) (i : nat) : Z := uE E (am_len (role cs i)).
Lemma role_in : ltac2:(TCodec.tc2 tcn__HandoffRolesK "D'K'4&=r1&2'M&Jr2%211%5241%8271&Q@&Q=r3%2217%912%53;21p071pSHA1pSDC1").
Proof. intros cs i Hi. unfold role. apply in_rev. apply nth_In. rewrite length_rev. exact Hi. Qed.
Lemma seps_rev_nth_apart : ltac2:(TCodec.tc2 tcn__HandoffRolesK "QG'3'6'R0yR0%211%4211%611'Q5r1%211&Q@r3%23741&QDz&R1&7r2%23>>1%42@1%7261p091pT0A1'4&=&2r6%22F1%42;1r7%52I1%72>1&;':r4%23<1H%411&Q4&>r5&QAr9%22Q51%54Q641A%64Q7:2B%8221p0:1p0@1p0D1pSJJ1pSHK1pSFQ>1p0N1p0Q<1pSLQ@1").
Proof.
intros l Hs Hpos d i j Hi Hj Hne.
pose proof (hl_seps_nodup l Hs Hpos) as ND. apply NoDup_rev in ND.
assert (Hq : nth i (rev l) d <> nth j (rev l) d).
{ intros Heq. apply Hne. apply (proj1 (NoDup_nth (rev l) d) ND i j); rewrite ?length_rev; assumption. }
pose proof (hl_seps_apart l Hs (nth i (rev l) d) (nth j (rev l) d)) as Hap.
unfold iv_disjoint. unfold BackingAlgebra.B, BackingAlgebra.S in Hap.
apply Hap; [apply in_rev; apply nth_In; rewrite length_rev; assumption | apply in_rev; apply nth_In; rewrite length_rev; assumption | exact Hq].
Qed.
Section Roles.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
Lemma role_den : ltac2:(TCodec.tc2 tcn__HandoffRolesK "QO'Q8'K&Hy5'R0yR0%211%5241'5y8%611%311p061'E'4'Q3vQ>v0vDvQ?vQHvAr6r5r4r3r2%<;;:987654321':'1&Q1&J%11:%311(8%73621'6%12OO&>&QA&G&F%11B%311%5271&Q2r8&Q:%3221%;4<H51&Q=r7%221K%8271%J3A51p0D1p0M1pSHQ;1pSNQ=1pQ6Q?1pQDQE1pSDQL1pQ2QN1").
Proof.
intros E cs R FULL model i HC Hnf. rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf).
rewrite <- map_rev. unfold role. apply map_nth.
Qed.
Lemma role_geo : ltac2:(TCodec.tc2 tcn__HandoffRolesK "S3'Q8'K&Hy5'R0yR0%211%5241'5y8%611%311p061'E'4'Q3vQ>v0vDvQ?vQHvAr6r5r4r3r2%<;;:987654321':'1&Q1&J%11:%311(8%73621&=&2'Mr7%911%4231%62A1'9&QDz&Q<r9r8%3321I%6251'?&QE&Q;%1376N+TP0%4221%M361<%6293%O381>'<&QC&QB%129>&Q0%11Q@%5231&O%11QC%821?%:241&QG&Q6&N%22K1+XPPP0%5221%@2>1%A2Q1H&QF+2+R0%3221%F2D1%Q9261%Q:281%Q;2@1%Q<2L1%Q=2O1%Q>2Q71p0Q@1p0QH1p0R11pSHR?1pSNRA1pQ6RC1pQDRI1pSDS01pQ2S21").
Proof.
intros E cs R FULL model i HC Hnf Hi.
assert (Hin : In (amap_den E (role cs i)) (vm_maps (m_vmmaps model))).
{ rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map. apply role_in. exact Hi. }
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as (P1 & P2 & P3 & P4 & P5).
pose proof (utop_bounds E) as UT.
destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _). pose proof (W _ Hin) as Wq.
unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq.
unfold amap_den in *. cbn [fst snd] in *. unfold rbase, rlen, uE in *.
pose proof (u64_range (edenot E (am_base (role cs i)))). repeat split; try assumption; lia.
Qed.
Lemma role_apart : ltac2:(TCodec.tc2 tcn__HandoffRolesK "R>'Q8'K&Hy5'R0yR0%211%5241'5y8%611%311p061'E'4'Q3vQ>v0vDvQ?vQHvAr7r6r5r4r3%<;;:987654321':'1&Q1&J%11:%311(8%73621&=&2'Mr8%911%4231%62A1r9%=11%8271%:2E1&;%D3Q2IH%211'<&QC&QB&Q;r<r;%3321Q2&Q<%1343Q4%7231%7365Q5%:221%5387Q7%;231%=218%?241p0A1p0E1p0J1p0Q21p0Q;1pSJQI1pSHQJ1pSNQL1pQ6QN1pQDR41pSDR;1pQ2R=1").
Proof.
intros E cs R FULL model i j HC Hnf Hi Hj Hne.
assert (Hlen : length (vm_maps (m_vmmaps model)) = length (a_maps cs)).
{ rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply length_map. }
pose proof (seps_rev_nth_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)
(fun q Hq => proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq))
(amap_den E AM_DUMMY) i j ltac:(rewrite Hlen; exact Hi) ltac:(rewrite Hlen; exact Hj) Hne) as D.
rewrite !(role_den E cs R FULL model _ HC Hnf) in D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
unfold rbase, rlen, uE. exact D.
Qed.
End Roles.
Lemma role_lit : ltac2:(TCodec.tc2 tcn__HandoffRolesK "Q7'Q8'K'4'?':'Q9&L&Q=r3r2%3221%511(Q7r1%211%;3:41'9&QCz%221:&QD&QF+2+R0%3221%52@1%:271&Q<r6r5r4%43321%L3M1Hp071p0C1pQ8Q01pSHQ21pSDQ41pQ2Q61").
Proof. intros E cs i L H HL. unfold rlen, uE. rewrite H. cbn [edenot]. apply u64_lit. exact HL. Qed.
