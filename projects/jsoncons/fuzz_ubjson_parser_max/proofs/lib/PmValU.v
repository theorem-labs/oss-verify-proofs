(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep PmParStep PmCertKitG PmValUP PmValUPz.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmValU () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsU.PMU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmValU.PMVAU."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmValU.PMVAU.Loop."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "3Z"; "0IH"; "0KS"]; ["0L"; "4bvmap"; "0M"; "0R"; "0R'"; "0R2"; "5msteps"; "6u8_at"; "7validate_spec"; "8KL"; "9goal_from"; "8VC"; "8vconst"; ":FPState"; ":getr"; ":mkst"]; [":rdn"; ":seg_rom"; ";loaded_segments"; "0S"; "0SCFG_P"; "<eqb"; "=In"; "=existsb"; "=forallb"; ">add"; ">le"; ">lt"; ">of_nat"; ">sub"; ">to_nat"; "0a"]; ["0b"; "0c"; "0c'"; "0d0"; "0e"; "0fx"; "0fx2"; "0k"; "0n"; "0p"; "0pc"; "0pc2"; "?Z_to_bv"; "?bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMVAU.
Import PMU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmValU "I'5'6%211';'3&Q8&Q7&Q5r1%211r2%53:21qS@;1%83<13(9%<3;21&Q6r4%23A:1%33B92p021pS@D1p071pQ0E1p2F1").
Proof. intros A KS.
intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Definition VC : list nat := [2; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%nat.
Definition KL : list nat := [1; 3; 4]%nat.
Ltac kin := apply sub_in; vm_compute; reflexivity.
Definition vconst (R : bvmap 5 word) (S e : Z) : Prop :=
getr R (reg 2) = Z_to_bv 64 (S - 96) /\ getr R (reg 5) = Z_to_bv 64 2 /\ getr R (reg 6) = Z_to_bv 64 (-65) /\ getr R (reg 7) = Z_to_bv 64 239
/\ getr R (reg 8) = Z_to_bv 64 240 /\ getr R (reg 9) = Z_to_bv 64 144 /\ getr R (reg 12) = Z_to_bv 64 e /\ getr R (reg 13) = Z_to_bv 64 8
/\ getr R (reg 14) = Z_to_bv 64 (-1) /\ getr R (reg 15) = Z_to_bv 64 1 /\ getr R (reg 16) = Z_to_bv 64 (-62) /\ getr R (reg 17) = Z_to_bv 64 245
/\ getr R (reg 18) = Z_to_bv 64 244 /\ getr R (reg 19) = Z_to_bv 64 143 /\ getr R (reg 20) = Z_to_bv 64 80065 /\ getr R (reg 21) = Z_to_bv 64 18446744073709471550
/\ getr R (reg 22) = Z_to_bv 64 3 /\ getr R (reg 28) = Z_to_bv 64 224 /\ getr R (reg 29) = Z_to_bv 64 160 /\ getr R (reg 30) = Z_to_bv 64 237
/\ getr R (reg 31) = Z_to_bv 64 159.
Lemma vconst_keep : ltac2:(TCodec.tc2 tcn__PmValU "Q6&Ay5'QMyR0%211%5241'=&Lr4r2r1%43321'6&Q6&K%23351';&Nr6&QL&Q<%11<%32E1%6251r7%8213%:3F31p0<1pS@@1r5r3%H32G1p041p0F1pS:L1pR8M1pQ:O1pQ8Q01").
Proof. intros R R' S e.
intros (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31) K.
unfold vconst. rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.
Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (80065 + Z.of_nat k)) 1 with Some [_] => true | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok : ltac2:(TCodec.tc2 tcn__PmValU "Q='=':&Q:zr1%3221&Q;+X0%2241%8241'<'QMy8%211';'8'5%114%311&Q0&Q2yR0%;11(1%11;q031&QL&Q9+R^V1r3%3221%52:1u1%>4=821(2(4(7%11H%33IQ21%52F1%J3F71qS2L1%Q02M1p0Q21pS@Q<1").
Proof. intros k.
intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (80065 + k)) 1) as [[|b [|]]|]; try discriminate. exists b. reflexivity.
Qed.
Section Loop.
Variable M : word -> option byte.
Variables (S p e : Z).
Hypothesis RO : L5.img_clear M 65536 749856.
Hypothesis DEF : L5.defined M p (e - p).
Hypothesis HS : 140735332483168 <= S <= 2 ^ 47.
Hypothesis Hp : 0 < p.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p <= 2 ^ 26.
Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
exists fx' R', msteps RSEGS (st fx R pc M) (st fx' R' 0x37a68 M) /\ getr R' (reg 2) = Z_to_bv 64 (S - 96) /\ (forall k, In k KL -> getr R' (reg k) = getr R (reg k)).
Lemma byte_at : ltac2:(TCodec.tc2 tcn__PmValU "J'=':&Q:vQIr1%3221&Q;vQD%2241%8241'<z%:218+X0%82:1%>231&G&Q2vBr3%44321@%D261qS2F1%=2G1p0?1pS0I1").
Proof. intros a. intros Ha. apply (PMCG.u8_of_defined RSEGS M a); [lia| lia|]. apply (L5.defined_sub M p (e - p)); [exact DEF| lia| lia]. Qed.
Ltac epi MS KSx V :=
lazymatch type of MS with msteps _ _ (@mkst ?fx2 ?R2 _ _ _) =>
exists fx2, R2; split; [exact MS|]; split; [rewrite (KSx 2%nat) by PMK.inl; exact (proj1 V)|]; intros k Hk; apply KSx; revert k Hk; kin
end.
Ltac split_exit H MS KS HR := destruct H as [MS H]; lazymatch type of H with
| (forall x, _) /\ _ => destruct H as [KS HR]
| _ => rename H into KS; assert (HR : True) by exact I
end.
Lemma join_case : ltac2:(TCodec.tc2 tcn__PmValU "R3'='M&Ay5'QMyR0%211%5241':&Q;r4r1%3221vQD%5231%7231&Lr3vQ3%33216';&N&QL&Q<u:%211%42G1%62A1%62G;%93G21&Jr6r5+VnW4%43321p061p0A1p0F1pS6Q61pQ8Q01pS<Q71&Q:vQI%221;r2%Q42>1%522Q1%Q7221%Q03Q6NQ3uG%K11%M2Q@1%O2D1%O2Q@Q;%Q23Q@21r7+Vnb0%K32J1p041p0;1p0=1p0B1pS6QN1pQ8QH1pS<QO1pNI1pS4R21").
Proof. intros c IH fx R c'.
intros Hpc Hc V R22. pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
cfeed P (PMVAUP.uvaB_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c' | 35%nat => e - c' | 37%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [ PMK.sc | (rewrite Z_to_bv_bv_unsigned; reflexivity) ]).
destruct P as (fx1 & R1 & M1 & _ & FR & _ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
destruct EX as [(MS & KS & _)|(MS & KS & A10 & NE)].
- epi MS KS V.
- rewrite (Z.mod_small (c' + (e - c'))) in NE by lia. replace (c' + (e - c')) with e in NE by lia.
assert (c' < e) by (destruct (Z.eq_dec c' e) as [->|]; [rewrite Z.sub_diag, Z.mod_0_l in NE by lia; lia| lia]).
destruct (IH fx1 R1 c' ltac:(lia) (vconst_keep R R1 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) A10) as (fx2 & R2 & MS2 & SP2 & KS2).
exists fx2, R2. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [exact SP2|]. intros k Hk. rewrite (KS2 k Hk). apply KS. revert k Hk; kin.
Qed.
Ltac get22 H := lazymatch type of H with
| getr _ (PMK.reg 23) = _ /\ _ => constr:(proj1 H)
| getr _ (PMK.reg 23) = _ => constr:(H)
| _ /\ ?B => let H2 := constr:(proj2 H) in get22 H2
end.
Ltac leaf c IH V :=
lazymatch goal with
| H : msteps _ _ (@mkst _ _ (Z_to_bv 64 0x37a68) _ _) /\ _ |- _ =>
let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR; epi MS KS V
| H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x37a40) _ _) /\ _ |- _ =>
let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
let t := get22 HR in let S6 := fresh "S6" in pose proof t as S6;
let fx3 := fresh "fx" in let R3 := fresh "R" in let MS3 := fresh "MS" in let SP3 := fresh "SP" in let KS3 := fresh "KS" in
lazymatch type of S6 with getr _ _ = Z_to_bv 64 ?cv =>
destruct (join_case c IH fx2 R2 cv ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) S6) as (fx3 & R3 & MS3 & SP3 & KS3) end;
exists fx3, R3; split; [eapply msteps_trans; [exact MS| exact MS3]|]; split; [exact SP3|]; intros k Hk; rewrite (KS3 k Hk); apply KS; revert k Hk; kin
end.
Ltac leaves c IH V := repeat (lazymatch goal with H : _ \/ _ |- _ => destruct H as [H|H]; [leaf c IH V|] end); leaf c IH V.
Lemma goal_pre : ltac2:(TCodec.tc2 tcn__PmValU "QG'M&Ay5'QMyR0%211%5241'='F&Q2&Or6r5&QLr4%22;1vB&Q1%119%9587431r3r2r1%:2C1%>543186%A3@61'6&Q6&I%23371';&N&Q<%11<%E2Q01%42G1r8%6213%83Q131p0:1pS@>1&J%13NLFr9r7%43291p041p071p0G1pSHQ:1pQ<Q<1pS>QC1pSFQ=1pQ8Q?1pS<QF1").
Proof. intros fx R pc fx2 R2 pc2.
intros MS KS (fx3 & R3 & MS3 & SP3 & KS3). exists fx3, R3. split; [eapply msteps_trans; [exact MS| exact MS3]|]. split; [exact SP3|].
intros k Hk. rewrite (KS3 k Hk). apply KS. exact Hk.
Qed.
Lemma slow : ltac2:(TCodec.tc2 tcn__PmValU "R0'='M&Ay5'QMyR0%211%5241':&Q;r4r1%3221vQD%5231%7231&Lr3vQ3%33216';&N&QL&Q<u:%211%42G1%62A1%62G;%93G21&Jr6r5+VnW4%43321p061p0A1p0F1pS6Q61pQ8Q01pS<Q71&Q:vQI%221;r2%42>1%Q522Q1%Q7221%Q03Q6NQ3%L2AG%L2Q=Q8%O3Q=21r7+Vn[H%H32G1p041p081p0:1p0?1pS8QK1pQ8QE1pS<QL1pNF1pS4QO1").
Proof. intros c IH fx R d0.
intros Hpc Hd V R10. pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
destruct (byte_at d0 ltac:(lia)) as (s8 & Hs8 & U0).
cfeed P (PMVAUP.uvaS1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & _ & FR & _ & MS1 & KS1 & A11 & A24). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
destruct (table_ok s8 Hs8) as (tb & TB).
assert (L1 : (25%bv : bv 5) <> 0%bv) by discriminate.
assert (L2 : getr R1 (11%bv : bv 5) = Z_to_bv 64 (s8 + 80065)) by exact A11.
assert (L3 : rdn RSEGS M (Z_to_bv 64 (s8 + 80065 + bv_signed (0%bv : bv 12))) 1 = Some [tb]).
{ change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, Z.add_comm. rewrite (PMCG.rdn_img RSEGS M 65536 749856 _ 1 RO) by lia. exact TB. }
pose proof (PMCG.lbu_img_run RSEGS fx1 R1 M 0x37988 (ltac:(oW' 0x37988%Z)) 25%bv 11%bv 0%bv (s8 + 80065) tb (ltac:(oF' 0x37988%Z)) eq_refl (ltac:(oD' 0x37988%Z)) L1 ltac:(lia) ltac:(lia) L2 ltac:(lia)
ltac:(change (bv_signed (0%bv : bv 12)) with 0; lia) L3) as MSl.
set (R2 := regupd R1 25%bv (Z_to_bv 64 (bv_unsigned tb))) in MSl.
assert (RU : forall k, k <> 25%nat -> (k < 32)%nat -> getr R2 (PMK.reg k) = getr R1 (PMK.reg k)).
{ intros k Hk Hk32. unfold R2. replace (25%bv : bv 5) with (PMK.reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
assert (R25 : getr R2 (PMK.reg 25) = Z_to_bv 64 (bv_unsigned tb)).
{ unfold R2. replace (25%bv : bv 5) with (PMK.reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_same_idx. lia. }
pose proof (bv_unsigned_in_range 8 tb) as Htb. change (bv_modulus 8) with 256 in Htb.
assert (V2 : vconst R2 S e).
{ apply (vconst_keep R R2 S e V). intros k Hk. rewrite RU; [apply KS1; revert k Hk; kin| |]; unfold VC in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk. }
assert (R2_10 : getr R2 (PMK.reg 10) = Z_to_bv 64 d0) by (rewrite RU by lia; rewrite (KS1 10%nat) by PMK.inl; exact R10).
assert (R2_24 : getr R2 (PMK.reg 24) = Z_to_bv 64 s8) by (rewrite RU by lia; exact A24).
apply (goal_pre fx R 0x37978 fx1 R2 (0x37988 + 4)).
{ eapply msteps_trans; [exact MS1| exact MSl]. }
{ intros k Hk. rewrite RU; [apply KS1; revert k Hk; kin| |]; unfold KL in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk. }
change (0x37988 + 4) with 0x3798c.
clear MS1 MSl KS1 A11 A24.
pose proof V2 as (D2 & D5 & D6 & D7 & D8 & D9 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D28 & D29 & D30 & D31).
set (t := bv_unsigned tb) in *.
assert (CASES : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ 4 <= t) by lia.
Local Ltac vfeed P := PMK.feed P ltac:(first [ PMK.sc | exact RO ]).
destruct CASES as [Et|[Et|[Et|[Et|Et]]]].
- rewrite Et in R25.
pose proof (PMVAUP.uvaS2_0_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaves c IH V2.
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 1) as [LE|GT].
+ pose proof (PMVAUP.uvaS2_1a_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaf c IH V2.
+ destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1).
pose proof (PMVAUP.uvaS2_1b_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | 39%nat => b1 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaves c IH V2.
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 2) as [LE|GT].
+ pose proof (PMVAUP.uvaS2_2a_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaf c IH V2.
+ destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1). destruct (byte_at (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
pose proof (PMVAUP.uvaS2_2b_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8
| 39%nat => b1 | 40%nat => b2 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaves c IH V2.
- rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 3) as [LE|GT].
+ pose proof (PMVAUP.uvaS2_3a_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaf c IH V2.
+ destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1). destruct (byte_at (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
destruct (byte_at (d0 + 3) ltac:(lia)) as (b3 & Hb3 & U3).
pose proof (PMVAUP.uvaS2_3b_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8
| 39%nat => b1 | 40%nat => b2 | 41%nat => b3 | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaves c IH V2.
- pose proof (PMVAUP.uvaS2_big_conc fx1 R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 36%nat => s8
| 38%nat => t | _ => 0 end)) as P.
cbn beta iota in P. vfeed P.
destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
leaves c IH V2.
Qed.
Ltac get10 H := lazymatch type of H with
| getr _ (PMK.reg 10) = _ /\ _ => constr:(proj1 H)
| getr _ (PMK.reg 10) = _ => constr:(H)
| _ /\ ?B => let H2 := constr:(proj2 H) in get10 H2
end.
Ltac fleaf c IH V R10 :=
lazymatch goal with
| H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x37978) _ _) /\ _ |- _ =>
let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
let A10 := fresh "A10" in
first [ let t := get10 HR in pose proof t as A10 | assert (A10 := eq_trans (KS 10%nat ltac:(PMK.inl)) R10) ];
lazymatch type of A10 with getr _ _ = Z_to_bv 64 ?dv =>
apply (goal_pre _ _ _ fx2 R2 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin));
apply (slow c IH fx2 R2 dv ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) A10) end
| H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x37a40) _ _) /\ _ |- _ =>
let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
let t := get22 HR in let S6 := fresh "S6" in pose proof t as S6;
lazymatch type of S6 with getr _ _ = Z_to_bv 64 ?cv =>
apply (goal_pre _ _ _ fx2 R2 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin));
apply (join_case c IH fx2 R2 cv ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) S6) end
end.
Ltac fleaves c IH V R10 := repeat (lazymatch goal with H : _ \/ _ |- _ => destruct H as [H|H]; [fleaf c IH V R10|] end); fleaf c IH V R10.
Lemma loop_head : ltac2:(TCodec.tc2 tcn__PmValU "QD'6'M&Ay5'QMyR0%211%5241'=';&Q>&Q=vQDr1%3221%511r4%83A21':&Q:vQIr2%3221&Q;%123<%7231&LvQ3%23<1@&Nr5&QL&Q<u:%211%42Q01%7261%62Q0E%M3Q021&Jr7r6+VnW4%43321p061p0A1p0E1p0N1pS4Q81pQ8Q:1pS<QA1pSBQC1").
Proof.
intros n. induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf). intros fx R c Hn' Hc V R10.
assert (IH : forall fx R c', c < c' < e -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0x378e4).
{ intros fx' R' c' Hc' V' R10'. apply (IHn (Z.to_nat (e - c')) ltac:(lia) fx' R' c'); [reflexivity| lia| exact V'| exact R10']. }
pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
destruct (Z_le_gt_dec 8 (e - c)) as [GE|LT].
- destruct (byte_at c ltac:(lia)) as (b0 & Hb0 & U0). destruct (byte_at (c + 1) ltac:(lia)) as (b1 & Hb1 & U1).
destruct (byte_at (c + 2) ltac:(lia)) as (b2 & Hb2 & U2). destruct (byte_at (c + 3) ltac:(lia)) as (b3 & Hb3 & U3).
destruct (byte_at (c + 4) ltac:(lia)) as (b4 & Hb4 & U4). destruct (byte_at (c + 5) ltac:(lia)) as (b5 & Hb5 & U5).
destruct (byte_at (c + 6) ltac:(lia)) as (b6 & Hb6 & U6). destruct (byte_at (c + 7) ltac:(lia)) as (b7 & Hb7 & U7).
cfeed P (PMVAUP.uvaF8_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | 37%nat => b1 | 38%nat => b2
| 39%nat => b3 | 40%nat => b4 | 41%nat => b5 | 42%nat => b6 | 43%nat => b7 | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & _ & FR & _ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
fleaves c IH V R10.
- destruct (byte_at c ltac:(lia)) as (b0 & Hb0 & U0).
cfeed P (PMVAUP.uvaF1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx1 & R1 & M1 & _ & FR & _ & MS & KS & _). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
apply (goal_pre _ _ _ fx1 R1 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin)).
apply (slow c IH fx1 R1 c ltac:(lia) ltac:(lia) (vconst_keep _ R1 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin))).
rewrite (KS 10%nat) by PMK.inl. exact R10.
Qed.
End Loop.
Lemma e6 : ltac2:(TCodec.tc2 tcn__PmValU ":';'QMyR0%211&QL+_oooooooooomO%2241-R1%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e14 : ltac2:(TCodec.tc2 tcn__PmValU ":';'QMyR0%211&QL+_oooooooooooO%2241-1%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Lemma e16 : ltac2:(TCodec.tc2 tcn__PmValU ":';'QMyR0%211&QL+_oooooooooon2%2241-QN%4261%93631"). Proof. apply bv_eq. reflexivity. Qed.
Section Stage.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis LY : PMU.layout L.
Theorem validate_ok : ltac2:(TCodec.tc2 tcn__PmValU "4&HvQ4v@%3221").
Proof.
unfold PMU.validate_spec, PMSP.validate_spec, PMSP.scan_spec.
intros fx R M model K p n sp r Mh Ml K0 ENT A10 A11 Hn Hp0 HpZ Hpn DEF DISJ BASE KONT.
destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
pose proof BASE as (RO & _ & _ & _). cbn [pa_rw_lo AD PmLayoutU.ADDR_U] in RO.
unfold PMSP.cfg. cbn [pa_validate AD PmLayoutU.ADDR_U].
assert (Hsp : 0 <= sp < 2 ^ 64) by lia.
destruct (Z.eq_dec p 0) as [Ep|Ep].
{ subst p. assert (En : n = 0) by (destruct HpZ as [E|E]; [exact E| lia]). subst n.
cfeed P (PMVAUPZ.uvaEz_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) ltac:(first [ PMK.sc | (apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]) ]).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & (MS & KS & E2 & _ & _ & _ & Z96 & Z88 & Z80 & Z72 & Z64 & Z56 & Z48 & Z40 & Z32 & Z24 & Z16 & Z8)).
assert (FB : forall M', (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
L5.frame_but [(sp - (12288 + 2048 * 0), 12288 + 2048 * 0)] M M').
{ intros M' FRZ x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FRZ; [apply (bv_unsigned_in_range 64)|].
intros X. apply (Hx (sp - (12288 + 2048 * 0), 12288 + 2048 * 0)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as V18. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as V19.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as V20. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 21))) as V21.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 22))) as V22. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 23))) as V23.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 24))) as V24. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 25))) as V25.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 26))) as V26. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 27))) as V27.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (WR1 : L5.writable RSEGS M1 (sp - 96) 96).
{ apply (L5.writable_grows RSEGS M M1 _ _ MG1). apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]. }
assert (TAIL : forall fx2 R2, msteps RSEGS (st fx R 0x37844 M) (st fx2 R2 0x37a68 M1) -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 96) ->
(forall k, In k KL -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 8))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 9))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 18))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 19))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 20))) -> L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 21))) ->
L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 22))) -> L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 23))) ->
L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (PMK.reg 24))) -> L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (PMK.reg 25))) ->
L5.u64_at RSEGS M1 (sp - 88) (bv_unsigned (getr R (PMK.reg 26))) -> L5.u64_at RSEGS M1 (sp - 96) (bv_unsigned (getr R (PMK.reg 27))) ->
srealizes RSEGS SCFG (mkCfg (st fx R 0x37844 M) model) K).
{ intros fx2 R2 MS2 SP2 KS2 S8 S16b S24 S32 S40 S48 S56 S64 S72 S80 S88 S96.
cfeed P (PMVAUP.uvaX_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
| 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19)) | 49%nat => bv_unsigned (getr R (PMK.reg 20))
| 50%nat => bv_unsigned (getr R (PMK.reg 21)) | 51%nat => bv_unsigned (getr R (PMK.reg 22)) | 52%nat => bv_unsigned (getr R (PMK.reg 23))
| 53%nat => bv_unsigned (getr R (PMK.reg 24)) | 54%nat => bv_unsigned (getr R (PMK.reg 25)) | 55%nat => bv_unsigned (getr R (PMK.reg 26))
| 56%nat => bv_unsigned (getr R (PMK.reg 27)) | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx3 & R3 & M3 & _ & FR3 & _ & MS3 & KS3 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
assert (EM : M3 = M1) by (apply functional_extensionality; exact FR3). subst M3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| eapply msteps_trans; [exact MS2| exact MS3]|].
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx3 R3 M1 0x37a9c (ltac:(oW' 0x37a9c%Z)) r (ltac:(oF' 0x37a9c%Z)) ltac:(reflexivity) (ltac:(oD' 0x37a9c%Z))); [| exact RA1| exact RA2]|].
{ rewrite (KS3 1%nat) by PMK.inl. rewrite (KS2 1%nat) by PMK.inl. exact Rra. }
apply (KONT fx3 R3 M1).
+ apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite X2, Rsp; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite (KS3 3%nat), (KS2 3%nat) by PMK.inl; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite (KS3 4%nat), (KS2 4%nat) by PMK.inl; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite X8; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X9; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X18; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X19; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X20; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X21; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X22; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X23; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X24; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X25; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X26; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X27; apply Z_to_bv_bv_unsigned|].
destruct Hk.
+ apply FB. exact FRZ1.
+ exact MG1. }
apply (TAIL fx1 R1 MS E2 ltac:(intros k Hk; apply KS; revert k Hk; kin)); assumption. }
assert (Hp : 0 < p) by lia. clear HpZ.
cfeed P (PMVAUP.uvaE_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [ PMK.sc | (apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]) ]).
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
assert (FB : forall M', (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
L5.frame_but [(sp - (12288 + 2048 * 0), 12288 + 2048 * 0)] M M').
{ intros M' FRZ x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FRZ; [apply (bv_unsigned_in_range 64)|].
intros X. apply (Hx (sp - (12288 + 2048 * 0), 12288 + 2048 * 0)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as V18. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as V19.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as V20. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 21))) as V21.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 22))) as V22. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 23))) as V23.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 24))) as V24. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 25))) as V25.
pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 26))) as V26. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 27))) as V27.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (WR1 : L5.writable RSEGS M1 (sp - 96) 96).
{ apply (L5.writable_grows RSEGS M M1 _ _ MG1). apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]. }
assert (TAIL : forall fx2 R2, msteps RSEGS (st fx R 0x37844 M) (st fx2 R2 0x37a68 M1) -> getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 96) ->
(forall k, In k KL -> getr R2 (PMK.reg k) = getr R (PMK.reg k)) ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 8))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 9))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 18))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 19))) ->
L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 20))) -> L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 21))) ->
L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 22))) -> L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 23))) ->
L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (PMK.reg 24))) -> L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (PMK.reg 25))) ->
L5.u64_at RSEGS M1 (sp - 88) (bv_unsigned (getr R (PMK.reg 26))) -> L5.u64_at RSEGS M1 (sp - 96) (bv_unsigned (getr R (PMK.reg 27))) ->
srealizes RSEGS SCFG (mkCfg (st fx R 0x37844 M) model) K).
{ intros fx2 R2 MS2 SP2 KS2 S8 S16b S24 S32 S40 S48 S56 S64 S72 S80 S88 S96.
cfeed P (PMVAUP.uvaX_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
| 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19)) | 49%nat => bv_unsigned (getr R (PMK.reg 20))
| 50%nat => bv_unsigned (getr R (PMK.reg 21)) | 51%nat => bv_unsigned (getr R (PMK.reg 22)) | 52%nat => bv_unsigned (getr R (PMK.reg 23))
| 53%nat => bv_unsigned (getr R (PMK.reg 24)) | 54%nat => bv_unsigned (getr R (PMK.reg 25)) | 55%nat => bv_unsigned (getr R (PMK.reg 26))
| 56%nat => bv_unsigned (getr R (PMK.reg 27)) | _ => 0 end)) ltac:(first [ PMK.sc ]).
destruct P as (fx3 & R3 & M3 & _ & FR3 & _ & MS3 & KS3 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
assert (EM : M3 = M1) by (apply functional_extensionality; exact FR3). subst M3.
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| eapply msteps_trans; [exact MS2| exact MS3]|].
eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx3 R3 M1 0x37a9c (ltac:(oW' 0x37a9c%Z)) r (ltac:(oF' 0x37a9c%Z)) ltac:(reflexivity) (ltac:(oD' 0x37a9c%Z))); [| exact RA1| exact RA2]|].
{ rewrite (KS3 1%nat) by PMK.inl. rewrite (KS2 1%nat) by PMK.inl. exact Rra. }
apply (KONT fx3 R3 M1).
+ apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
destruct Hk as [<-|Hk]; [rewrite X2, Rsp; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite (KS3 3%nat), (KS2 3%nat) by PMK.inl; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite (KS3 4%nat), (KS2 4%nat) by PMK.inl; reflexivity|].
destruct Hk as [<-|Hk]; [rewrite X8; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X9; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X18; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X19; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X20; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X21; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X22; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X23; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X24; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X25; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X26; apply Z_to_bv_bv_unsigned|].
destruct Hk as [<-|Hk]; [rewrite X27; apply Z_to_bv_bv_unsigned|].
destruct Hk.
+ apply FB. exact FRZ1.
+ exact MG1. }
destruct EX as [(MS & KS & E2 & _ & _ & _ & Hn0 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16b & S8)|
(MS & KS & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E28 & E29 & E30 & E31 & Hn0
& S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16b & S8)].
- apply (TAIL fx1 R1 MS E2 ltac:(intros k Hk; apply KS; revert k Hk; kin)); assumption.
- rewrite Z.sub_0_r, Z.mod_small in Hn0 by lia.
assert (RO1 : L5.img_clear M1 65536 749856) by (intros i Hi; rewrite FRZ1 by lia; apply RO; exact Hi).
assert (DEF1 : L5.defined M1 p (p + n - p)).
{ replace (p + n - p) with n by lia. intros i Hi. rewrite FRZ1 by lia. apply DEF. exact Hi. }
assert (V : vconst R1 sp (p + n)).
{ unfold vconst. rewrite e6 in E6. rewrite e14 in E14. rewrite e16 in E16. repeat split; assumption. }
destruct (loop_head M1 sp p (p + n) RO1 DEF1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Z.to_nat n) fx1 R1 p ltac:(lia) ltac:(lia) V
ltac:(rewrite (KS 10%nat) by PMK.inl; exact A10)) as (fx2 & R2 & MS2 & SP2 & KS2).
apply (TAIL fx2 R2 ltac:(eapply msteps_trans; [exact MS| exact MS2]) SP2 ltac:(intros k Hk; rewrite (KS2 k Hk); apply KS; revert k Hk; kin)); assumption.
Qed.
End Stage.
End PMVAU.
