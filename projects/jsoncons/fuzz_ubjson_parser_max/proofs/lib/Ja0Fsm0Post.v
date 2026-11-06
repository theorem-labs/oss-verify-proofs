(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MemSplit Ja0RegionPoisoned Ja0FakeStackGC Ja0Fsm0Core Ja0FakeStackGCC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0Fsm0Post () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0FakeStackGCC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Fsm0Core."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0Fsm0Post."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nil"; "1option"; "2False"; "2eq"; "2or"; "3repeat"; "4Z"; "5word_to_le_bytes"; "0Mg"; "0Mj"; "6gc_postb"; "7core0_mem"; "8fsm0_post"]; ["9rdn"; ":mem_grows"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<pow"; "0col"; "0ff"; "0fs"; "0gb"; "0h"; "0hi"; "0j"; "0lo"; "0mem0"]; ["0pos"; "0s"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation CLS := 0%Z.
Lemma gc_post_nogc_0 : ltac2:(TCodec.tc2 tcn__Ja0Fsm0Post "RH'9'Q3yR0%211'4y8%511%311p051&Ar5r4%3221'7&E&Q4r1%22?1%4218&D%1293%8231'6r7r2%211r8%113%63E31p081pR<K1zr3%>221&C+S1%22I1&F+2+R0%3221%F251%82Q07%H21Dr6+S0%<2Q41%L231%Q3251'2%11Q<%Q?11&@&Br:&Q2%F2<;%22QG1u1%746521(0(1r;%82QJ1(3%11QK%53QL31%72A1%Q>3A91&=r<r9'5q0R91q0R:1%675=E4QAQD1p081p0M1p0Q51p0Q>1p0QB1p0R51pQDRB1pQJRC1pQNRD1pJR=1pR0R>1pQFRG1").
Proof.
intros gb mem0 Mj lo hi fs G O F1 F2 D C. split; [exact G|]. split; [intros x Hx _ _; apply O; exact Hx|]. split; [intros c i _ []|].
rewrite <- C. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply O. lia.
Qed.
Definition fsm0_fp (fs pos ff : Z) (col : Z -> Z -> Prop) (a : Z) : Prop :=
(fs + 0 <= a < fs + 0 + 8)%Z \/ a = (fs + 96)%Z \/ a = gc_fl fs CLS pos \/ (ff + 24 <= a < ff + 32)%Z \/ (ff + 56 <= a < ff + 56 + 8)%Z
\/ (SB + ff / 8 <= a < SB + ff / 8 + 8)%Z
\/ (exists c i, gc_valid c i /\ col c i /\ (a = gc_fl fs c i \/ gc_insh fs c i a)).
Definition fsm0_post (gb : Z) (mem0 Mf : word -> option byte) (lo hi s fs h j pos ff : Z) (col : Z -> Z -> Prop) : Prop :=
mem_grows mem0 Mf
/\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> ~ fsm0_fp fs pos ff col (bv_unsigned x) -> Mf x = mem0 x)
/\ rdn ASEGS Mf (Z_to_bv 64 (fs + 0)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))
/\ rdn ASEGS Mf (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb]
/\ rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs CLS pos)) 1%nat = Some [Z_to_bv 8 1]
/\ (forall c i, gc_valid c i -> col c i -> ~ (c = CLS /\ i = pos) -> rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 0])
/\ rdn ASEGS Mf (Z_to_bv 64 (ff + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 s))
/\ rdn ASEGS Mf (Z_to_bv 64 (ff + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (gc_fl fs CLS pos)))
/\ (forall i, (0 <= i < 8)%Z -> Mf (Z_to_bv 64 (SB + ff / 8 + i)) = Some (Z_to_bv 8 0)).
Section POST0.
Variables mem0 Mg : word -> option byte.
Variables gb lo hi s fs h j pos ff : Z.
Variable col : Z -> Z -> Prop.
Hypothesis GP : gc_postb gb mem0 Mg lo hi fs col.
Hypothesis Hfs : (0x691000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
Hypothesis Happm : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
Hypothesis Hpos : (0 <= pos < 16384)%Z.
Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 0 + 64 * pos)%Z.
#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.
#[local] Ltac pwin e H := let v := eval vm_compute in e in change e with v in H.
#[local] Ltac lens := rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat].
#[local] Ltac side := lens; rewrite ?u64_lit by lia; lia.
#[local] Ltac peel_pt := repeat (rewrite wbytes_outside by side).
#[local] Ltac peel_rd := repeat (rewrite rdn_wbytes_out by side).
#[using="Type"] Lemma le8_zero_p : ltac2:(TCodec.tc2 tcn__Ja0Fsm0Post "A'6'2'Q3y8%211%411&:u8&Q2yR0z%3221%6251&8%62;4%23;18%@3;41").
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.
#[using="GP Hfs Happm Hpos Hff_def"] Theorem core0_desc : ltac2:(TCodec.tc2 tcn__Ja0Fsm0Post "@&?vJvO&>v;vQ1vIvKvMvQ0vH%877654321vNvLvG%?<>=432:987651").
Proof.
unfold fsm0_post. destruct Hfs as [Fs1 Fs2]. pose proof (gc_shz_facts fs Fs1 Fs2 Happm) as (Z1 & Z2 & Z3 & Z4).
assert (Vpos : gc_valid CLS pos) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
assert (Eff : gc_fr fs CLS pos = ff) by (unfold gc_fr; pw (2 ^ (6 + CLS))%Z; rewrite Hff_def; lia).
assert (Efl : gc_fl fs CLS pos = (fs + 4096 + 0 + pos)%Z) by (unfold gc_fl; pw (2 ^ (14 - CLS))%Z; lia).
pose proof (gc_fr_range fs CLS pos Vpos) as [FRR1 FRR2]. rewrite Eff in FRR1, FRR2. pwin (2 ^ (6 + CLS))%Z FRR2.
pose proof (gc_sh_range fs CLS pos Vpos) as [SHR1 SHR2]. unfold gc_sh in SHR1, SHR2. rewrite Eff in SHR1, SHR2. pwin (2 ^ (3 + CLS))%Z SHR2.
destruct GP as (GG & GO & GPc & G96).
assert (FPOS : forall c i, gc_valid c i -> col c i -> ~ (c = CLS /\ i = pos) -> gc_fl fs c i <> (fs + 4096 + 0 + pos)%Z).
{ intros c i Vc Cc NE E. rewrite <- Efl in E. apply (gc_fl_inj fs c i CLS pos Vc Vpos) in E. exact (NE E). }
unfold core0_mem, fsm0_fp. rewrite !Efl.
set (sh := (SB + ff / 8)%Z) in *. clearbody sh. clear Eff Efl Hff_def Happm.
split; [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact GG|].
split.
{ intros x Hx NF. pose proof (u64_range x) as Ux.
assert (N1 : ~ (fs + 0 <= bv_unsigned x < fs + 0 + 8)%Z) by (intros X; apply NF; left; exact X).
assert (N2 : bv_unsigned x <> (fs + 96)%Z) by (intros X; apply NF; right; left; exact X).
assert (N3 : bv_unsigned x <> (fs + 4096 + 0 + pos)%Z) by (intros X; apply NF; right; right; left; exact X).
assert (N4 : ~ (ff + 24 <= bv_unsigned x < ff + 32)%Z) by (intros X; apply NF; right; right; right; left; exact X).
assert (N5 : ~ (ff + 56 <= bv_unsigned x < ff + 56 + 8)%Z) by (intros X; apply NF; right; right; right; right; left; exact X).
assert (N6 : ~ (sh <= bv_unsigned x < sh + 8)%Z) by (intros X; apply NF; right; right; right; right; right; left; exact X).
assert (N7 : forall c i, gc_valid c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)).
{ intros c i Vc Cc. split; intros X; apply NF; do 6 right; exists c, i; (split; [exact Vc | split; [exact Cc|]]); [left | right]; exact X. }
clear NF. peel_pt. apply GO; assumption. }
split. { peel_rd. apply rdn_wbytes_hit8. side. }
split.
{ peel_rd. exact G96. }
split. { peel_rd. apply (rdn_wbytes_hit ASEGS [Z_to_bv 8 1]). side. }
split.
{ intros c i Vc Cc NE. pose proof (FPOS c i Vc Cc NE) as NEQ. pose proof (gc_fl_range fs c i Vc) as FLc. pose proof (GPc c i Vc Cc) as P1.
clear GO GPc FPOS. peel_rd. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) 1). apply MemSplit.rdn_const; [side|].
intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite (word_of_u x (gc_fl fs c i)) by lia. exact P1. }
split. { peel_rd. apply rdn_wbytes_hit8. side. }
split. { peel_rd. apply rdn_wbytes_hit8. side. }
intros i Hi. clear GO GPc FPOS.
assert (D : (0 <= i < 8)%Z) by lia.
decompose [or] D; clear D; peel_pt; (rewrite wbytes_inside by side); rewrite le8_zero_p; f_equal; apply nth_repeat.
Qed.
End POST0.
