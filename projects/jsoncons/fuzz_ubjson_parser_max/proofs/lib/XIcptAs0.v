(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib MemsetLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import LibSym Ja0RegionPoisoned Ja0AsanMemset Ja0AsanMemcpy Ja0MemsetIcpt Ja0MemcpyIcpt Ja0TlsGetAddr XIcptA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__XIcptAs0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.XIcptA.XIA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4word_to_le_bytes"; "5bvmap"; "0M"; "6kept_ok"; "7SB"]; ["7rt_layout_globs"; "8rdn"; "9keeps_cs"; ":AS0_BLKSLOT"; ":AS0_CELLS"; ":AS0_CTXSLOT"; ":AS0_ENTV"; ":AS0_MCPY"; ":AS0_MSET"; ":AS0_TCELLS"; ":AS0_TLSPC"; ":AS0_TPV"; ":HIGHEND"; ":cells_ok"; ":icpt_copy_spec"; ":icpt_fill_spec"]; [":icpt_tls_spec"; ":shadow_ok"; ":tcells_ok"; ";loaded_segments"; "<In"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=sub"; "0a"; "0fD"; "0kD"; "0lD"; "0mem0"]; ["0n"; "0p"; "0regs"; "0regs'"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0v"; "0w"; "0w0"; "0w1"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
Lemma kept_ok_of_keeps_cs : ltac2:(TCodec.tc2 tcn__XIcptAs0 "@&<y5'QEyR0%211%5241&Br2r1%3221&>r3%2215p041pS891pS6:1").
Proof.
intros regs regs' Hk r Hr0 Hnin. apply Hk.
pose proof (AX2S.ridx_range r) as Hrr.
assert (Hr : AX2.ridx r <> 0%nat).
{ intros X. apply Hr0. rewrite (APSX.reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
{ exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
destruct E as (k & Hink & Hrk). rewrite (APSX.reg_of_ridx r k Hrk).
cbn [In] in Hink. unfold callee_saved.
repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.
Lemma cell_of : ltac2:(TCodec.tc2 tcn__XIcptAs0 "Q?'QEyR0%211'3y8%511%311p051':'2&M&Q3&Dr4%43321&Q4'5%1298%221:(4r3%24=<81r2%446?21%9361<'7'1%11F%I11&Ar6&QDr5%22Q01%54G41E(0&;%62Q4A%22I1%42<1%?3<61p0A1p0L1pS@Q31pSBQ31pRHQ51pLQ71").
Proof. intros M a w v H Hin. unfold XIA.cells_ok in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Lemma shadow_facts : ltac2:(TCodec.tc2 tcn__XIcptAs0 "SD'QEyR0%211'3y8%511%311p051':&Q7+1r1%3221zr3%6221&Q5r4%2214+8%4221&L%=221&Q1r6r5%33219&?&Q6%125:%>231&Q:r7%A219%321H%721@%D291'8'6&QF%12Q7M%Q02H1&Q8%123M%6231'7r<r2%211(0&QD%12Q?Q6%32Q?1%83Q?51p0:1pSHQE1r:%72QH:%211%92QGQ@%;2QG1%@3QG31'9%B3QGQDQB&Q9r9r8%QC221%Q521QJ%521QB%L21QK+7%QO2QM1%Q3231%<2;1+R0%R32:1'1%11R9%R<11&A&Q3r=%C2QKR0%QE2QL1%Q32RD1u8%746521%Q72:Q9%Q<3:21%J2R1R7%QL2R21%Q:2RK1%=4<;17%Q=2@RC%QB3@21%QJ271qSFC1%QM2D1qSDE1%QO2F1p0I1%R02L1%R12Q:1%R22QA1qRLS11%R52S21tRNS3R71tRJS4R>1p0RC1p0RH1p0S01p0S41pS2S91pS4S:1pS0S<1").
Proof.
intros mem0 p n Hn Hp Hpn (HZ & (kD & HL & HkD) & HD) fD lD.
assert (Dv1 : 0 <= p / 8) by (apply Z.div_pos; lia).
assert (Dv2 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Dv3 : (p + n - 1) / 8 <= XIA.HIGHEND) by (apply Z.div_le_upper_bound; unfold XIA.HIGHEND in *; lia).
assert (EfD : fD = XIA.SB + p / 8) by reflexivity. assert (ElD : lD = XIA.SB + (p + n - 1) / 8) by reflexivity.
pose proof (Z.mod_pos_bound fD 8 ltac:(lia)) as MfD. pose proof (Z.mod_pos_bound lD 8 ltac:(lia)) as MlD.
pose proof (Z.div_mod fD 8 ltac:(lia)) as DfD. pose proof (Z.div_mod lD 8 ltac:(lia)) as DlD.
assert (RNG : 2 ^ 20 <= fD /\ fD <= lD /\ lD + 8 < 2 ^ 64) by (unfold XIA.SB, XIA.HIGHEND in *; lia).
exists kD. split; [intros x Hx; apply HZ; lia|]. split; [exact HL|]. split; [exact HkD|].
intros Hn64. specialize (HD Hn64). fold fD lD in HD. rewrite <- EfD, <- ElD in HD.
assert (RD8 : forall a, 8 * (fD / 8) <= a -> a + 8 <= 8 * (lD / 8) + 8 -> exists w, rdn ASEGS mem0 (Z_to_bv 64 a) 8%nat = Some w).
{ intros a Ha1 Ha2.
destruct (AX2S.rdn_defined ASEGS mem0 8%nat (Z_to_bv 64 a)) as (bs & Hbs & _).
- rewrite u64_of_Z by lia. cbn. lia.
- intros j Hj. rewrite u64_of_Z by lia. unfold AX2S.rd1.
destruct (mem0 (Z_to_bv 64 (a + Z.of_nat j))) eqn:Hm; [discriminate|]. exfalso.
refine (HD (Z_to_bv 64 (a + Z.of_nat j)) _ Hm). rewrite u64_of_Z by lia. lia.
- exists bs. exact Hbs. }
destruct (RD8 (fD - fD mod 8) ltac:(lia) ltac:(lia)) as (w0 & W0). destruct (RD8 (lD - lD mod 8) ltac:(lia) ltac:(lia)) as (w1 & W1).
exists w0, w1. split; assumption.
Qed.
Lemma layout_of_cells : ltac2:(TCodec.tc2 tcn__XIcptAs0 "B'QEyR0%211'3y8%511%311p051&M&Q3&Dr1%43321&@r2%211p041pS0:1").
Proof.
intros mem0 Hcells. unfold rt_layout_globs. repeat split;
match goal with |- rdn _ _ ?a ?w = Some (word_to_le_bytes _ (Z_to_bv 64 ?v)) =>
replace a with (Z_to_bv 64 (bv_unsigned a)) by (apply Z_to_bv_bv_unsigned); apply (cell_of mem0 _ w v Hcells); in_list end.
Qed.
Theorem as0_icpt_fill : ltac2:(TCodec.tc2 tcn__XIcptAs0 "5&O&Q3&H&D%43321").
Proof.
intros fx mem0 c pd n sp regs ret Hn Happ Hs Hs' Hsh Hdj Hok Hdst Hcells Hshz Hret H1 H2 H10 H11 H12.
unfold XIA.SCR in *.
assert (Hpd : 0 <= pd /\ pd + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
destruct (shadow_facts mem0 pd n ltac:(lia) ltac:(lia) ltac:(lia) Hshz) as (kD & HZD & HLD & HkD & HWD).
set (fD := Ja0RegionPoisoned.SB + pd / 8) in *. set (lD := Ja0RegionPoisoned.SB + (pd + n - 1) / 8) in *.
assert (ElD : lD = XIA.SB + (pd + n - 1) / 8) by reflexivity.
destruct (@wrap_memset_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret c pd n sp kD fD lD (fD - fD mod 8) (lD - lD mod 8)) with (regs := regs)
as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
- apply u64_of_Z. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- exact Happ.
- lia.
- lia.
- lia.
- apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 2560)) _ 2560%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
- exact Hdst.
- exact Hret.
- apply layout_of_cells. exact Hcells.
- unfold ms_icpt_globs. repeat split.
+ replace (0x1331a0%bv : word) with (Z_to_bv 64 0x1331a0) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x13b9d9 Hcells). in_list.
+ replace (0x13b9d9%bv : word) with (Z_to_bv 64 0x13b9d9) by (apply bv_eq; reflexivity).
rewrite (cell_of mem0 0x13b9d9 1%nat 1 Hcells) by in_list. reflexivity.
+ replace (0x134648%bv : word) with (Z_to_bv 64 0x134648) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x124db0 Hcells). in_list.
- intros _ x Hx. apply HZD. exact Hx.
- intros _. exact HLD.
- exact HkD.
- intros [_ Hn64]. exact (HWD Hn64).
- exact H10.
- exact H11.
- exact H12.
- rewrite H2. reflexivity.
- exact H1.
- exists regs', Mj. split.
+ replace (Z_to_bv 64 XIA.AS0_MSET) with (0x77330%bv : word) by (apply bv_eq; reflexivity). exact RUN.
+ split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
intros x Hx. apply OUT. lia.
Qed.
Theorem as0_icpt_copy : ltac2:(TCodec.tc2 tcn__XIcptAs0 "5&N&Q3&G&D%43321").
Proof.
intros fx mem0 pd ps n sp bs regs ret Hn Hlbs HappD HappS Hs Hs' HshD HshS HdjD HdjS Hover Hok Hdst Hsrc Hcells HshzD HshzS Hret H1 H2 H10 H11 H12.
unfold XIA.SCR in *.
assert (Hpd : 0 <= pd /\ pd + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
assert (Hps : 0 <= ps /\ ps + n + 8 <= XIA.HIGHEND) by (unfold XIA.app8, XIA.LOWEND, XIA.HIGHBEG, XIA.HIGHEND in *; lia).
destruct (shadow_facts mem0 pd n ltac:(lia) ltac:(lia) ltac:(lia) HshzD) as (kD & HZD & HLD & HkD & HWD).
destruct (shadow_facts mem0 ps n ltac:(lia) ltac:(lia) ltac:(lia) HshzS) as (kS & HZS & HLS & HkS & HWS).
set (fD := Ja0RegionPoisoned.SB + pd / 8) in *. set (lD := Ja0RegionPoisoned.SB + (pd + n - 1) / 8) in *.
set (fS := Ja0RegionPoisoned.SB + ps / 8) in *. set (lS := Ja0RegionPoisoned.SB + (ps + n - 1) / 8) in *.
assert (ElD : lD = XIA.SB + (pd + n - 1) / 8) by reflexivity. assert (ElS : lS = XIA.SB + (ps + n - 1) / 8) by reflexivity.
destruct (@wrap_memcpy_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret pd ps n sp bs kS fS lS (fS - fS mod 8) (lS - lS mod 8) kD fD lD (fD - fD mod 8) (lD - lD mod 8))
with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OUT & GR).
- apply u64_of_Z. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- lia.
- exact HappS.
- exact HappD.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 2560)) _ 2560%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
- exact Hdst.
- exact Hsrc.
- exact Hret.
- apply layout_of_cells. exact Hcells.
- unfold mc_icpt_globs. repeat split.
+ replace (0x1331a0%bv : word) with (Z_to_bv 64 0x1331a0) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x13b9d9 Hcells). in_list.
+ replace (0x13b9d9%bv : word) with (Z_to_bv 64 0x13b9d9) by (apply bv_eq; reflexivity).
rewrite (cell_of mem0 0x13b9d9 1%nat 1 Hcells) by in_list. reflexivity.
+ replace (0x134640%bv : word) with (Z_to_bv 64 0x134640) by (apply bv_eq; reflexivity). apply (cell_of mem0 _ 8%nat 0x1249ac Hcells). in_list.
- intros _ x Hx. apply HZS. exact Hx.
- intros _. exact HLS.
- exact HkS.
- intros [_ Hn64]. exact (HWS Hn64).
- intros _ x Hx. apply HZD. exact Hx.
- intros _. exact HLD.
- exact HkD.
- intros [_ Hn64]. exact (HWD Hn64).
- exact H10.
- exact H11.
- exact H12.
- rewrite H2. reflexivity.
- exact H1.
- exists regs', Mj. split.
+ replace (Z_to_bv 64 XIA.AS0_MCPY) with (0x77338%bv : word) by (apply bv_eq; reflexivity). exact RUN.
+ split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
intros x Hx. apply OUT. lia.
Qed.
Lemma tcell_of : ltac2:(TCodec.tc2 tcn__XIcptAs0 "Q?'QEyR0%211'3y8%511%311p051':'2&Q2&Q3&Ir4%43321&Q4'5%1298%221:(4r3%24=<81r2%446?21%9361<'7'1%11F%I11&Ar6&QDr5%22Q01%54G41E(0&;%62Q4A%22I1%42<1%?3<61p0A1p0L1pS@Q31pSBQ31pRHQ51pLQ71").
Proof. intros M a w v H Hin. unfold XIA.tcells_ok in H. rewrite Forall_forall in H. exact (H _ Hin). Qed.
Theorem as0_icpt_tls : ltac2:(TCodec.tc2 tcn__XIcptAs0 "9&Q0&Q3&J&I&K&F&E&C%877654321").
Proof.
intros fx mem0 d off ctx th tbv tev blk rec sp regs ret Hs Hs' Hd Hd' Hoff Hctx Hctx' Hth Hth' Htb Hte Hblk Hblk' Hrec Hok Htc
Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 A1 A2 A3 A4 Hret H1 H2 H4 H10.
unfold XIA.SCRT, XIA.apartZ, XIA.u64cell in *.
assert (TR : forall (M' : word -> option byte), (forall x : word, bv_unsigned x < sp - 176 \/ sp <= bv_unsigned x -> M' x = mem0 x) ->
forall a (w : nat) bs, 0 <= a < 2 ^ 64 -> a + Z.of_nat w <= 2 ^ 64 -> (a + Z.of_nat w <= sp - 512 \/ sp <= a) ->
rdn ASEGS mem0 (Z_to_bv 64 a) w = Some bs -> rdn ASEGS M' (Z_to_bv 64 a) w = Some bs).
{ intros M' HM a w bs Ha Haw Hap Hr. rewrite <- Hr. apply rdn_ext; [rewrite u64_of_Z by lia; lia|].
intros x Hx. rewrite u64_of_Z in Hx by lia. apply HM. lia. }
destruct (@wrap_tls_get_addr_run fx mem0 (seg_rom ASEGS) (Z_to_bv 64 sp) ret sp XIA.AS0_TPV d 1 off 0x66eda0 XIA.AS0_ENTV 0 0x690238 ctx th tbv tev 0x1cc828 0x1ca798 0 8 blk rec)
with (regs := regs) as (regs' & Mj & RUN & Q10 & Q2' & Q1' & KCS & OUT & GR).
- apply u64_of_Z. lia.
- exact Hret.
- lia.
- apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (sp - 512)) _ 512%nat); [rewrite !u64_of_Z by lia; lia | exact Hok | rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; cbn; lia].
- unfold XIA.AS0_TPV. lia.
- lia.
- lia.
- lia.
- lia.
- unfold XIA.AS0_ENTV. lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- lia.
- unfold XIA.AS0_TPV. lia.
- lia.
- lia.
- intros M' HM. specialize (TR M' HM). unfold tls_cells, XIA.AS0_TPV, XIA.AS0_ENTV.
repeat split.
+ replace (0x13b9d8%bv : word) with (Z_to_bv 64 0x13b9d8) by (apply bv_eq; reflexivity).
apply (TR 0x13b9d8 1%nat); [lia | cbn; lia | cbn; lia |]. rewrite (tcell_of mem0 0x13b9d8 1%nat 1 Htc) by in_list. reflexivity.
+ replace (0x134538%bv : word) with (Z_to_bv 64 0x134538) by (apply bv_eq; reflexivity).
apply (TR 0x134538 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x125990 Htc). in_list.
+ apply (TR d 8%nat); [lia | cbn; lia | cbn; lia | exact Q1].
+ apply (TR (d + 8) 8%nat); [lia | cbn; lia | cbn; lia | exact Q2].
+ apply (TR (0x66ed80 - 8) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x66ed78 8%nat 0x66eda0 Htc). in_list.
+ apply (TR (0x66eda0 + 8 * 1) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x66eda8 8%nat 0x66f580 Htc). in_list.
+ replace (0x13a560%bv : word) with (Z_to_bv 64 0x13a560) by (apply bv_eq; reflexivity).
apply (TR 0x13a560 1%nat); [lia | cbn; lia | cbn; lia |]. rewrite (tcell_of mem0 0x13a560 1%nat 1 Htc) by in_list. reflexivity.
+ replace (0x13a564%bv : word) with (Z_to_bv 64 0x13a564) by (apply bv_eq; reflexivity).
apply (TR 0x13a564 4%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x13a564 4%nat 0 Htc). in_list.
+ apply (TR (0x66ed80 - 88) 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x66ed28 8%nat 0x690238 Htc). in_list.
+ apply (TR (0x690238 + 8 * 0) 8%nat); [lia | cbn; lia | cbn; lia |]. exact Q3.
+ apply (TR (ctx + 152) 8%nat); [lia | cbn; lia | cbn; lia | exact Q4].
+ apply (TR (th + 48) 8%nat); [lia | cbn; lia | cbn; lia | exact Q5].
+ apply (TR (th + 56) 8%nat); [lia | cbn; lia | cbn; lia | exact Q6].
+ replace (0x132628%bv : word) with (Z_to_bv 64 0x132628) by (apply bv_eq; reflexivity).
apply (TR 0x132628 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x1cc828 Htc). in_list.
+ apply (TR (0x1cc828 + 137) 1%nat); [lia | cbn; lia | cbn; lia |]. change (0x1cc828 + 137) with 0x1cc8b1. rewrite (tcell_of mem0 0x1cc8b1 1%nat 1 Htc) by in_list. reflexivity.
+ replace (0x132688%bv : word) with (Z_to_bv 64 0x132688) by (apply bv_eq; reflexivity).
apply (TR 0x132688 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 0x1ca798 Htc). in_list.
+ apply (TR 0x1ca798 4%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 0x1ca798 4%nat 0 Htc). in_list.
+ replace (0x133440%bv : word) with (Z_to_bv 64 0x133440) by (apply bv_eq; reflexivity).
apply (TR 0x133440 8%nat); [lia | cbn; lia | cbn; lia |]. apply (tcell_of mem0 _ 8%nat 8 Htc). in_list.
+ apply (TR (8 + 0x66ed80) 8%nat); [lia | cbn; lia | cbn; lia |]. exact Q7.
+ apply (TR (blk + 16 * 1 + 8) 8%nat); [lia | cbn; lia | cbn; lia |]. replace (blk + 16 * 1 + 8) with (blk + 24) by lia. exact Q8.
- exact H10.
- exact H4.
- rewrite H2. reflexivity.
- exact H1.
- exists regs', Mj. split.
+ replace (Z_to_bv 64 XIA.AS0_TLSPC) with (0x62a98%bv : word) by (apply bv_eq; reflexivity). exact RUN.
+ split; [apply kept_ok_of_keeps_cs; exact KCS|]. split; [exact Q10|]. split; [|exact GR].
intros x Hx. apply OUT. lia.
Qed.
