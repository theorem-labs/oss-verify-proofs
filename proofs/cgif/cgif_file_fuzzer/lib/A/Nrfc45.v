(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08 YI59.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACey ACev Nrfc6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac rebaseH HS AG :=
lazymatch type of HS with st_ok _ ?Enew _ _ =>
let Ev := fresh "E" in let HEv := fresh "HE" in
remember Enew as Ev eqn:HEv in HS;
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
let AG2 := fresh "AG" in
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac oblH RA EQx E22x :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?q ?c)) _ =>
rewrite (U_atom_off Ex q _ c ltac:(enorm; agnorm; exact EQx)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 22 SB ltac:(enorm; agnorm; exact E22x)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac rregS HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_restrict_reg segs H E ss ms r HS))
end.
Lemma lor_hl8 : forall vh vl, 0 <= vh -> 0 <= vl < 256 -> Z.lor (vh * 256) vl = vl + 256 * vh.
Proof.
intros vh vl Hh Hl.
assert (E1 : vl = Z.land vl (Z.ones 8)) by (rewrite Z.land_ones by lia; rewrite Z.mod_small by (change (2 ^ 8) with 256; lia); reflexivity).
assert (E2 : Z.land (vh * 256) vl = 0).
{ rewrite E1, (Z.land_comm vl (Z.ones 8)), Z.land_assoc, (Z.land_ones (vh * 256) 8) by lia. change (2 ^ 8) with 256. rewrite Z.mod_mul by lia. apply Z.land_0_l. }
pose proof (Z.add_lor_land (vh * 256) vl) as AL. lia.
Qed.
Lemma U_hl8 : forall E h l vh vl, ew E h = Z_to_bv 64 vh -> ew E l = Z_to_bv 64 vl -> 0 <= vh < 256 -> 0 <= vl < 256 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff h 0)) (SLit 8)) (SExt false 8 (SOff l 0))) = vl + 256 * vh.
Proof.
intros E h l vh vl Hh Hl Rh Rl. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SExt, U_SLit, (U_atom E h vh Hh), (U_atom E l vl Hl) by lia. cbn [Z.of_N].
change (2 ^ 8) with 256. rewrite (Z.mod_small vh 256), (Z.mod_small vl 256) by lia.
rewrite (zcanon_id vh), (zcanon_id 8), (zcanon_id vl) by (unfold M64; lia).
change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (vh * 256)) by (unfold M64; lia).
rewrite lor_hl8 by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_hl8_hi : forall E h l vh vl, ew E h = Z_to_bv 64 vh -> ew E l = Z_to_bv 64 vl -> 0 <= vh < 256 -> 0 <= vl < 256 ->
U E (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff h 0)) (SLit 8)) (SExt false 8 (SOff l 0))) (SLit 8)) = vh.
Proof.
intros E h l vh vl Hh Hl Rh Rl. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_hl8 E h l vh vl Hh Hl Rh Rl), U_SLit.
rewrite (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace (vl + 256 * vh) with (vl + vh * 256) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia.
apply zcanon_id. unfold M64; lia.
Qed.
Lemma field1_of_region : forall E m n b cs lo hi wlo whi od e v,
region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem tfibsegs m (b + od) 1 (v mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He Hv k Hk.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
assert (Hk0 : k = 0%nat) by lia. subst k.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite He in Hb1. unfold YP09.byte_of_word in Hb1. injection Hb1 as <-.
cbn [Z.of_nat]. rewrite Z.add_0_r in Hb2 |- *. rewrite Hb2. f_equal.
rewrite unsigned_lit_small by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma U_attr_bit : forall E n fattr, ew E n = Z_to_bv 64 fattr -> 0 <= fattr < 2 ^ 32 ->
U E (SAlu ALU_AND (SExt false 8 (SOff n 0)) (SLit 1)) = Z.land fattr 1.
Proof.
intros E n fattr Hn Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit, (U_atom E n fattr Hn) by lia. cbn [Z.of_N].
change (2 ^ 8) with 256. pose proof (Z.mod_pos_bound fattr 256 ltac:(lia)) as Hm.
rewrite (zcanon_id (fattr mod 256)) by (unfold M64; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
assert (L1 : forall x, 0 <= x -> Z.land x 1 = x mod 2) by (intros x Hx; change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
rewrite !L1 by lia. rewrite zcanon_id by (unfold M64; pose proof (Z.mod_pos_bound (fattr mod 256) 2 ltac:(lia)); lia).
apply Z.mod_mod_divide. exists 128. reflexivity.
Qed.
Lemma lor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lor x (2 ^ 64 - 1) = 2 ^ 64 - 1.
Proof.
intros x Hx. replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
apply Z.lor_ones_low; [lia|]. destruct (Z.eq_dec x 0) as [->|Hx0]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.
Lemma or5_m1 : forall a b c, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
alu64 ALU_OR (alu64 ALU_OR (alu64 ALU_OR (Z_to_bv 64 a) (Z_to_bv 64 b)) (alu64 ALU_OR (Z_to_bv 64 c) (Z_to_bv 64 (2 ^ 64 - 1)))) (Z_to_bv 64 (2 ^ 64 - 1)) = Z_to_bv 64 (2 ^ 64 - 1).
Proof.
intros a b c Ha Hb Hc. rewrite (rfcJ_alu_or_lits a b), (rfcJ_alu_or_lits c (2 ^ 64 - 1)) by lia.
rewrite (rfcJ_alu_or_lits (Z.lor a b) (Z.lor c (2 ^ 64 - 1))) by (apply Z_lor_bound; lia).
rewrite (rfcJ_alu_or_lits (Z.lor (Z.lor a b) (Z.lor c (2 ^ 64 - 1))) (2 ^ 64 - 1)) by (try apply Z_lor_bound; try apply Z_lor_bound; lia).
rewrite lor_m1; [reflexivity|]. apply Z_lor_bound; [lia | apply Z_lor_bound; lia | apply Z_lor_bound; lia].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section RC.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_C3_ok : RFC_J_stmt B MT -> RFC_C3_stmt B MT.
Proof.
intros RJ.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 regs1 mem1 md1 r1 r2 r3 cur2 cur3 fattr fgen delay T P
RC HPL HJ1 HH3 HRC HFR HM RAdst1 KEPT1 HIO1.
pose proof RC as ((HMOK & HCOST & HlenP) & HPerm & Hpd & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hown & HfinC & Hcid & Hfal & Hst1 & Hst2 & Hdst1 & Hdst2 & Hsd
& Hst8 & Hdst8 & HN & Hcur & Hnb & HSEP & HlyF & Hev & Hlive & (HFhi1 & HFimg & HFhi2) & HFceil & (Hph & Hpimg & Hpapp) & Hpceil & HnbM).
rbox HFimg. rbox HFhi2. rbox Hpimg. rbox Hpapp.
pose proof HH3 as (Hr1 & Hr2 & Hr3 & Hhd & Hcur2 & Hfattr & Hfgen & Hdelay).
pose proof HM as (Wp & Wn & Wc & _).
pose proof HRC as ((R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & R27) & RC10 & RC14 & RC15 & RC16 & RC17 & RC13).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFA1 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity. assert (HEV : EV_RFC = 6) by reflexivity.
assert (HBb1 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc Sc)) by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (apply HBb1; exact Hpd).
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2].
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (HSPB : alloc_ceiling <= spZ regs - TRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDST0 : 4096 <= dst) by (clear - Hdst1 HFhi1; lia). assert (HDSTC : dst + 32 <= alloc_ceiling) by (clear - Hdst2 HFceil; lia).
assert (HDSTH : rboxed (dst + 32 <= 2147446784 \/ 17594333495296 <= dst)) by (unfold rboxed in *; clear - Hdst1 Hdst2 HFhi2; lia).
assert (Hpdst : rboxed (pdata + req_size nb <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= pdata)).
{ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ pdata nb cid pos HAR1 Hpdc HfinC) as D. unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (HV : rfc_vals (bv_unsigned (getr regs1 25)) cur2 0 0 fattr fgen delay 0 cur nb) by (unfold rfc_vals; pose proof (bv_unsigned_in_range 64 (getr regs1 25)) as HRg; change (bv_modulus 64) with (2 ^ 64) in HRg; repeat split; lia).
remember (Ereg regs1 (I_extra regs pdata nb cur2 0 fattr fgen delay 0 0)) as E eqn:HE.
pose proof (rfc_C3_entry B TL LAWS W1 regs regs1 mem1 lyc Sc md1 ly STK sp0 st dst N pdata nb cur2 0 fattr fgen delay 0 0 cid pos cur r1 r2 r3 cur3
HAR1 Hpdc HfinC Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV ltac:(clear - Hcur; lia) Hstk Hal16 Hwlo Hwhi Hpres1 HRC HFR HM) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - HSPB C1 HTS Has; lia).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 N) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = Z_to_bv 64 (dst + 16)) by (rewrite (EE 10%nat 10%bv eq_refl); exact RC10).
assert (E13 : ew E 13 = Z_to_bv 64 cur3) by (rewrite (EE 13%nat 13%bv eq_refl); exact RC13).
assert (E15 : ew E 15 = Z_to_bv 64 r1) by (rewrite (EE 15%nat 15%bv eq_refl); exact RC15).
assert (E16 : ew E 16 = Z_to_bv 64 r2) by (rewrite (EE 16%nat 16%bv eq_refl); exact RC16).
assert (E17 : ew E 17 = Z_to_bv 64 r3) by (rewrite (EE 17%nat 17%bv eq_refl); exact RC17).
assert (EX : forall j, ew E (32 + j) = nth j (I_extra regs pdata nb cur2 0 fattr fgen delay 0 0) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 pdata) by exact (EX 0%nat). assert (E33 : ew E 33 = Z_to_bv 64 nb) by exact (EX 1%nat).
assert (E34 : ew E 34 = Z_to_bv 64 cur2) by exact (EX 2%nat). assert (E35 : ew E 35 = Z_to_bv 64 0) by exact (EX 3%nat).
assert (E36 : ew E 36 = getr regs 1) by exact (EX 4%nat). assert (E37 : ew E 37 = getr regs 8) by exact (EX 5%nat).
assert (E38 : ew E 38 = getr regs 9) by exact (EX 6%nat). assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat).
assert (E40 : ew E 40 = getr regs 19) by exact (EX 8%nat). assert (E41 : ew E 41 = getr regs 20) by exact (EX 9%nat).
assert (E42 : ew E 42 = getr regs 21) by exact (EX 10%nat). assert (E43 : ew E 43 = getr regs 22) by exact (EX 11%nat).
assert (E44 : ew E 44 = getr regs 23) by exact (EX 12%nat). assert (E45 : ew E 45 = getr regs 24) by exact (EX 13%nat).
assert (E46 : ew E 46 = getr regs 25) by exact (EX 14%nat). assert (E47 : ew E 47 = getr regs 26) by exact (EX 15%nat).
assert (E48 : ew E 48 = Z_to_bv 64 fattr) by exact (EX 16%nat). assert (E49 : ew E 49 = Z_to_bv 64 fgen) by exact (EX 17%nat).
assert (E50 : ew E 50 = Z_to_bv 64 delay) by exact (EX 18%nat). assert (E51 : ew E 51 = Z_to_bv 64 0) by exact (EX 19%nat).
assert (E52 : ew E 52 = Z_to_bv 64 0) by exact (EX 20%nat).
clear EX.
assert (B19 : bv_unsigned (ew E 19) = st) by (rewrite E19; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8) = dst) by (rewrite E8; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
set (Zs := fun a : Z => spZ regs - TRFC_STK <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
assert (ZBsm : forall a, SB <= a < kHighShadowEnd -> ~ Zsm a).
{ intros a Ha. subst Zsm. cbn beta. clear - Ha HSPB HSTB HDST0 HDSTH HTS Has C1 C2 C3 C4 C5. unfold rboxed in HDSTH. unfold SB in Ha. lia. }
reshok_bx HS 22%nat.
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RFC_RD3) mem1 (seg_rom tfibsegs))) in HJ1.
destruct (Z_le_gt_dec (cur3 + 3) nb) as [CA|CA].
{ assert (HC6 : cur3 = cur + 6) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & ->)]; [exact X | lia]).
assert (GB : forall j, 0 <= j < 3 -> aview tfibsegs (w_H W1) mem1 (pdata + (cur3 + j)) = Some (hb P cur (6 + j))).
{ intros j Hj. rewrite (proj1 (proj2 KEPT1) pdata nb (cur3 + j) Hpd) by (unfold req_size; destruct (Z.eqb_spec nb 0); lia).
  unfold hb. replace (pdata + (cur3 + j)) with (pdata + Z.of_nat (Z.to_nat (cur + (6 + j)))) by lia.
  apply (garr8_aview _ _ _ _ HPL). lia. }
assert (HBR : forall j, 0 <= j < 3 -> 0 <= hb P cur (6 + j) < 256)
  by (intros j Hj; destruct (aview_byte tfibsegs _ _ _ _ (GB j Hj)) as (bb & _ & _ & Hr); exact Hr).
assert (VB : forall i, (i < 3)%nat -> val_mem tfibsegs (mrestrict (w_H W1) mem1) (pdata + cur3 + Z.of_nat i) 1 (hb P cur (6 + Z.of_nat i))).
{ intros i Hi. replace (pdata + cur3 + Z.of_nat i) with (pdata + (cur3 + Z.of_nat i)) by (clear; lia).
  exact (val_mem1_of_aview _ _ _ _ (GB (Z.of_nat i) ltac:(clear - Hi; lia))). }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let WS := constr:(map (Z_to_bv 64) ((pdata + cur3) :: map (fun i => hb P cur (6 + Z.of_nat i)) (seq 0 3))) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS;
assert (EQ : ew (havoc Ev K WS) K = Z_to_bv 64 (pdata + cur3)) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; clear; lia)));
assert (EBy : forall i, (i < 3)%nat -> ew (havoc Ev K WS) (K + (1 + i)) = Z_to_bv 64 (hb P cur (6 + Z.of_nat i)))
  by (intros i Hi; rewrite (ew_havoc_new Ev K WS (1 + i) (Z_to_bv 64 0)) by (cbn [length map seq]; clear - Hi; lia);
      do 3 (destruct i as [|i]; [reflexivity|]); clear - Hi; lia)
end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_alias tfibsegs Ev ssv msv (SAlu ALU_ADD (SOff 32 0) (SOff 13 0)) (SOff K 0) HS
  ltac:(transitivity (Z_to_bv 64 (pdata + cur3));
        [ apply denot_add_atoms; [enorm; exact E32 | enorm; exact E13 | clear - Hph; lia | clear - Hcur HC6; lia | clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia]
        | cbn [sv_denot]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia); rewrite Z.add_0_r; reflexivity ])) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (src_region K 3) HS eq_refl
  (src_region_ok Ev _ K 3 (pdata + cur3) (fun i => hb P cur (6 + Z.of_nat i))
     ltac:(rewrite EQ; apply unsigned_lit_small; clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(clear - Hcur Hph HC6; lia) ltac:(cbn; clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(intros i Hi; split; [exact (EBy i Hi) | split; [exact (HBR (Z.of_nat i) ltac:(clear - Hi; lia)) | exact (VB i Hi)]]))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold src_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia);
    enorm; agnorm; rewrite B8, B19, Usp;
    unfold A_GOT_shadow, A_shadow_glob, off_img in *; unfold rboxed in *;
    clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB HSTB Hpdst Hdst1 Hdst2 Hst1 Hpimg Hpapp HTS Has C1; cbn; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ K (mkAF 4096 140737479966720 0) HS
  ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 HSPB C1; lia);
         rewrite Z.pow_0_r, Z.mod_1_r; clear - Hcur Hnb HC6 CA Hph Hpceil Hrq2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end end.
pose proof (EBy 0%nat ltac:(lia)) as EB0. pose proof (EBy 1%nat ltac:(lia)) as EB1. pose proof (EBy 2%nat ltac:(lia)) as EB2. cbn [Nat.add Z.of_nat] in EB0, EB1, EB2. clear EBy GB VB.
rebaseH HS AG.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
assert (HB6 : 0 <= hb P cur 6 < 256) by exact (HBR 0 ltac:(lia)). assert (HB7 : 0 <= hb P cur 7 < 256) by exact (HBR 1 ltac:(lia)). assert (HB8 : 0 <= hb P cur 8 < 256) by exact (HBR 2 ltac:(lia)).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur3 1) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur3 + 1)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur3) 3)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CA HC6 Hcur Hrq2; lia);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT3. clear KEPT2.
vkeepUN2 UN2 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur3 3) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur3 + 3)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur3) 3)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CA HC6 Hcur Hrq2; lia);
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_J.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 5%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 13 3) (cur3 + 3) HRt B18n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite E13, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 20 4 (SOff 49 0) fgen HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfg.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 24 2 (SOff 50 0) delay HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SExt false 8 (SOff 54 0)) (hb P cur 6) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; rewrite U_SExt, (U_atom _ 54 (hb P cur 6)) by first [enorm; exact EB0 | unfold M64; lia]; cbn [Z.of_N]; change (2 ^ 8) with 256; rewrite Z.mod_small by lia; rewrite ?zcanon_id by (unfold M64; lia); reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (field1_of_region _ _ 8%nat dst _ _ _ _ _ 26 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 56 0)) (SLit 8)) (SExt false 8 (SOff 55 0))) (hb P cur 7 + 256 * hb P cur 8) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8 _ 56 55 (hb P cur 8) (hb P cur 7)); [enorm; exact EB2 | enorm; exact EB1 | lia | lia])
  ltac:(lia)) as V26.
replace ((hb P cur 7 + 256 * hb P cur 8) mod 256) with (hb P cur 7) in V26
  by (rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia; reflexivity).
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 27 1 (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 56 0)) (SLit 8)) (SExt false 8 (SOff 55 0))) (SLit 8)) (hb P cur 8) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8_hi _ 56 55 (hb P cur 8) (hb P cur 7)); [enorm; exact EB2 | enorm; exact EB1 | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as V27.
replace (dst + 27) with (dst + 26 + 1) in V27 by lia.
pose proof (val_mem_bytes2 _ _ _ _ V26 V27 ltac:(lia) ltac:(lia)) as Vnl. clear V26 V27.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Uspn
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vfg, Vde, Vti. rewrite Z.add_0_r in Vl.
destruct Hhd as [(Hz & H6 & Hc3 & Efa & Efg & Ede) | (_ & X & ->)]; [| exfalso; clear - X CA HC6; lia].
apply Z.lor_eq_0_iff in Hz as [Hz12 Hz3]. apply Z.lor_eq_0_iff in Hz12 as [Hz1 Hz2]. subst r1 r2 r3.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (21%bv : bv 5) Q21. rregS HS (10%bv : bv 5) Q10s.
pose proof (denot_shx _ 19 22 16 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_J end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RJ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX 0 (cur3 + 3) (hb P cur 7 + 256 * hb P cur 8) fattr fgen delay (hb P cur 6) T P);
[ exact RC | exact HPL
| intros H9; split; [exact Efa|]; split; [exact Efg|]; split; [exact Ede|]; split; reflexivity
| left; split; [reflexivity|]; split; lia
| exact HJc
| unfold rfc_vals; repeat split; lia
| unfold J_regs_at, I_regs_at, w64;
  rewrite Q10s, denot_lit_U, (U_attr_bit _ 48 fattr) by first [enorm; exact E48 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q21, Q25; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, E15, E16, E17, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; pose proof (rfcJ_alu_or_lits 0 0 ltac:(lia) ltac:(lia)) as AOZ; change (Z.lor 0 0) with 0 in AOZ; rewrite ?AOZ; reflexivity
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
destruct (Z_le_gt_dec (cur3 + 1) nb) as [CB|CC].
{ assert (HC6 : cur3 = cur + 6) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & ->)]; [exact X | lia]).
assert (GB : forall j, 0 <= j < 1 -> aview tfibsegs (w_H W1) mem1 (pdata + (cur3 + j)) = Some (hb P cur (6 + j))).
{ intros j Hj. rewrite (proj1 (proj2 KEPT1) pdata nb (cur3 + j) Hpd) by (unfold req_size; destruct (Z.eqb_spec nb 0); lia).
  unfold hb. replace (pdata + (cur3 + j)) with (pdata + Z.of_nat (Z.to_nat (cur + (6 + j)))) by lia.
  apply (garr8_aview _ _ _ _ HPL). lia. }
assert (HBR : forall j, 0 <= j < 1 -> 0 <= hb P cur (6 + j) < 256)
  by (intros j Hj; destruct (aview_byte tfibsegs _ _ _ _ (GB j Hj)) as (bb & _ & _ & Hr); exact Hr).
assert (VB : forall i, (i < 1)%nat -> val_mem tfibsegs (mrestrict (w_H W1) mem1) (pdata + cur3 + Z.of_nat i) 1 (hb P cur (6 + Z.of_nat i))).
{ intros i Hi. replace (pdata + cur3 + Z.of_nat i) with (pdata + (cur3 + Z.of_nat i)) by (clear; lia).
  exact (val_mem1_of_aview _ _ _ _ (GB (Z.of_nat i) ltac:(clear - Hi; lia))). }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let WS := constr:(map (Z_to_bv 64) ((pdata + cur3) :: map (fun i => hb P cur (6 + Z.of_nat i)) (seq 0 1))) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS;
assert (EQ : ew (havoc Ev K WS) K = Z_to_bv 64 (pdata + cur3)) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; clear; lia)));
assert (EBy : forall i, (i < 1)%nat -> ew (havoc Ev K WS) (K + (1 + i)) = Z_to_bv 64 (hb P cur (6 + Z.of_nat i)))
  by (intros i Hi; rewrite (ew_havoc_new Ev K WS (1 + i) (Z_to_bv 64 0)) by (cbn [length map seq]; clear - Hi; lia);
      do 1 (destruct i as [|i]; [reflexivity|]); clear - Hi; lia)
end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_alias tfibsegs Ev ssv msv (SAlu ALU_ADD (SOff 32 0) (SOff 13 0)) (SOff K 0) HS
  ltac:(transitivity (Z_to_bv 64 (pdata + cur3));
        [ apply denot_add_atoms; [enorm; exact E32 | enorm; exact E13 | clear - Hph; lia | clear - Hcur HC6; lia | clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia]
        | cbn [sv_denot]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia); rewrite Z.add_0_r; reflexivity ])) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (src_region K 1) HS eq_refl
  (src_region_ok Ev _ K 1 (pdata + cur3) (fun i => hb P cur (6 + Z.of_nat i))
     ltac:(rewrite EQ; apply unsigned_lit_small; clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(clear - Hcur Hph HC6; lia) ltac:(cbn; clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(intros i Hi; split; [exact (EBy i Hi) | split; [exact (HBR (Z.of_nat i) ltac:(clear - Hi; lia)) | exact (VB i Hi)]]))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold src_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia);
    enorm; agnorm; rewrite B8, B19, Usp;
    unfold A_GOT_shadow, A_shadow_glob, off_img in *; unfold rboxed in *;
    clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB HSTB Hpdst Hdst1 Hdst2 Hst1 Hpimg Hpapp HTS Has C1; cbn; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ K (mkAF 4096 140737479966720 0) HS
  ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 HSPB C1; lia);
         rewrite Z.pow_0_r, Z.mod_1_r; clear - Hcur Hnb HC6 CB Hph Hpceil Hrq2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end end.
pose proof (EBy 0%nat ltac:(lia)) as EB0. cbn [Nat.add Z.of_nat] in EB0. clear EBy GB VB.
rebaseH HS AG.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
assert (HB6 : 0 <= hb P cur 6 < 256) by exact (HBR 0 ltac:(lia)).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur3 1) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur3 + 1)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur3) 1)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CB HC6 Hcur Hrq2; lia);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT3. clear KEPT2.
vkeepUN2 UN2 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
{ exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur3 3) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur3 + 3)); [discriminate Hc | lia]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur3) 1)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CB HC6 Hcur Hrq2; lia);
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_J.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 5%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 33 0) nb HRt B18n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 20 4 (SOff 49 0) fgen HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfg.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 24 2 (SOff 50 0) delay HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 26 2 (SOff 51 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SExt false 8 (SOff 54 0)) (hb P cur 6) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; rewrite U_SExt, (U_atom _ 54 (hb P cur 6)) by first [enorm; exact EB0 | unfold M64; lia]; cbn [Z.of_N]; change (2 ^ 8) with 256; rewrite Z.mod_small by lia; rewrite ?zcanon_id by (unfold M64; lia); reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Uspn
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vfg, Vde, Vnl, Vti. rewrite Z.add_0_r in Vl.
destruct Hhd as [(Hz & H6 & Hc3 & Efa & Efg & Ede) | (_ & X & ->)]; [| exfalso; clear - X CB HC6; lia].
apply Z.lor_eq_0_iff in Hz as [Hz12 Hz3]. apply Z.lor_eq_0_iff in Hz12 as [Hz1 Hz2]. subst r1 r2 r3.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (21%bv : bv 5) Q21. rregS HS (10%bv : bv 5) Q10s.
pose proof (denot_shx _ 19 22 16 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_J end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RJ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX (2 ^ 64 - 1) nb 0 fattr fgen delay (hb P cur 6) T P);
[ exact RC | exact HPL
| intros H9; exfalso; lia
| right; split; [lia|]; split; lia
| exact HJc
| unfold rfc_vals; repeat split; lia
| unfold J_regs_at, I_regs_at, w64;
  rewrite Q10s, denot_lit_U, (U_attr_bit _ 48 fattr) by first [enorm; exact E48 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q21, Q25; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, E15, E16, E17, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; pose proof (rfcJ_alu_or_lits 0 0 ltac:(lia) ltac:(lia)) as AOZ; change (Z.lor 0 0) with 0 in AOZ; rewrite ?AOZ; rewrite rfcJ_alu_or_lits by lia; reflexivity
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
{
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Usp E19 E8 Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
{ exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur3 1) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur3 + 1)); [discriminate Hc | lia]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_J.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
{ awrI Usp E19 E8 Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT2.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 3%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 33 0) nb HRt B19 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 20 4 (SOff 49 0) fgen HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E49, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfg.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 24 2 (SOff 50 0) delay HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 26 2 (SOff 51 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SOff 52 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Usp
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vfg, Vde, Vnl, Vti. rewrite Z.add_0_r in Vl.
assert (HnbC : nb < cur + 9) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & _)]; lia).
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (21%bv : bv 5) Q21. rregS HS (10%bv : bv 5) Q10s.
pose proof (denot_shx _ 19 22 16 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_J end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RJ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX (2 ^ 64 - 1) nb 0 fattr fgen delay 0 T P);
[ exact RC | exact HPL
| intros H9; exfalso; lia
| right; split; [lia|]; split; lia
| exact HJc
| unfold rfc_vals; repeat split; lia
| unfold J_regs_at, I_regs_at, w64;
  rewrite Q10s, denot_lit_U, (U_attr_bit _ 48 fattr) by first [enorm; exact E48 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q21, Q25; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, E15, E16, E17, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; apply or5_m1; lia
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
Qed.
End RC.
End d.
