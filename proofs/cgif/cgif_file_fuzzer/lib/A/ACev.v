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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACey.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Ltac reseatL HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
Ltac oblD RA E8x E25x :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 8 ?c)) _ =>
rewrite (U_atom_off Ex 8 _ c ltac:(enorm; agnorm; exact E8x)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 22 SB ltac:(enorm; agnorm; exact E25x)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac oblS RA E19x E22x :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 19 ?c)) _ =>
rewrite (U_atom_off Ex 19 _ c ltac:(enorm; agnorm; exact E19x)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 22 SB ltac:(enorm; agnorm; exact E22x)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n :=
try clear E8n; try clear E18n; try clear E25n; try clear Uspn; try clear B8n; try clear B18n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E8 with _ = ?v => assert (E8n : ew Ev 8 = v) by (rewrite (AG 8%nat) by lia; exact E8) end;
lazymatch type of E19 with _ = ?v => assert (E18n : ew Ev 19 = v) by (rewrite (AG 19%nat) by lia; exact E19) end;
lazymatch type of E22 with _ = ?v => assert (E25n : ew Ev 22 = v) by (rewrite (AG 22%nat) by lia; exact E22) end;
lazymatch type of Usp with _ = ?v => assert (Uspn : bv_unsigned (ew Ev 2) = v) by (rewrite (AG 2%nat) by lia; exact Usp) end;
assert (B8n : bv_unsigned (ew Ev 8) = dst) by (rewrite E8n; apply unsigned_lit_small; lia);
assert (B18n : bv_unsigned (ew Ev 19) = st) by (rewrite E18n; apply unsigned_lit_small; lia) end.
Ltac cregI HS Usp :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R; enorm; agnorm;
repeat match goal with H : ew ?Ex ?n = _ |- context [ew ?Ex ?n] => rewrite H end;
first [ reflexivity | symmetry; assumption
| rewrite Usp; unfold spZ; rewrite <- (Z_to_bv_bv_unsigned 64 (getr _ 2)) at 2; f_equal; lia ] end.
Ltac field_at HS i n b HB od w e v Ee Vname :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_region) in
let HRr := fresh "HRr" in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ n b cs lo hi wlo whi od w (SOff e 0) v HRr HB ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Ee, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as Vname end;
clear HRr; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vname; rewrite ?Z.add_0_r in Vname end.
Ltac vkeep V H2 m2 etac :=
lazymatch type of V with val_mem _ (mrestrict ?Hh ?m) ?a ?n ?v =>
let V2 := fresh "V" in
assert (V2 : val_mem tfibsegs (mrestrict H2 m2) a n v) by (apply (val_mem_kept Hh H2 m m2 a n v V); intros i Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; etac);
clear V; rename V2 into V end.
Ltac vkeepUN UN Vp Vn Vc ztac :=
lazymatch type of UN with forall a, _ -> _ -> aview _ ?H2 ?m2 a = _ =>
vkeep Vp H2 m2 ltac:(apply UN; ztac); vkeep Vn H2 m2 ltac:(apply UN; ztac); vkeep Vc H2 m2 ltac:(apply UN; ztac) end.
Ltac vkeepUN2 UN Vp Vn ztac :=
lazymatch type of UN with forall a, _ -> _ -> aview _ ?H2 ?m2 a = _ =>
vkeep Vp H2 m2 ltac:(apply UN; ztac); vkeep Vn H2 m2 ltac:(apply UN; ztac) end.
Lemma Z_lor_bound : forall x y n, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
intros x y n Hn Hx Hy. pose proof (proj2 (Z.lor_nonneg x y) ltac:(lia)) as Hnn. split; [exact Hnn|].
destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.lor_0_r; lia|].
assert (Hp : 0 < Z.lor x y).
{ destruct (Z.eq_dec (Z.lor x y) 0) as [H0|H0]; [|lia]. apply Z.lor_eq_0_iff in H0. lia. }
apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma U_or_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
U E (SAlu ALU_OR (SOff a 0) (SOff b 0)) = Z.lor x y.
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a x Ha Hx), (U_atom E b y Hb Hy).
apply zcanon_id. unfold M64. apply Z_lor_bound; lia.
Qed.
Lemma U_seqz : forall E e, U E (SAlu ALU_SLTU e (SLit 1)) = (if U E e =? 0 then 1 else 0).
Proof.
intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. rewrite (zcanon_id 1) by (unfold M64; lia).
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu. change (bv_unsigned (sv_denot E e)) with (U E e) in Hu.
destruct (Z.ltb_spec (U E e) 1) as [Hl|Hl]; destruct (Z.eqb_spec (U E e) 0) as [He|He]; try lia; apply zcanon_id; unfold M64; lia.
Qed.
Lemma alu_seqz_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
alu64 ALU_SLTU (alu64 ALU_OR (Z_to_bv 64 x) (Z_to_bv 64 y)) (Z_to_bv 64 1) = Z_to_bv 64 (if Z.lor x y =? 0 then 1 else 0).
Proof.
intros x y Hx Hy. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])).
change (alu64 _ _ _) with (sv_denot E0 (SAlu ALU_SLTU (SAlu ALU_OR (SLit x) (SLit y)) (SLit 1))).
rewrite denot_lit_U, U_seqz, U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; apply Z_lor_bound; lia). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section RI.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy_tfb.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_I_ok : RFC_I_stmt B MT.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 regs1 mem1 md1 ly1 S1 k1 racc curv lpa nlp fattr fgen delay tidx pal T acc P
RC HPL HMLE Hacc Hhdrv Hprog HJ1 Hk1 Hfrs1 HPerm1 HPAL HV HRI HFR HM RAdst1 KEPT1 HIO1.
pose proof RC as ((HMOK & HCOST & HlenP) & HPerm & Hpd & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hown & HfinC & Hcid & Hfal & Hst1 & Hst2 & Hdst1 & Hdst2 & Hsd
& Hst8 & Hdst8 & HN & Hcur & Hnb & HSEP & HlyF & Hev & Hlive & (HFhi1 & HFimg & HFhi2) & HFceil & (Hph & Hpimg & Hpapp) & Hpceil & HnbM).
rbox HFimg. rbox HFhi2. rbox Hpimg. rbox Hpapp.
pose proof HPAL as (Hpal & Hlpa0 & Hpaltok & Hpal4096).
pose proof HV as (HR & Hcurv & Hlpa & Hnlp & Hfattr & Hfgen & Hdelay & Htidx).
pose proof HM as (Wp & Wn & Wc & _).
pose proof HRI as (R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & R27).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFA1 : forall c p, frame_addr ly1 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly1 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HdstA1 : frame_addr ly1 cid pos <= dst) by (rewrite EFA1; exact Hdst1).
assert (HdstB1 : dst + 32 <= frame_addr ly1 cid pos + fs_frame_bytes cid) by (rewrite EFA1; exact Hdst2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity. assert (HEV : EV_RFC = 6) by reflexivity.
assert (HBb1 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly1 S1)).
{ intros b m Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. right. exact Hb. }
assert (Hpdc : In (pdata, nb) (ablocks B ly1 S1)) by (apply HBb1; exact Hpd).
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. pose proof (req_size_pos N ltac:(lia)) as [HrqN1 HrqN2].
assert (Hfin : In (cid, pos) (frames S1)) by (rewrite Hfrs1; exact HfinC). pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (HSPB : alloc_ceiling <= spZ regs - TRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDST0 : 4096 <= dst) by (clear - Hdst1 HFhi1; lia). assert (HDSTC : dst + 32 <= alloc_ceiling) by (clear - Hdst2 HFceil; lia).
assert (HDSTH : rboxed (dst + 32 <= 2147446784 \/ 17594333495296 <= dst)) by (unfold rboxed in *; clear - Hdst1 Hdst2 HFhi2; lia).
assert (Hpdst : rboxed (pdata + req_size nb <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= pdata)).
{ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ pdata nb cid pos HAR1 Hpdc Hfin) as D. rewrite EFA1 in D. unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (Hlive1 : blocks_bytes S1 + N <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HPerm1), bsum_app, <- (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B lyc Sc).
assert (bsum pal <= 3 * 2 ^ 16) by (rewrite Hpal; destruct (Z.land fattr 1 =? 0); cbn; lia).
unfold LIVE_RFC in Hlive. clear - H Hlive HN. lia. }
remember (Ereg regs1 (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx)) as E eqn:HE.
pose proof (rfc_I_entry B TL LAWS W1 regs regs1 mem1 ly1 S1 md1 ly STK sp0 st dst N pdata nb curv lpa fattr fgen delay nlp tidx cid pos racc cur
HAR1 Hpdc Hfin Hst1 Hst2 ltac:(rewrite EFA1; exact Hdst1) ltac:(rewrite EFA1; exact Hdst2)
Hsd Hst8 Hdst8 HN Hnb HV ltac:(clear - Hcur; lia) Hstk Hal16 Hwlo Hwhi Hpres1 HRI HFR HM) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - HSPB C1 HTS Has; lia).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 N) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew E 25 = Z_to_bv 64 racc) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (EX : forall j, ew E (32 + j) = nth j (I_extra regs pdata nb curv lpa fattr fgen delay nlp tidx) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 pdata) by exact (EX 0%nat). assert (E33 : ew E 33 = Z_to_bv 64 nb) by exact (EX 1%nat).
assert (E34 : ew E 34 = Z_to_bv 64 curv) by exact (EX 2%nat). assert (E35 : ew E 35 = Z_to_bv 64 lpa) by exact (EX 3%nat).
assert (E36 : ew E 36 = getr regs 1) by exact (EX 4%nat). assert (E37 : ew E 37 = getr regs 8) by exact (EX 5%nat).
assert (E38 : ew E 38 = getr regs 9) by exact (EX 6%nat). assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat).
assert (E40 : ew E 40 = getr regs 19) by exact (EX 8%nat). assert (E41 : ew E 41 = getr regs 20) by exact (EX 9%nat).
assert (E42 : ew E 42 = getr regs 21) by exact (EX 10%nat). assert (E43 : ew E 43 = getr regs 22) by exact (EX 11%nat).
assert (E44 : ew E 44 = getr regs 23) by exact (EX 12%nat). assert (E45 : ew E 45 = getr regs 24) by exact (EX 13%nat).
assert (E46 : ew E 46 = getr regs 25) by exact (EX 14%nat). assert (E47 : ew E 47 = getr regs 26) by exact (EX 15%nat).
assert (E48 : ew E 48 = Z_to_bv 64 fattr) by exact (EX 16%nat). assert (E49 : ew E 49 = Z_to_bv 64 fgen) by exact (EX 17%nat).
assert (E50 : ew E 50 = Z_to_bv 64 delay) by exact (EX 18%nat). assert (E51 : ew E 51 = Z_to_bv 64 nlp) by exact (EX 19%nat).
assert (E52 : ew E 52 = Z_to_bv 64 tidx) by exact (EX 20%nat).
clear EX.
assert (B19 : bv_unsigned (ew E 19) = st) by (rewrite E19; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8) = dst) by (rewrite E8; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
set (Zs := fun a : Z => spZ regs - TRFC_STK <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 16 \/ st + 16 <= a < st + 24).
set (Zsn := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 16).
assert (ZBsm : forall a, SB <= a < kHighShadowEnd -> ~ Zsm a).
{ intros a Ha. subst Zsm. cbn beta. clear - Ha HSPB HSTB HDST0 HDSTH HTS Has C1 C2 C3 C4 C5. unfold rboxed in HDSTH. unfold SB in Ha. lia. }
reshok_bx HS 22%nat.
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RFC_I) mem1 (seg_rom tfibsegs))) in HJ1.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
{ awrI Usp E19 E8 Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
assert (SHK1 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem ms) a = aview tfibsegs (w_H W1) mem1 a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]).
pose proof (RA_kept_band _ _ dst 32 SHK1 ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as RAdst1s. clear SHK1 RAdst1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
clear Wc. field_at HS 4%nat 19%nat st B19 16 8%N 34%nat curv E34 Wc.
rename Wp into Vp. rename Wn into Vn. rename Wc into Vc.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ1) Hfin) as (_ & _ & HFpres1 & _).
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 338224) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly1 (aview tfibsegs (w_H W1) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly1 _ (spZ regs - 96) dst []).
- apply achain_low; clear - HDST0 HDSTC; lia.
- unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - HSPB C1 HTS Has; unfold spZ in *; lia.
- unfold s0Z; rewrite Rs0; enorm; agnorm; rewrite E8; apply unsigned_lit_small; clear - HDST0 HDSTC C1; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub tfibsegs B LAWS tfib_segs_low MT AMALLOC4 W1 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
ly1 S1 _ k1 N (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_IM) [] HJ1);
[ rewrite Ra0; enorm; agnorm; rewrite E18; reflexivity
| unfold MALLOC_MAX; clear - HN; lia
| exact Hlive1
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; clear; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| rewrite HEV in Hev; clear - Hnev1 Hev Hk1; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
|
apply (mok_station MT Sc S1 T acc (mo_malloc MT N) MTL HMOK HMLE); [apply (mo_malloc_nonneg MT MTL); clear - HN; lia|];
unfold RFC_COST in HCOST; pose proof (mo_free_nonneg MT MTL) as Hf0; clear - Hacc HCOST Hf0; lia ] end. }
cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 CH.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hr4096 & Ebl & HK0 & HMLE2 & HJS2).
assert (HIO2 : same_io mdc md2) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJS2)). clear HJS2.
pose proof (proj1 HJ2) as HAR2.
assert (HK : acall_kept tfibsegs B ly1 S1 W1 (ms_mem ms) W2 mem2 (sp0 + (spZ regs - 96 - sp0) - ASTACK) (sp0 + (spZ regs - 96 - sp0)) (fun a => res <> 0 /\ res <= a < res + req_size N))
by (eapply acall_kept_mono_E; [exact HK0 | intros a Ha; cbn beta; split; [clear - Hr4096; lia | exact Ha]]).
assert (HBin : forall b, In b (ablocks B ly1 S1) -> In b (ablocks B ly2 S2)) by (intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb).
assert (HrIn : In (res, N) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HresIn : res <> 0 -> In (res, N) (ablocks B ly2 S2)) by (intros _; exact HrIn).
vkeep Vp (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vn (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vc (w_H W2) mem2 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res N HAR2 HrIn) as (Hr16 & _ & HrCeil & [_ HrHi2] & _).
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR2 HrIn) as HrHi1.
assert (HrHi : (res + req_size N <= 65536 \/ 6270976 <= res) /\ (res + req_size N <= 2147446784 \/ 17594333495296 <= res))
by (pose proof asan_consts as (C1' & C2' & C3' & C4' & C5'); clear - HrHi1 HrHi2 C1' C2' C3' C4' C5'; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (Hrng : res = 0 \/ (4096 <= res /\ ((res + req_size N <= 65536 \/ 6270976 <= res) /\ (res + req_size N <= 2147446784 \/ 17594333495296 <= res)) /\ res + req_size N <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, N) (ablocks B ly2 S2)))
by (right; split; [exact Hr4096|]; split; [exact HrHi|]; split; [exact HrCeil|]; split; [exact Hr16 | exact HrIn]).
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & Hnev2 & _).
assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HdstA2 : frame_addr ly2 cid pos <= dst) by (rewrite EFA2; exact Hdst1).
assert (HdstB2 : dst + 32 <= frame_addr ly2 cid pos + fs_frame_bytes cid) by (rewrite EFA2; exact Hdst2). clear HdstA1 HdstB1.
assert (HnewF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (res <> 0 /\ res <= a < res + req_size N)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res N cid pos HAR2 (HresIn Hnz) Hfin2) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
assert (RAdst2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF dst 32).
{ eapply (RA_kept_call B ly1 S1); [exact HK | exact Hfin | intros a [Hnz Ha]; clear - Hnz Ha Hrng; unfold rboxed in *; lia | exact Hcid | rewrite EFA1; exact Hfal
| rewrite EFA1; clear - HFhi1; lia | rewrite EFA1; exact HFceil | rewrite EFA1; exact Hdst1 | rewrite EFA1; exact Hdst2 | exact RAdst1s]. }
clear RAdst1s.
reseatL HS HJ2 HP2 [0; 1; 2; 3; 4]%nat AG
ltac:(first [ eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact HJ2 | evalER AG | clear - HTS Has; lia | clear - Hwlo HTS Has; lia | clear - Hwhi; lia | cbn; lia | cbn; lia]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot2) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell2) | lia]
| eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalER AG | exact Hfin | left; cbn [YP09.r_lo YP09.r_hi]; rewrite EFA1; lia
| intros a Ha; cbn beta; apply HnewF; lia | intros a Ha; apply (fun H => proj1 (HFpres2 a H)); rewrite EFA2; lia ]
| eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact HJ2 | evalER AG | clear - Hst1 HTS Has; lia | clear - Hst1 Hwlo HTS Has; lia | clear - Hst2; lia | cbn; lia | cbn; lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell1 Kgot1 Kcell2 Kgot2.
rreg HS (10%bv : bv 5) Rres. rewrite Ha02 in Rres. symmetry in Rres. unfold w64 in Rres.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
clear Hrng. rbox HrHi.
pose proof (aftok_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N HJ1 (proj1 HJ2) Ebl ltac:(clear - HN; lia)) as Timg.
assert (Aimg : forall blc i lyq, In (res, N) blc -> 0 <= i < req_size N -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N blc i lyq HJ1 (proj1 HJ2) Ebl ltac:(clear - HN; lia) Hin Hi). }
assert (HPerm2 : Permutation (ablocks B ly2 S2) ((res, N) :: pal ++ Bb)).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm1]. }
assert (HsepB : forall b m, In (b, m) (pal ++ Bb) -> res + req_size N <= b \/ b + req_size m <= res).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1 & l2 & El).
assert (HP' : Permutation (ablocks B ly2 S2) ((res, N) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HPerm2|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR2 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
assert (HimgFS : forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ (res <= a < res + req_size N)).
{ intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res N c p HAR2 HrIn ltac:(rewrite Hfrs2, Hfrs1; exact Hcp)) as D.
rewrite EFA2 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin HrqN2. lia.
+ destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR2 ltac:(rewrite Hfrs2, Hfrs1; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA2 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. unfold rboxed in HrHi. lia. }
assert (KEPT3 : rfc_kept B W memc W2 mem2 (spZ regs) Bb lyc Sc st dst).
{ eapply (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ ly1 S1 _ _ _ _ _ KEPT2 HK ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb1 _ Hfrs1 EFA1 _).
Unshelve.
- intros b m i Hb Hi [_ Hin]. pose proof (HsepB b m ltac:(apply in_app_iff; right; exact Hb)) as Hd. clear - Hd Hi Hin. lia.
- intros c p a Hcp Ha [_ Hin]. exact (HimgFS c p a Hcp Ha Hin). }
clear KEPT2 Hlive1 HnewF.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact tfibsegs Ex _ _ nx (mkAF 4096 140737479966720 4) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia;
change (2 ^ 4) with 16; clear - Hr4096 HrCeil Hr16 HrqN1 HrqN2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 22%nat.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
assert (RAst2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS ly2 S2 W2 mem2 _ st 24 HAR2); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
aj_run_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan.
all: try (oblD RAdst2 E8 E22).
all: try (oblS RAst2 E19 E22).
{ awrI Uspn E18n E8n Hown EFA2. }
unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
vkeepUN2 UN2 Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
clear Vc. field_at HS 4%nat 19%nat st B18n 16 8%N 34%nat curv E34 Vc.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
assert (SHK2 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) (ms_mem ms0) a = aview tfibsegs (w_H W2) mem2 a)
by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS ly2 S2 W2 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
pose proof (proj1 HJc) as HARc end end.
lazymatch type of HS with st_ok _ _ ?ss _ =>
lazymatch type of AG with forall n, _ -> ew ?Eb n = _ =>
let Kb := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
let ssJv := eval vm_compute in (mkSS RFC_IRD (sr_sets (ss_regs ss) (junk_upd 200 CLOB)) (ss_mem ss) None (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)))) in
pose (ssJ := ssJv);
assert (AGX : forall j, (j < Kb)%nat -> ew Eb j = ew Eb j) by (intros; reflexivity);
lazymatch goal with |- SRr _ ?Wx {| cfg_ms := ?msX; cfg_model := ?mdX |} _ =>
eapply SRr_bind with (R := rd_cut B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 Wx mdX (k1 + 1) ssJ Eb Kb (ms_mem msX) st res N pdata nb curv (spZ regs - 96 - sp0) dst RFC_IRD) end end end.
{ srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
- rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 33 nb), (U_atom _ 18 N), (U_atom _ 34 curv), zcanon_id in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E18 | exact E34]].
  assert (HOK : curv + N <= nb) by (destruct (Z.ltb_spec nb (N + curv)); [discriminate Hc | lia]). clear Hc.
  norm_ss HS. reshok_bx HS 22%nat.
  aj_run_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan.
  all: try (oblS RAstC E19 E22).
  { awrI Uspn E18n E8n Hown EFA2. }
  keStep HF HFr HG KE PR Zsm Usp B8 Usp.
  shkOf KE ZBsm SHKb.
  assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by exact (HBin _ Hpdc).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
  lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
  assert (HppresB : forall a, pdata + curv <= a < pdata + curv + N -> apresent (w_H W2) (ms_mem msX) a)
  by (destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb (proj1 HJc) Hpd2) as (_ & _ & _ & _ & HP & _); intros a Ha; apply (proj1 (HP a ltac:(clear - Ha HOK Hcurv Hcur Hrq2; lia))));
  assert (HsrcA : amem_range (pdata + curv) N) by (apply (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2; lia);
  assert (HsrcR : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF (pdata + curv) N) by (apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2; lia);
  assert (HsrcH : 0 < N -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem msX)) (pdata + curv) N) by (intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ _ pdata nb _ _ (proj1 HJc) Hpd2); clear - HOK Hcurv Hcur Hrq2 Hn0; lia);
  assert (HdA : amem_range res N) by (apply (amem_range_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJc) HrIn); clear - HrqN2 HN; lia);
  assert (HdR : range_addressable (aview tfibsegs (w_H W2) (ms_mem msX)) SHADOW_OFF res N) by (apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJc) HrIn); clear - HrqN2 HN; lia);
  assert (HdH : 0 < N -> shadow_hull_vis (aview tfibsegs (w_H W2) (ms_mem msX)) res N) by (intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJc) HrIn); clear - HrqN2 Hn0; lia);
  destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJc)) as (KcellC & _ & KgotC & _) end end.
  rewrite HBgot, HBcell in KgotC. rewrite HBcell in KcellC.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
  rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ (Z_to_bv 64 ?p) _ _; cfg_model := _ |} _ => change p with A_asan_memcpy_tfb end.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?msX) _ (ms_mem ?msX) _; cfg_model := _ |} _ =>
    lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem msX) _ _ |- _ =>
    eapply (aj_intrin_at_io B LAWS OCpy A_asan_memcpy_tfb AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
      ly2 S2 _ (k1 + 1) res (pdata + curv) N (spZ regs - 96 - sp0) (Z_to_bv 64 (RFC_IM + 100)) HJc);
    [ rewrite Ra0; rewrite Rres; reflexivity
    | rewrite Ra1; agnorm; rewrite E32, E34, alu_add_small by (unfold M64; clear - HOK Hcurv Hcur Hnb Hpceil Hrq2 Hph HN C1; lia); reflexivity
    | rewrite Ra2; agnorm; rewrite E18; reflexivity
    | clear - HN; lia | clear - Hr4096; lia | clear - HrCeil HrqN2 C1 C3 C4 C5; lia
    | unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; lia
    | replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
    | lia
    | clear - Hwlo HTS Has Hes; lia
    | rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
    | rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
    | rewrite Rra; reflexivity
    | vm_compute; reflexivity
    | intros a Ha; split; [replace a with (res + (a - res)) by lia; apply Aimg; [exact HrIn | clear - Ha HrqN2; lia] | clear - Ha HrCeil HrqN2 HSPB C1 HTS Has Hes; lia]
    | exact HdA | exact HdR | exact HdH
    | split; [clear - Hpceil Hcurv Hcur Hrq2 Hph C1; lia|]; split; [clear - Hpceil HOK Hcurv Hcur Hrq2 Hph C1 C3 C4 C5; lia|]; split;
      [ intros a Ha; split; [apply (aview_some_of_apresent tfibsegs); exact (HppresB a Ha)
        | unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - Ha Hpceil HOK Hcurv Hcur Hrq2 Hph HSPB C1 HTS Has Hes; unfold ESTACK in *; lia]
      | split; [pose proof (HsepB pdata nb ltac:(apply in_app_iff; right; exact Hpd)) as Hd; clear - Hd HOK Hcurv Hcur Hrq2 HrqN2 Hph; lia|];
        split; [exact HsrcA|]; split; [exact HsrcR | exact HsrcH] ] ] end end. }
  cbv beta. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HppresB HsrcA HsrcR HsrcH HdA HdR HdH.
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & Hio3).
  replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr3 by lia.
  destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
  reseatX HS HJ3 HP3 [0; 1; 2; 3; 4]%nat AG AGX
  ltac:(first [ eapply region_kept_aview;
    [ evalER AG
    | intros a Ha; apply Hfr3;
      [ clear - Ha HSPB HDST0 HDSTC HSTB Hst2 HTS Has C1 Hwhi; lia
      | first [ clear - Ha HSPB HrCeil HrqN2 HSTB HTS Has C1; lia
              | intros X; apply (HimgFS cid pos a HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia | clear - X HrqN2; lia] ]
      | clear - Ha HSPB HDST0 HDSTC HSTB HTS Has Hes C1; unfold ESTACK in *; lia ]
    | exact Hpres3 ]
  | apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ KgotC) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot3) | lia]
  | apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ KcellC) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell3) | lia]
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  clear KcellC KgotC Kcell3 Kgot3.
  renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
  set (ZsF := fun a : Z => Zsm a \/ res <= a < res + N \/ spZ regs - 96 - ESTACK <= a < spZ regs - 96).
  lazymatch type of KE with forall a, _ -> _ -> aview ?sg ?Hh ?mc a = aview _ _ ?m0 a =>
  assert (KE3 : forall a, 0 <= a < 2 ^ 64 -> ~ ZsF a -> aview sg Hh mem3 a = aview sg Hh m0 a)
  by (intros a Ha Hn; rewrite (Hfr3 a Ha) by (intros X; apply Hn; subst ZsF; cbn beta; right; first [left; exact X | right; exact X]);
      apply KE; [exact Ha | intros X; apply Hn; subst ZsF; cbn beta; left; exact X]) end.
  rename KE into KEc. rename KE3 into KE.
  lazymatch type of PR with forall a, apresent ?Hh ?m0 a -> apresent _ ?mc a =>
  assert (PR3 : forall a, apresent Hh m0 a -> apresent Hh mem3 a) by (intros a' Ha'; exact (Hpres3 a' (PR a' Ha'))) end.
  clear PR. rename PR3 into PR.
  assert (ZBF : forall a, SB <= a < kHighShadowEnd -> ~ ZsF a).
  { intros a Ha. subst ZsF. cbn beta. intros [X|[X|X]]; [exact (ZBsm a Ha X) | clear - Ha X HrHi HrqN2 C1 C2 C3 C4 C5; unfold rboxed in HrHi; unfold SB in Ha; lia | clear - Ha X HSPB HTS Has Hes C1 C2 C3 C4 C5; unfold SB, ESTACK in *; lia]. }
  shkOf KE ZBF SHK3.
  pose proof (RA_kept_band _ _ st 24 SHK3 ltac:(lia) ltac:(clear - Hst2 Hshi H47 C4; lia) RAstC) as RAst3.
  norm_ss HS. reshok_bx HS 22%nat.
  aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan RFC_IRD.
  all: try (oblS RAst3 E19 E22).
  { awrI Uspn E18n E8n Hown EFA2. }
  unrunRD HFr Zsm Usp B8 Usp UNf. clear HF HFr. prStep HG PR.
  pose proof (st_ok_cut 200 _ _ _ HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HSJ.
  lazymatch type of HSJ with st_ok _ _ ?ssx _ => replace ssx with ssJ in HSJ by (vm_compute; reflexivity) end.
  rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
  apply SRr_ret. unfold rd_cut. split; [reflexivity|].
  lazymatch type of HSJ with st_ok _ ?Ej _ _ =>
  lazymatch goal with |- exists E2 r2 m2 d2 r c2, {| cfg_ms := mkst ?rg _ ?mF _; cfg_model := ?dd |} = _ /\ _ =>
  exists Ej, rg, mF, dd, 0, (curv + N) end end.
  split. { reflexivity. }
  split. { exact HSJ. }
  split. { intros j Hj. rewrite ew_havoc_old by lia. rewrite ?ew_ewset_other by lia.
           first [reflexivity | rewrite AGX by exact Hj; rewrite ?ew_ewset_other by lia; reflexivity]. }
  split. { exact HJ3. }
  split. { rewrite R10. reflexivity. }
  split. { rewrite R11. agnorm. rewrite E18, E34, alu_add_small by (unfold M64; clear - HOK Hcurv Hcur Hnb HN HnbM C1; unfold MALLOC_MAX in *; lia). unfold w64. f_equal. lia. }
  split. { left. split; [reflexivity|]. split; [exact HOK|]. split; [reflexivity|].
           intros i Hi.
           rewrite (UNf (res + i)) by first [clear - Hi HrCeil HrqN2 Hr4096 C1; lia | subst Zsm; cbn beta; intros [X|[X|X]];
             [clear - X Hi HrCeil HrqN2 HSPB HTS Has C1; lia
             | apply (HimgFS cid pos (res + i) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hi HrqN2; lia]
             | clear - X Hi HrCeil HrqN2 HSTB; lia]].
           rewrite (Heff3 i Hi). cbn beta iota.
           apply KEc; [clear - Hi Hpceil HOK Hcurv Hcur Hrq2 Hph C1; lia | subst Zsm; cbn beta; unfold rboxed in Hpdst; intros [X|[X|X]];
             [clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 HSPB HTS Has C1; lia
             | clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 Hph Hpdst Hdst1 Hdst2; lia
             | clear - X Hi Hpceil HOK Hcurv Hcur Hrq2 HSTB; lia]]. }
  split. { intros a Ha N1 N2 N3 N4.
           rewrite (UNf a Ha) by (subst Zsm; cbn beta; clear - N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia).
           apply KE; [exact Ha | subst ZsF Zsm; cbn beta; clear - N1 N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia]. }
  split. { exact PR. }
  repeat (apply same_io_wvb). eapply same_io_trans; [|exact Hio3]. repeat split; reflexivity.
- rewrite branch_geu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 33 nb), (U_atom _ 18 N), (U_atom _ 34 curv), zcanon_id in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E18 | exact E34]].
  assert (HKO : nb < curv + N) by (destruct (Z.ltb_spec nb (N + curv)); [lia | discriminate Hc]). clear Hc.
  norm_ss HS. reshok_bx HS 22%nat.
  aj_run_to_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan RFC_IRD.
  { awrI Uspn E18n E8n Hown EFA2. }
  keStep HF HFr HG KE PR Zsm Usp B8 Usp.
  pose proof (st_ok_cut 200 _ _ _ HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HSJ.
  lazymatch type of HSJ with st_ok _ _ ?ssx _ => replace ssx with ssJ in HSJ by (vm_compute; reflexivity) end.
  rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
  apply SRr_ret. unfold rd_cut. split; [reflexivity|].
  lazymatch type of HSJ with st_ok _ ?Ej _ _ =>
  lazymatch goal with |- exists E2 r2 m2 d2 r c2, {| cfg_ms := mkst ?rg _ ?mF _; cfg_model := ?dd |} = _ /\ _ =>
  exists Ej, rg, mF, dd, (2 ^ 64 - 1), nb end end.
  split. { reflexivity. }
  split. { exact HSJ. }
  split. { intros j Hj. rewrite ew_havoc_old by lia. rewrite ?ew_ewset_other by lia. reflexivity. }
  split. { exact HJ2. }
  split. { rewrite R10. unfold w64. f_equal. }
  split. { rewrite R11. enorm. rewrite E33. reflexivity. }
  split. { right. split; [reflexivity|]. split; [exact HKO|]. split; [reflexivity|].
           intros i Hi. apply KE; [clear - Hi HrCeil HrqN2 Hr4096 C1; lia | subst Zsm; cbn beta; intros [X|[X|X]];
           [clear - X Hi HrCeil HrqN2 HSPB HTS Has C1; lia
           | apply (HimgFS cid pos (res + i) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hi HrqN2; lia]
           | clear - X Hi HrCeil HrqN2 HSTB; lia]]. }
  split. { intros a Ha N1 N2 N3 N4. apply KE; [exact Ha | subst Zsm; cbn beta; clear - N2 N3 N4 HTS Has Hes; unfold ESTACK in *; lia]. }
  split. { exact PR. }
  repeat split; reflexivity. }
cbv beta. intros W3 c3 _ (-> & Ej3 & regs3 & mem3 & md3 & r6 & cur6 & -> & HS3 & AGX3 & HJ3 & Ha03 & Ha13 & Hr6 & Hfr3 & Hpres3 & Hio3).
assert (HIO3 : same_io mdc md3) by (io_after Hio3). clear Hio3.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr3 by lia.
vkeep Vp (w_H W2) mem3 ltac:(apply Hfr3; unfold rboxed in Hsd; clear - Hi HSTB Hst1 Hsd HrCeil HrqN2 HSPB HTS Has C1 Hes; unfold ESTACK in *; lia).
vkeep Vn (w_H W2) mem3 ltac:(apply Hfr3; unfold rboxed in Hsd; clear - Hi HSTB Hst1 Hsd HrCeil HrqN2 HSPB HTS Has C1 Hes; unfold ESTACK in *; lia).
clear Vc RAstC HARc AGX.
rebaseJ HS HS3 AGX3 AG.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
rreg HS (10%bv : bv 5) Rr6. rewrite Ha03 in Rr6. symmetry in Rr6. unfold w64 in Rr6.
rreg HS (11%bv : bv 5) Rc6. rewrite Ha13 in Rc6. symmetry in Rc6. unfold w64 in Rc6.
assert (Hr6rng : 0 <= r6 < 2 ^ 64) by (clear - Hr6; destruct Hr6 as [(-> & _)|(-> & _)]; lia).
assert (Hcb6 : cur <= cur6 <= nb) by (clear - Hr6 Hcurv Hnb Hcur HN; destruct Hr6 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
lazymatch type of Hfr3 with forall a, _ -> _ -> _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mY a =>
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + N \/ st + 16 <= a < st + 24 \/ spZ regs - 96 - 32 - ESTACK <= a < spZ regs \/ dst <= a < dst + 16) ->
aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mY a) end.
{ intros a Ha Hn. apply (Hfr3 a Ha); clear - Hn; lia. }
pose proof (rfc_kept_stepE B _ _ _ _ _ _ _ _ _ _ _ _ (fun a => res <= a < res + req_size N) KEPT4 HSEP UN3
ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha HrqN2 HTS Has Hes; lia) ltac:(clear - HSPB; lia) ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha HrCeil; lia)
ltac:(intros b m i Hb Hi Hin; cbn beta in Hin; pose proof (HsepB b m ltac:(apply in_app_iff; right; exact Hb)) as Hd; clear - Hd Hi Hin; lia)
ltac:(intros c p a Hcp Ha Hin; cbn beta in Hin; exact (HimgFS c p a Hcp Ha Hin))
ltac:(intros a Ha Him; cbn beta in Ha; pose proof (tfib_img_range a Him) as Hir; clear - Ha Hir HrHi HrqN2; unfold rboxed in HrHi; lia)) as KEPT5.
assert (SHK3 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. rewrite (UN3 a); [apply SHK2; exact Ha | clear - Ha C2; unfold SB in Ha; lia |].
clear - Ha HrHi HrqN2 HSTB HSPB HDSTH HTS Has Hes C1 C2 C3 C4 C5. unfold rboxed in HrHi, HDSTH. unfold SB in Ha. lia. }
pose proof (RA_kept_band _ _ st 24 SHK3 ltac:(lia) ltac:(clear - Hst2 Hshi H47 C4; lia) RAst2) as RAst3. clear RAst2.
assert (HIMGa : r6 = 0 -> forall j, 0 <= j < N -> aview tfibsegs (w_H W2) mem3 (res + j) = aview tfibsegs (w_H W) memc (pdata + (curv + j))).
{ intros Hz j Hj. destruct Hr6 as [(_ & Hfit & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp j Hj). replace (pdata + curv + j) with (pdata + (curv + j)) by (clear; lia).
apply (proj1 (proj2 KEPT4) pdata nb (curv + j) Hpd). clear - Hj Hfit Hcurv Hcur Hnb HN; unfold req_size; destruct (Z.eqb_spec nb 0); lia. }
assert (HLPa : Z.land fattr 1 <> 0 -> forall j, 0 <= j < 3 * nlp -> aview tfibsegs (w_H W2) mem3 (lpa + j) = aview tfibsegs (w_H W1) mem1 (lpa + j)).
{ intros Hbit j Hj.
assert (Hpin1 : In (lpa, 3 * nlp) (ablocks B ly1 S1))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; rewrite Hpal;
destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb1|Hb1]; [exfalso; exact (Hbit Hb1) | left; reflexivity]);
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR1 Hpin1) as (_ & Hl4096 & Hlceil & _);
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ lpa (3 * nlp) cid pos HAR1 Hpin1 Hfin) as DL; rewrite EFA1 in DL; unfold zdisjoint, block_rng, frame_rng in DL; cbn [fst snd] in DL;
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hnlp; lia)) as [Hrql1 Hrql2];
pose proof (HsepB lpa (3 * nlp) ltac:(apply in_app_iff; left; rewrite Hpal; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb1|Hb1]; [exfalso; exact (Hbit Hb1) | left; reflexivity])) as DLI.
rewrite UN3; [| clear - Hl4096 Hlceil Hj Hrql2 C1; lia | clear - Hj Hrql2 DLI DL HrqN2 Hl4096 Hlceil HSTB HSPB Hdst1 Hdst2 HTS Has Hes C1; lia].
rewrite UN2; [| clear - Hl4096 Hlceil Hj Hrql2 C1; lia | subst Zsm; cbn beta; clear - Hl4096 Hlceil Hj Hrql2 DL HSPB HSTB Hdst1 Hdst2 HTS Has C1; lia].
rewrite (proj1 (proj2 HK) lpa (3 * nlp) j Hpin1 ltac:(clear - Hj Hrql2; lia)); [| cbn beta; intros [_ X]; clear - X Hj Hrql2 DLI HrqN2; lia].
apply UN1; [clear - Hl4096 Hlceil Hj Hrql2 C1; lia | subst Zsm; cbn beta; clear - Hl4096 Hlceil Hj Hrql2 DL HSPB HSTB Hdst1 Hdst2 HTS Has C1; lia]. }
clear KEPT4 UN3 UN2 SHK2 Hfr3 Hpres3 Ha03 UN1 HK.
reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblS RAst3 E19 E22).
{ awrI Uspn E18n E8n Hown EFA2. }
unrunRD HFr Zsm Usp B8 Usp UN4. clear HF HFr HG.
vkeepUN2 UN4 Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
try clear Vc. lazymatch type of Rc6 with ew _ ?n11 = _ => field_at HS 4%nat 19%nat st B18n 16 8%N n11 cur6 Rc6 Vc end.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT5 HSEP UN4 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT6. clear KEPT5.
lazymatch type of UN4 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (SHK4 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) m2 a = aview tfibsegs (w_H W2) mem2 a)
by (intros a Ha; rewrite (UN4 a); [exact (SHK3 a Ha) | clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHK4 ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst2) as RAdst4. clear SHK3.
assert (E20n : forall Ex, (forall m, (m < 33)%nat -> ew Ex m = ew E m) -> ew Ex 25 = Z_to_bv 64 racc) by (intros Ex AGx; rewrite (AGx 25%nat) by lia; exact E25).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
-
lazymatch type of Rr6 with ew _ ?n6 = _ => lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
rewrite branch_eq_U, (U_or_atoms Ex n6 25 r6 racc ltac:(rewrite ?ew_ewset_other by lia; exact Rr6) ltac:(rewrite ?ew_ewset_other by lia; exact (E20n _ AG)) Hr6rng HR), U_SLit in Hc end end.
change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. apply Z.lor_eq_0_iff in Hc. destruct Hc as [Hz6 Hz20].
assert (Hcv : curv + N <= nb /\ cur6 = curv + N) by (clear - Hr6 Hz6; destruct Hr6 as [(_ & X & Y & _)|(X & _)]; [split; assumption | exfalso; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan.
{ awrI Uspn E18n E8n Hown EFA2. }
unrunRD HFr Zsm Usp B8 Usp UN5. clear HF HFr HG.
vkeepUN2 UN5 Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
try clear Vc. lazymatch type of Rc6 with ew _ ?n11 = _ => field_at HS 4%nat 19%nat st B18n 16 8%N n11 cur6 Rc6 Vc end.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT6 HSEP UN5 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT7. clear KEPT6.
rreg HS (10%bv : bv 5) Q10. rreg HS (1%bv : bv 5) Q1.
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem]. unfold rfc_post.
lazymatch goal with |- exists ly3 S3 r3 m3 d3 res3 cur3, {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem _) _; cfg_model := ?dd |} = _ /\ _ =>
exists ly2, S2, (ms_regs msF), (ms_mem msF), dd, 1, cur6 end.
split. { rewrite Q1, E36, Hra. reflexivity. }
split. { eapply (ajournal_mono_k tfibsegs B); [apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ3 | rewrite HEV; clear - Hk1; lia]. }
split. { apply aregs_preserved_eqs; cregI HS Usp. }
split. { rewrite Hfrs2. exact Hfrs1. }
split.
{ rewrite Q10. first [ reflexivity
| lazymatch type of Rr6 with ew ?Ex ?n6 = _ => rewrite Rr6, (E20n Ex AG), (alu_seqz_or r6 racc Hr6rng HR), Hz6, Hz20; reflexivity end ]. }
destruct KEPT7 as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [io_now|].
split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcb6; lia|].
split. { apply (mle_weaken MT Sc S2 _ _ MTL (mle_station MT Sc S1 S2 acc (mo_malloc MT N) MTL HMLE HMLE2)). unfold RFC_COST. pose proof (mo_free_nonneg MT MTL) as Hf0. clear - Hacc Hf0. lia. }
field_at HS 3%nat 8%nat dst B8n 0 8%N 35%nat lpa E35 Vl.
lazymatch type of Rres with ew _ ?nres = _ => field_at HS 3%nat 8%nat dst B8n 8 8%N nres res Rres Vi end.
field_at HS 3%nat 8%nat dst B8n 16 4%N 48%nat fattr E48 Vfa.
field_at HS 3%nat 8%nat dst B8n 20 4%N 49%nat fgen E49 Vfg.
field_at HS 3%nat 8%nat dst B8n 24 2%N 50%nat delay E50 Vde.
field_at HS 3%nat 8%nat dst B8n 26 2%N 51%nat nlp E51 Vnl.
field_at HS 3%nat 8%nat dst B8n 28 1%N 52%nat tidx E52 Vti.
right. split; [reflexivity|].
exists lpa, lpa, res, fattr, fgen, delay, nlp, tidx, (firstn (Z.to_nat (palsz fattr nlp)) (skipn (Z.to_nat (cur + 9)) P)), (firstn (Z.to_nat N) (skipn (Z.to_nat curv) P)).
split.
{ cbn [obj_at LAY_FrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 1)) with 256.
rewrite Z.add_0_r.
repeat split; first [assumption | exact I | clear - Hlpa Hr4096 HrCeil HrqN1 Hfattr Hfgen Hdelay Hnlp Htidx C1; lia]. }
split; [intros X; exact (Hlpa0 X)|].
split; [reflexivity|].
split; [rewrite <- Hpal; exact HPerm2|].
split.
{ intros b [<- | Hb].
+ split; [exact Timg|]. intros blc i Hblc Hi. exact (Aimg blc i ly2 Hblc Hi).
+ rewrite <- Hpal in Hb. destruct (Hpaltok b Hb) as [T1 T2]. split; [exact T1|]. intros blc i Hblc Hi. exact (T2 ly2 blc i Hblc Hi). }
destruct Hprog as [(HR0 & Hfit & Ecv & HLP) | (Habs & _)]; [| exfalso; apply Habs; exact Hz20].
assert (Hps : 0 <= palsz fattr nlp <= 3 * nlp) by (unfold palsz; destruct (Z.land fattr 1 =? 0); clear - Hnlp; lia).
destruct Hcv as [HfitI Ecur6].
destruct (Hhdrv ltac:(clear - Hfit Hps; lia)) as (Efa & Efg & Ede & Eti & Enl).
assert (Epz : hdr_palsz (hb P cur 0) (hb P cur 1) (hb P cur 7) (hb P cur 8) = palsz fattr nlp).
{ unfold hdr_palsz, YO07.flag, palsz. rewrite <- Efa, <- Enl. destruct (Z.land fattr 1 =? 0); reflexivity. }
split.
{ rewrite Ecur6, Ecv, Efa, Efg, Ede, Eti, Enl. rewrite Efa, Enl in Epz. rewrite <- Epz.
apply (parse_frameN_ok N P cur); [clear - Hcur; lia | clear - HN; lia | unfold hdr_at, hb; rewrite Z.add_0_r; repeat split; reflexivity | rewrite <- Enl; clear - Hnlp; lia
| rewrite Epz, HlenP; rewrite <- Efa, <- Enl; rewrite Ecv in HfitI; exact HfitI]. }
split.
{
apply garr8_of_aview. intros j Hj. rewrite firstn_length_le in Hj by (rewrite length_skipn; clear - HfitI HlenP Hcurv Hcur HN; lia).
rewrite slice_nth by (rewrite firstn_length_le by (rewrite length_skipn; clear - HfitI HlenP Hcurv Hcur HN; lia); exact Hj).
rewrite UN5; [| clear - Hr4096 HrCeil Hj HN HrqN2 C1; lia
| subst Zsm; cbn beta; intros [X|[X|X]]; [clear - X Hr4096 HrCeil Hj HrqN2 HN HSPB HTS Has C1; lia
| apply (HimgFS cid pos (res + Z.of_nat j) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hj HrqN2 HN; lia]
| clear - X Hr4096 HrCeil Hj HrqN2 HN HSTB; lia]].
rewrite UN4; [| clear - Hr4096 HrCeil Hj HN HrqN2 C1; lia
| subst Zsm; cbn beta; intros [X|[X|X]]; [clear - X Hr4096 HrCeil Hj HrqN2 HN HSPB HTS Has C1; lia
| apply (HimgFS cid pos (res + Z.of_nat j) HfinC); [left; unfold in_zr, frame_rng; cbn [fst snd]; clear - X Hdst1 Hdst2; lia | clear - Hj HrqN2 HN; lia]
| clear - X Hr4096 HrCeil Hj HrqN2 HN HSTB; lia]].
rewrite (HIMGa Hz6 (Z.of_nat j)) by (clear - Hj; lia).
replace (pdata + (curv + Z.of_nat j)) with (pdata + Z.of_nat (Z.to_nat curv + j)) by (clear - Hcurv Hcur; lia).
rewrite (garr8_aview _ _ _ _ HPL) by (clear - Hj HfitI HlenP Hcurv Hcur; lia). reflexivity. }
split; [rewrite firstn_length_le by (rewrite length_skipn; clear - HfitI HlenP Hcurv Hcur HN; lia); clear - HN; lia|].
intros Hbit.
assert (Hpin1 : In (lpa, 3 * nlp) (ablocks B ly1 S1))
by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; rewrite Hpal;
destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb1|Hb1]; [exfalso; exact (Hbit Hb1) | left; reflexivity]);
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR1 Hpin1) as (_ & Hl4096 & Hlceil & _);
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ lpa (3 * nlp) cid pos HAR1 Hpin1 Hfin) as DL; rewrite EFA1 in DL; unfold zdisjoint, block_rng, frame_rng in DL; cbn [fst snd] in DL;
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hnlp; lia)) as [Hrql1 Hrql2];
pose proof (HsepB lpa (3 * nlp) ltac:(apply in_app_iff; left; rewrite Hpal; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb1|Hb1]; [exfalso; exact (Hbit Hb1) | left; reflexivity])) as DLI.
assert (Hps3 : palsz fattr nlp = 3 * nlp) by (unfold palsz; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb1|Hb1]; [exfalso; exact (Hbit Hb1) | reflexivity]).
rewrite Hps3. split; [| rewrite firstn_length_le by (rewrite length_skipn; clear - Hfit HlenP Hps3 HN Hcur; lia); clear - Hnlp; lia].
eapply garr8_kept_aview; [|exact (HLP Hbit)]. intros i Hi. rewrite firstn_length_le in Hi by (rewrite length_skipn; clear - Hfit HlenP Hps3 HN Hcur; lia).
rewrite UN5; [| clear - Hl4096 Hlceil Hi Hrql2 C1; lia
| subst Zsm; cbn beta; clear - Hl4096 Hlceil Hi Hrql2 DL HSPB HSTB Hdst1 Hdst2 HTS Has C1; lia].
rewrite UN4; [| clear - Hl4096 Hlceil Hi Hrql2 C1; lia
| subst Zsm; cbn beta; clear - Hl4096 Hlceil Hi Hrql2 DL HSPB HSTB Hdst1 Hdst2 HTS Has C1; lia].
apply (HLPa Hbit i). clear - Hi Hnlp; lia.
-
lazymatch type of Rr6 with ew _ ?n6 = _ => lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
rewrite branch_eq_U, (U_or_atoms Ex n6 25 r6 racc ltac:(rewrite ?ew_ewset_other by lia; exact Rr6) ltac:(rewrite ?ew_ewset_other by lia; exact (E20n _ AG)) Hr6rng HR), U_SLit in Hc end end.
change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into Hnz.
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblD RAdst4 E8 E22).
{ awrI Uspn E18n E8n Hown EFA2. }
unrunRD HFr Zsm Usp B8 Usp UN5. clear HF HFr HG.
vkeepUN2 UN5 Vp Vn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
try clear Vc. lazymatch type of Rc6 with ew _ ?n11 = _ => field_at HS 4%nat 19%nat st B18n 16 8%N n11 cur6 Rc6 Vc end.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT6 HSEP UN5 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT7. clear KEPT6.
lazymatch type of UN5 with forall a, _ -> _ -> aview _ _ ?m2 a = aview _ _ ?m1 a =>
assert (SHK5 : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W2) m2 a = aview tfibsegs (w_H W2) m1 a)
by (intros a Ha; apply (UN5 a); [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHK5 ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst4) as RAdst5. clear UN5 SHK5 RAdst4.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 338220) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly2 (aview tfibsegs (w_H W2) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly2 _ (spZ regs - 96) dst []).
- apply achain_low; clear - HDST0 HDSTC; lia.
- unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - HSPB C1 HTS Has; unfold spZ in *; lia.
- unfold s0Z; rewrite Rs0; enorm; agnorm; rewrite E8; apply unsigned_lit_small; clear - HDST0 HDSTC C1; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly2 S2 W2 (ms_mem ?msX) _ _ |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => pose proof HJc as HJ3c end.
pose proof HJ3c as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W2 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
ly2 S2 mdX (k1 + 1) res N (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_F1) [] HJ3c HrIn);
[ rewrite Ra0; enorm; agnorm; unfold w64; rewrite Rres; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia | clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| rewrite HEV in Hev; clear - Hnev3 Hev Hk1; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
| intros Hin0 i Hi; exact (Timg Hin0 i Hi)
|
apply (mok_station MT Sc S2 T (acc + mo_malloc MT N) (mo_free MT) MTL HMOK (mle_station MT Sc S1 S2 acc (mo_malloc MT N) MTL HMLE HMLE2)); [apply (mo_free_nonneg MT MTL)|];
unfold RFC_COST in HCOST; pose proof (mo_free_nonneg MT MTL) as Hf0; clear - Hacc HCOST Hf0; lia ] end. }
cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 CH.
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl2 & Ebl4) & Hfrs4 & HK4 & HMLE4 & HJS4).
assert (HIO4 : same_io mdc md4) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sink_closed_ablocks_fp [(res, N)] ltac:(constructor; [cbn [fst]; clear - Hr4096; lia | constructor])) HJS4)). clear HJS4.
pose proof (mle_station MT Sc S2 S4 _ _ MTL (mle_station MT Sc S1 S2 acc (mo_malloc MT N) MTL HMLE HMLE2) HMLE4) as HMLE4c. clear HMLE4.
pose proof (proj1 HJ4) as HAR4. pose proof HJ4 as (_ & Hly4 & _ & _ & _ & _ & Hnev4 & _).
assert (EFA4 : forall c p, frame_addr ly4 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly4 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HdstA4 : frame_addr ly4 cid pos <= dst) by (rewrite EFA4; exact Hdst1).
assert (HdstB4 : dst + 32 <= frame_addr ly4 cid pos + fs_frame_bytes cid) by (rewrite EFA4; exact Hdst2).
assert (HPerm4 : Permutation (ablocks B ly4 S4) (pal ++ Bb)).
{ rewrite Ebl4. apply Permutation_sym. apply (@Permutation_cons_app_inv _ (pal ++ Bb) l1 l2 (res, N)). rewrite <- Ebl2. apply Permutation_sym. exact HPerm2. }
assert (Hfin4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact Hfin2).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR4 Hfin4) as (_ & _ & HFpres4 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3c)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR4) as (Kcell4 & _ & Kgot4 & _). rewrite HBgot, HBcell in Kgot4. rewrite HBcell in Kcell4.
assert (HBb2 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly2 S2)).
{ intros b m Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. apply in_app_iff. right. exact Hb. }
vkeep Vp (w_H W4) mem4 ltac:(apply (proj1 HK4); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vn (w_H W4) mem4 ltac:(apply (proj1 HK4); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vc (w_H W4) mem4 ltac:(apply (proj1 HK4); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
pose proof (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ ly2 S2 _ _ _ _ _ KEPT7 HK4 ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb2
ltac:(intros b m i Hb Hi Hin; pose proof (HsepB b m ltac:(apply in_app_iff; right; exact Hb)); clear - Hi Hin H; lia)
ltac:(rewrite Hfrs2; exact Hfrs1) EFA2 HimgFS) as KEPT8. clear KEPT7.
assert (RAdst6 : range_addressable (aview tfibsegs (w_H W4) mem4) SHADOW_OFF dst 32).
{ eapply (RA_kept_call B ly2 S2); [exact HK4 | exact Hfin2 | intros a [Ha Ha2]; clear - Ha Ha2 HrHi HrqN2; unfold rboxed in HrHi; lia | exact Hcid | rewrite EFA2; exact Hfal
| rewrite EFA2; clear - HFhi1; lia | rewrite EFA2; exact HFceil | exact HdstA2 | exact HdstB2 | exact RAdst5]. }
clear RAdst5.
reseatL HS HJ4 HP4 [0; 1; 2; 3]%nat AG
ltac:(first [ eapply (region_kept_stack_aj tfibsegs B); [exact HK4 | exact HJ4 | evalER AG | clear - HTS Has; lia | clear - Hwlo HTS Has; lia | clear - Hwhi; lia | cbn; lia | cbn; lia]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot3) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot4) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell3) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell4) | lia]
| eapply (region_kept_ownframe_aj tfibsegs _); [exact HK4 | evalER AG | exact Hfin2 | left; cbn [YP09.r_lo YP09.r_hi]; clear - HdstA2 HdstB2; lia
| cbn [YP09.r_lo YP09.r_hi]; intros a Ha; apply (HimgFS cid pos a HfinC); left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia
| intros a Ha; apply (fun H => proj1 (HFpres4 a H)); clear - Ha HdstA4 HdstB4; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell3 Kgot3 Kcell4 Kgot4.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RBspan.
all: try (oblD RAdst6 E8 E22).
{ awrI Uspn E18n E8n Hown EFA4. }
unrunRD HFr Zsn Usp B8 Usp UN6. clear HF HFr HG.
vkeepUN UN6 Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsn; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsn KEPT8 HSEP UN6 ltac:(intros a Ha; subst Zsn; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT9. clear KEPT8 UN6.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 338220) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly4 (aview tfibsegs (w_H W4) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly4 _ (spZ regs - 96) dst []).
- apply achain_low; clear - HDST0 HDSTC; lia.
- unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; clear - HSPB C1 HTS Has; unfold spZ in *; lia.
- unfold s0Z; rewrite Rs0; enorm; agnorm; rewrite E8; apply unsigned_lit_small; clear - HDST0 HDSTC C1; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly4 S4 W4 (ms_mem ?msX) _ _ |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => pose proof HJc as HJ4c end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (TAIL : forall W5 ly5 S5 (regs5 : bvmap 5 word) mem5 md5 (Er : Z -> Prop),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly5 S5 W5 mem5 md5 (k1 + 1 + 1 + 1) ->
aregs_preserved (ms_regs msX) regs5 -> Permutation (ablocks B ly5 S5) Bb -> frames S5 = frames S4 ->
acall_kept tfibsegs B ly4 S4 W4 (ms_mem msX) W5 mem5 (sp0 + (spZ regs - 96 - sp0) - ASTACK) (sp0 + (spZ regs - 96 - sp0)) Er ->
(forall a, Er a -> a < alloc_ceiling) ->
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> ~ Er (b + i)) ->
(forall c p a, In (c, p) (frames Sc) -> (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ Er a) ->
mo_le MT Sc S5 (RFC_COST MT N) ->
same_io mdc md5 ->
SRr tfibsegs W5 (mkCfg (mkst regs5 (Z_to_bv 64 RFC_F2) mem5 (seg_rom tfibsegs)) md5)
(rfc_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs Bb st dst N pdata nb cur lyc Sc W memc mdc P)) end.
{ intros W5 ly5 S5 regs5 mem5 md5 Er HJ5 HP5 HPerm5 Hfrs5 HK5 HErC HErB HErF HMLE5 HIO5.
pose proof (proj1 HJ5) as HAR5. pose proof HJ5 as (_ & Hly5 & _).
assert (EFA5 : forall c p, frame_addr ly5 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly5 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HdstA5 : frame_addr ly5 cid pos <= dst) by (rewrite EFA5; exact Hdst1).
assert (HdstB5 : dst + 32 <= frame_addr ly5 cid pos + fs_frame_bytes cid) by (rewrite EFA5; exact Hdst2).
assert (Hfin5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR5 Hfin5) as (_ & _ & HFpres5 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ4c)) as (Kcell4 & _ & Kgot4 & _). rewrite HBgot, HBcell in Kgot4. rewrite HBcell in Kcell4.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR5) as (Kcell5 & _ & Kgot5 & _). rewrite HBgot, HBcell in Kgot5. rewrite HBcell in Kcell5.
assert (HBb4 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly4 S4)).
{ intros b m Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. apply in_app_iff. right. exact Hb. }
vkeep Vp (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi HSTB; lia | clear - Hi Hst1 HTS Has; lia]).
vkeep Vn (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi HSTB; lia | clear - Hi Hst1 HTS Has; lia]).
vkeep Vc (w_H W5) mem5 ltac:(apply (proj1 HK5); [clear - Hi HSTB; lia | clear - Hi Hst1 HTS Has; lia]).
pose proof (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ ly4 S4 _ _ _ _ _ KEPT9 HK5 ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb4 HErB
ltac:(rewrite Hfrs4, Hfrs2; exact Hfrs1) EFA4 HErF) as KEPT10.
reseatL HS HJ5 HP5 [0; 1; 2; 3]%nat AG
ltac:(first [ eapply (region_kept_stack_aj tfibsegs B); [exact HK5 | exact HJ5 | evalER AG | clear - HTS Has; lia | clear - Hwlo HTS Has; lia | clear - Hwhi; lia | cbn; lia | cbn; lia]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot4) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot5) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell4) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell5) | lia]
| eapply (region_kept_ownframe_aj tfibsegs _); [exact HK5 | evalER AG | exact Hfin4 | left; cbn [YP09.r_lo YP09.r_hi]; clear - HdstA4 HdstB4; lia
| cbn [YP09.r_lo YP09.r_hi]; intros a Ha; apply (HErF cid pos a HfinC); left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia
| intros a Ha; apply (fun H => proj1 (HFpres5 a H)); clear - Ha HdstA5 HdstB5; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell4 Kgot4 Kcell5 Kgot5.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ5 SHOK RBspan.
{ awrI Uspn E18n E8n Hown EFA5. }
unrunRD HFr Zsn Usp B8 Usp UN7. clear HF HFr HG.
vkeepUN UN7 Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsn; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsn KEPT10 HSEP UN7 ltac:(intros a Ha; subst Zsn; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT11. clear KEPT10 UN7.
rreg HS (10%bv : bv 5) Q10. rreg HS (1%bv : bv 5) Q1.
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx W5 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem]. unfold rfc_post.
lazymatch goal with |- exists ly3 S3 r3 m3 d3 res3 cur3, {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem _) _; cfg_model := ?dd |} = _ /\ _ =>
exists ly5, S5, (ms_regs msF), (ms_mem msF), dd, 0, cur6 end.
split. { rewrite Q1, E36, Hra. reflexivity. }
split. { eapply (ajournal_mono_k tfibsegs B); [apply (ajournal_materialize tfibsegs B LAWS Hsegs); exact HJ5 | rewrite HEV; clear - Hk1; lia]. }
split. { apply aregs_preserved_eqs; cregI HS Usp. }
split. { rewrite Hfrs5, Hfrs4, Hfrs2. exact Hfrs1. }
split.
{ rewrite Q10. first [ reflexivity
| lazymatch type of Rr6 with ew ?Ex ?n6 = _ => rewrite Rr6, (E20n Ex AG), (alu_seqz_or r6 racc Hr6rng HR);
destruct (Z.eqb_spec (Z.lor r6 racc) 0) as [X|X]; [exfalso; exact (Hnz X) | reflexivity] end ]. }
destruct KEPT11 as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [io_now|].
split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcb6; lia|].
split; [exact HMLE5|].
left. split; [reflexivity|]. split; [|exact HPerm5].
assert (Hps : 0 <= palsz fattr nlp) by (unfold palsz; destruct (Z.land fattr 1 =? 0); clear - Hnlp; lia).
apply (parse_frameN_fail N P cur (hb P cur 0) (hb P cur 1) (hb P cur 2) (hb P cur 3) (hb P cur 4) (hb P cur 5) (hb P cur 6) (hb P cur 7) (hb P cur 8));
[clear - Hcur; lia | clear - HN; lia |].
destruct (Z_lt_le_dec nb (cur + 9)) as [Hlt | Hge]; [left; rewrite HlenP; exact Hlt | right].
destruct (Hhdrv Hge) as (Efa & Efg & Ede & Eti & Enl).
split; [unfold hdr_at, hb; rewrite Z.add_0_r; repeat split; reflexivity|]. split; [rewrite <- Enl; clear - Hnlp; lia|].
replace (hdr_palsz (hb P cur 0) (hb P cur 1) (hb P cur 7) (hb P cur 8)) with (palsz fattr nlp)
by (unfold hdr_palsz, YO07.flag, palsz; rewrite <- Efa, <- Enl; destruct (Z.land fattr 1 =? 0); reflexivity).
rewrite HlenP.
destruct Hprog as [(HR0 & Hfit & Ecv & _) | (_ & Hsh & Ecv)]; [| clear - Hsh HN; lia].
destruct Hr6 as [(Hz6 & _)|(_ & Hsh6 & _)]; [exfalso; apply Hnz; rewrite Hz6, HR0; reflexivity | clear - Hsh6 Ecv; lia]. }
destruct (Z.land fattr 1 =? 0) eqn:Hbit.
+
assert (Hl0 : lpa = 0) by (apply Hlpa0; apply Z.eqb_eq; exact Hbit).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (afree_null04_sub tfibsegs B LAWS tfib_segs_low MT AFREEN4 W4 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
ly4 S4 mdX (k1 + 1 + 1) (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_F2) [] HJ4c);
[ rewrite Ra0; enorm; agnorm; rewrite E35, Hl0; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia | clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| rewrite HEV in Hev; clear - Hnev4 Hev Hk1; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
|
apply (mok_station MT Sc S4 T _ (mo_free MT) MTL HMOK HMLE4c); [apply (mo_free_nonneg MT MTL)|];
unfold RFC_COST in HCOST; clear - Hacc HCOST; lia ] end. }
cbv beta. clear CH. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HK5 & HMLE5 & HJS5).
assert (HIO5 : same_io mdc md5) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJS5)). clear HJS5.
apply (TAIL W5 ly5 S5 regs5 mem5 md5 (fun _ => False) HJ5 HP5);
[ eapply Permutation_trans; [exact HPerm5|]; rewrite Hpal, ?Hbit in HPerm4; cbn [app] in HPerm4; exact HPerm4
| exact Hfrs5 | exact HK5 | intros a F; destruct F | intros b m i _ _ F; exact F | intros c p a _ _ F; exact F
| apply (mle_weaken MT Sc S5 _ _ MTL (mle_station MT Sc S4 S5 _ _ MTL HMLE4c HMLE5)); unfold RFC_COST; clear - Hacc; lia
| exact HIO5 ].
+
assert (Hpin4 : In (lpa, 3 * nlp) (ablocks B ly4 S4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. rewrite Hpal, ?Hbit. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR4 Hpin4) as (_ & Hl4096 & Hlceil & _).
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hnlp; lia)) as [Hrql1 Hrql2].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W4 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
ly4 S4 mdX (k1 + 1 + 1) lpa (3 * nlp) (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_F2) [] HJ4c Hpin4);
[ rewrite Ra0; enorm; agnorm; unfold w64; rewrite E35; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia | clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| rewrite HEV in Hev; clear - Hnev4 Hev Hk1; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
| intros Hin0 i Hi; exact (proj1 (Hpaltok _ ltac:(rewrite Hpal, ?Hbit; left; reflexivity)) Hin0 i Hi)
|
apply (mok_station MT Sc S4 T _ (mo_free MT) MTL HMOK HMLE4c); [apply (mo_free_nonneg MT MTL)|];
unfold RFC_COST in HCOST; clear - Hacc HCOST; lia ] end. }
cbv beta. clear CH. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1' & l2' & Ebl4' & Ebl5) & Hfrs5 & HK5 & HMLE5 & HJS5).
assert (HIO5 : same_io mdc md5) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sink_closed_ablocks_fp [(lpa, 3 * nlp)] ltac:(constructor; [cbn [fst]; clear - Hl4096; lia | constructor])) HJS5)). clear HJS5.
rewrite Hpal, ?Hbit in HPerm4. cbn [app] in HPerm4.
assert (HPerm5 : Permutation (ablocks B ly5 S5) Bb).
{ rewrite Ebl5. apply Permutation_sym. apply (@Permutation_cons_app_inv _ Bb l1' l2' (lpa, 3 * nlp)). rewrite <- Ebl4'. apply Permutation_sym. exact HPerm4. }
apply (TAIL W5 ly5 S5 regs5 mem5 md5 (fun a => lpa <= a < lpa + req_size (3 * nlp)) HJ5 HP5 HPerm5 Hfrs5 HK5);
[| | | apply (mle_weaken MT Sc S5 _ _ MTL (mle_station MT Sc S4 S5 _ _ MTL HMLE4c HMLE5)); unfold RFC_COST; clear - Hacc; lia | exact HIO5].
* intros a Ha. clear - Ha Hlceil. lia.
* intros b m i Hb Hi Hin. destruct (in_split _ _ Hb) as (k1' & k2' & El).
assert (HP' : Permutation (ablocks B ly4 S4) ((lpa, 3 * nlp) :: (b, m) :: k1' ++ k2')).
{ eapply Permutation_trans; [exact HPerm4|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR4 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D Hi Hin. lia.
* intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
-- pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ lpa (3 * nlp) c p HAR4 Hpin4 ltac:(rewrite Hfrs4, Hfrs2, Hfrs1; exact Hcp)) as D.
rewrite EFA4 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin. lia.
-- destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR4 ltac:(rewrite Hfrs4, Hfrs2, Hfrs1; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA4 in F0, Fc, Fh.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR4 Hpin4) as (_ & _ & _ & Hlh_ia & _).
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin Hlh_ia Hrql2 C2 C3. zones. lia.
Qed.
End RI.
End d.
