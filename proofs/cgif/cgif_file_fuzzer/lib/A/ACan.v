(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACam ACai.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma ra_le_byte_of_sum4 : forall (u : nat -> Z) k, (forall j, 0 <= u j < 256) -> (k < 4)%nat ->
le_byte (u 0%nat + 256 * (u 1%nat + 256 * (u 2%nat + 256 * u 3%nat))) 4 k = u k.
Proof.
intros u k Hu Hk.
pose proof (Hu 0%nat). pose proof (Hu 1%nat). pose proof (Hu 2%nat). pose proof (Hu 3%nat).
unfold le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia.
destruct k as [|[|[|[|k]]]]. 5: lia.
all: cbn -[Z.add Z.mul Z.modulo Z.div].
all: clear Hu Hk.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
all: nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma ra_val_mem_of_present4 : forall H mem a,
(forall i, 0 <= i < 4 -> apresent H mem (a + i)) ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem SEGS (mrestrict H mem) a 4 v.
Proof.
intros H mem a HP.
set (u := fun j : nat => match mbyte SEGS (mrestrict H mem) (a + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end).
assert (Hu : forall j, 0 <= u j < 256 /\ ((j < 4)%nat -> mbyte SEGS (mrestrict H mem) (a + Z.of_nat j) = Some (Z_to_bv 8 (u j)))).
{ intros j. subst u. cbv beta. destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat j)) as [b|] eqn:Hb.
- pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [lia|]. intros _. rewrite Z_to_bv_bv_unsigned. reflexivity.
- split; [lia|]. intros Hj. exfalso. pose proof (aview_some_of_apresent SEGS H mem (a + Z.of_nat j) (HP (Z.of_nat j) ltac:(lia))) as X.
unfold aview in X. rewrite Hb in X. apply X. reflexivity. }
exists (u 0%nat + 256 * (u 1%nat + 256 * (u 2%nat + 256 * u 3%nat))).
pose proof (proj1 (Hu 0%nat)). pose proof (proj1 (Hu 1%nat)). pose proof (proj1 (Hu 2%nat)). pose proof (proj1 (Hu 3%nat)).
split; [lia|].
intros k Hk. rewrite (proj2 (Hu k) Hk). f_equal. f_equal. symmetry. apply ra_le_byte_of_sum4; [intros j; apply (proj1 (Hu j)) | exact Hk].
Qed.
Lemma ra_vals_of : forall cx E,
ew E 33 = Z_to_bv 64 (c_gct cx) -> ew E 34 = Z_to_bv 64 (c_rattr cx) -> ew E 35 = Z_to_bv 64 (c_Wd cx) ->
ew E 36 = Z_to_bv 64 (c_Hd cx) -> ew E 37 = Z_to_bv 64 (c_sgct cx) -> ew E 38 = Z_to_bv 64 (c_loops cx) ->
ew E 39 = Z_to_bv 64 (c_rcur cx) -> ew E 40 = Z_to_bv 64 SB -> ew E 41 = Z_to_bv 64 (c_lct cx) ->
ew E 42 = Z_to_bv 64 (c_img cx) -> ew E 43 = Z_to_bv 64 (c_fattr cx) -> ew E 44 = Z_to_bv 64 (c_w cx) ->
ew E 45 = Z_to_bv 64 (c_h cx) -> ew E 46 = Z_to_bv 64 (c_top cx) -> ew E 47 = Z_to_bv 64 (c_left cx) ->
ew E 48 = Z_to_bv 64 (c_delay cx) -> ew E 49 = Z_to_bv 64 (c_slct cx) -> ew E 50 = Z_to_bv 64 (c_disp cx) ->
ew E 51 = Z_to_bv 64 (c_tidx cx) -> ew E 52 = Z_to_bv 64 (c_ctx cx) ->
ew E 53 = Z_to_bv 64 (c_wfn cx) -> ew E 54 = Z_to_bv 64 (c_hw cx) -> ew E 55 = Z_to_bv 64 (c_uar cx) ->
forall j, (1 <= j < 24)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (ra_vals cx) 0).
Proof.
intros cx E H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50 H51 H52 H53 H54 H55 j Hj.
do 24 (try (destruct j as [|j]; [first [assumption | lia] |])). lia.
Qed.
Lemma st_ok_fact_In : forall segs E ss ms n af,
st_ok segs E ss ms -> In (n, af) (f_atoms (ss_facts ss)) -> afact_ok E n af.
Proof.
intros segs E ss ms n af HS Hin. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (Ha & _ & _)).
pose proof (atoms_ok_incl E _ [(n, af)] ltac:(intros x [<-|[]]; exact Hin) Ha) as [H _]. exact H.
Qed.
End f.
End d.
Ltac fact_of HS n H :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let rec find l := lazymatch l with (n, ?af) :: _ => af | _ :: ?t => find t end in
let af := find fa in
pose proof (st_ok_fact_In _ Ev _ msx n af HS ltac:(cbn [abs_ss setpc f_atoms ss_facts In]; repeat (first [left; reflexivity | right]))) as H;
unfold afact_ok in H; cbn [af_lo af_hi af_al2] in H;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in H; rewrite ?ew_ewset_other in H by lia | st_ok _ ?Ev ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let rec find l := lazymatch l with (n, ?af) :: _ => af | _ :: ?t => find t end in
let af := find fa in
pose proof (st_ok_fact_In _ Ev ssx msx n af HS ltac:(cbn [f_atoms ss_facts In]; repeat (first [left; reflexivity | right]))) as H;
unfold afact_ok in H; cbn [af_lo af_hi af_al2] in H;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in H; rewrite ?ew_ewset_other in H by lia  end.
Ltac ra_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws _ ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HINV HS;
destruct cx as [ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h topv leftv delay slct disp tidx Nimg rest cid pos fpos wfn hw uar E0];
pose proof HBASE as HBASE0;
unfold ra_base in HBASE; unfold ra_E in HEE; red in HINV; unfold ra_vals, ra_F, ra_FL in HBASE, HEE;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0] in HBASE, HEE, HJ3, Hfrs3, HINV;
destruct HBASE as (HPRE & Hal32 & Hctx & Hroom & HROD & H10 & H11 & (Hfin & Hcid0 & Hfal & Hflo & Hfhi & Hcal & HRA) & Hcfg & Hraw & Hsg
& Mgw & Mgf & Rctx & Mg80 & Hw & Hh & HnP & HnPN & HPerm & Hlct & Hev & Hlive & EE & EX & Usp & Rwfn & Rhw & WFN & Huar);
subst uar;
destruct HEE as (AG & EXE & RF & E528 & E529 & HEI);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TRAWADD_STK = 17040) by reflexivity;
assert (HEV : EV_RAWADD = 27) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (E10 : ew E0 10 = Z_to_bv 64 raw) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10);
assert (E11 : ew E0 11 = Z_to_bv 64 cfp) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof (EX 0%nat ltac:(lia)) as E32; cbn [Nat.add nth] in E32;
pose proof (EXE 1%nat ltac:(lia)) as E33;
pose proof (EXE 2%nat ltac:(lia)) as E34;
pose proof (EXE 3%nat ltac:(lia)) as E35;
pose proof (EXE 4%nat ltac:(lia)) as E36;
pose proof (EXE 5%nat ltac:(lia)) as E37;
pose proof (EXE 6%nat ltac:(lia)) as E38;
pose proof (EXE 7%nat ltac:(lia)) as E39;
pose proof (EXE 8%nat ltac:(lia)) as E40;
pose proof (EXE 9%nat ltac:(lia)) as E41;
pose proof (EXE 10%nat ltac:(lia)) as E42;
pose proof (EXE 11%nat ltac:(lia)) as E43;
pose proof (EXE 12%nat ltac:(lia)) as E44;
pose proof (EXE 13%nat ltac:(lia)) as E45;
pose proof (EXE 14%nat ltac:(lia)) as E46;
pose proof (EXE 15%nat ltac:(lia)) as E47;
pose proof (EXE 16%nat ltac:(lia)) as E48;
pose proof (EXE 17%nat ltac:(lia)) as E49;
pose proof (EXE 18%nat ltac:(lia)) as E50;
pose proof (EXE 19%nat ltac:(lia)) as E51;
pose proof (EXE 20%nat ltac:(lia)) as E52;
pose proof (EXE 21%nat ltac:(lia)) as E53;
pose proof (EXE 22%nat ltac:(lia)) as E54;
pose proof (EXE 23%nat ltac:(lia)) as E55;
cbn [Nat.add nth] in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55; clear EXE;
let Hc' := fresh "Hc'" in
pose proof Hcfg as Hc'; cbn [obj_at LAY_RawFrameConfig] in Hc';
destruct Hc' as ([_ Rlct] & [_ Rimg] & [_ Rfattr] & [_ Rw] & [_ Rh] & [_ Rtop] & [_ Rleft] & [_ Rdelay] & [_ Rslct] & [_ Rdisp] & [_ Rtidx] & _);
cbn [fst snd N.to_nat Z.of_N] in Rlct, Rimg, Rfattr, Rw, Rh, Rtop, Rleft, Rdelay, Rslct, Rdisp, Rtidx;
change (2 ^ (8 * 8)) with (2 ^ 64) in Rlct, Rimg; change (2 ^ (8 * 4)) with (2 ^ 32) in Rfattr;
change (2 ^ (8 * 2)) with 65536 in Rw, Rh, Rtop, Rleft, Rdelay, Rslct; change (2 ^ (8 * 1)) with 256 in Rdisp, Rtidx;
let Hr' := fresh "Hr'" in
pose proof Hraw as Hr'; cbn [obj_at LAY_Raw LAY_RawConfig app] in Hr';
destruct Hr' as (_ & [_ Rg] & [_ Rgct] & [_ Rrattr] & [_ RWd] & [_ RHd] & [_ Rsgct] & [_ Rloops] & [_ Rrcur] & _);
cbn [fst snd N.to_nat Z.of_N] in Rg, Rgct, Rrattr, RWd, RHd, Rsgct, Rloops, Rrcur;
change (2 ^ (8 * 8)) with (2 ^ 64) in Rg, Rgct; change (2 ^ (8 * 4)) with (2 ^ 32) in Rrattr, Rrcur;
change (2 ^ (8 * 2)) with 65536 in RWd, RHd, Rsgct, Rloops;
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity);
assert (Himg_in : In (img, Nimg) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; left; reflexivity);
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & [Hrh Hrapp] & Hrpres & _);
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img;
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres, Hrh;
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh;
destruct (frames_bounds _ _ LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; right; exact Hfin);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 1) with 128 in *; change (128 / 8) with 16 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 1 fpos) in *; set (FL := flag_addr ly 1 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ LAWS ly3 S3 _ _ _ (1, fpos) (cid, pos) [] fl1 fl2 HAR3 ltac:(rewrite Hfrs3, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC; change (fs_frame_bytes 1) with 128 in HdFC; rewrite !EFA3 in HdFC; fold F in HdFC; box HdFC;
clear fl1 fl2 Efl;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview _ (w_H W3) (ms_mem ms3) a = aview _ (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in let Vgr3 := fresh "Vgr3" in
aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
img_factsA E; img_hull_factsA.
Ltac ra_blocks3 Hraw3 Hing3 :=
let LAWS := rnLAWS in
lazymatch goal with HAR3 : AR _ ?B ?ly3 ?S3 ?W3 ?m3 ?md3, HdFC : context [frame_addr _ ?cid ?pos] |- _ =>
lazymatch type of Hraw3 with In (?raw, _) _ => lazymatch type of Hing3 with In (?g, _) _ =>
lazymatch goal with Hfin3 : In (1, ?fpos) (frames S3), HfinS3 : In (cid, pos) (frames S3), EFA3 : forall c p, frame_addr ly3 c p = _ |- _ =>
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR3 Hraw3) as (_ & _ & _ & _ & Hrpres3 & _);
change (req_size RAW_SIZE) with 48 in Hrpres3;
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR3 Hing3) as (_ & _ & _ & _ & Hgpres3 & _);
change (req_size CGIF_SIZE) with 96 in Hgpres3;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ raw RAW_SIZE 1 fpos HAR3 Hraw3 Hfin3) as HdFR;
unfold zdisjoint in HdFR; cbn [fst snd] in HdFR; change (req_size RAW_SIZE) with 48 in HdFR; change (fs_frame_bytes 1) with 128 in HdFR; rewrite EFA3 in HdFR;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ raw RAW_SIZE cid pos HAR3 Hraw3 HfinS3) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; rewrite EFA3 in HdRC;
pose proof (sep_blocks _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE raw RAW_SIZE HAR3 Hing3 Hraw3 ltac:(unfold CGIF_SIZE, RAW_SIZE; intros X; injection X; lia)) as HdRG;
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE 1 fpos HAR3 Hing3 Hfin3) as HdFG;
unfold zdisjoint in HdFG; cbn [fst snd] in HdFG; change (req_size CGIF_SIZE) with 96 in HdFG; change (fs_frame_bytes 1) with 128 in HdFG; rewrite EFA3 in HdFG;
pose proof (sep_block_frame _ _ LAWS ly3 S3 _ _ _ g CGIF_SIZE cid pos HAR3 Hing3 HfinS3) as HdGC;
unfold zdisjoint in HdGC; cbn [fst snd] in HdGC; change (req_size CGIF_SIZE) with 96 in HdGC; rewrite EFA3 in HdGC;
box HdFR; box HdRC; box HdRG; box HdFG; box HdGC
end end end end.
Ltac pi_park_deads HS N deads :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
let nf := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
lazymatch (eval vm_compute in (Nat.leb nf N)) with
| true => idtac
| false =>
let M := eval vm_compute in (Nat.max nf (N + 40)) in
pose proof (st_ok_pi_havoc_hi M Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS M vals' 0%nat dl;
norm_ss HS
end
| _ => idtac
end.
Ltac ra_join HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
pi_park_deads HS N deads;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem _ Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_pi_havoc_hi N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc _ N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl  end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_pi_facts_incl3 Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 _ Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS  end;
norm_ss HS;
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] | st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg]  end.
Ltac ra_join_val HS N i R En :=
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end | st_ok _ ?Ev _ _ =>
lazymatch Ev with havoc _ _ ?vals =>
lazymatch type of R with _ = ?v =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew Ev n = v);
[ change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; exact R | ] end end  end.
Ltac ra_join_fact HS n af tac :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_fact Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS  end.
Ltac ra_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (ra_post ?B ?cxv) =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : ra_base _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- ra_E _ (havoc _ _ _) => apply ra_E_havoc; [clear; cbn; lia|] end);
unfold ra_E, ra_F, ra_FL; cbn [c_ly c_fpos c_E0 c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx];
split; [assumption|]; split; [eapply ra_vals_of; eassumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0]
| exact HS ] | st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : ra_base _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- ra_E _ (havoc _ _ _) => apply ra_E_havoc; [clear; cbn; lia|] end);
unfold ra_E, ra_F, ra_FL; cbn [c_ly c_fpos c_E0 c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx];
split; [assumption|]; split; [eapply ra_vals_of; eassumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0]
| exact HS ]  end end.
Ltac relowC HS AG E10 E11 E32 E10n E11n E32n :=
relow HS AG E10 E32 E10n E32n; try clear E11n;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end | st_ok _ ?Ev _ _ =>
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end  end.
Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf)  end.
Ltac frame_pres HJx Hfin3 EFA3 F HFp HFSp :=
let LAWS := rnLAWS in
lazymatch type of Hfin3 with In (1, ?fpos) _ =>
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJx) Hfin3) as (_ & _ & HFp & HFSp);
change (fs_frame_bytes 1) with 128 in HFp, HFSp; change (128 / 8) with 16 in HFSp;
rewrite !EFA3 in HFp, HFSp; fold F in HFp, HFSp end.
Ltac upd_aboveW HUP HFr AG :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac idx_of_base_lo rs n lo :=
lazymatch rs with
| YP09.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base_lo tl n lo in constr:(S i)
end.
