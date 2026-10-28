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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACai ACam ACan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma wtac_awr_byte_ly : forall STK sp0 FP bl0 blc ly ly' own a,
(forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof.
intros STK sp0 FP bl0 blc ly ly' own a Efa [H | [H | [H | (cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
right. right. right. exists cid, pos. split; [exact Hin|]. unfold frame_rng in *. cbn [fst snd] in *. rewrite !Efa. exact H.
Qed.
Ltac wcb_siteA rs HS HJ3 HAR3 Hfin3 HfinS3 Hraw3 Hing3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 :=
let AG := lazymatch goal with H : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => H end in
let EE := lazymatch goal with H : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew _ n = getr _ r |- _ => H end in
let Usp := lazymatch goal with H : bv_unsigned (ew _ 2) = spZ _ |- _ => H end in
let E0v := lazymatch type of EE with forall n r, _ -> ew ?E0v n = _ => E0v end in
let E32 := lazymatch goal with H : ew E0v 32 = Z_to_bv 64 _ |- _ => H end in
let E53 := lazymatch goal with H : ew _ 53 = Z_to_bv 64 _ |- _ => H end in
let E54 := lazymatch goal with H : ew _ 54 = Z_to_bv 64 _ |- _ => H end in
let Hch := lazymatch goal with H : achain _ _ _ _ _ |- _ => H end in
let Hal32 := lazymatch goal with H : spZ _ mod 32 = 0 |- _ => H end in
let Hra4 := lazymatch goal with H : 4096 <= raZ _ |- _ => H end in
let Hgp := lazymatch goal with H : getr _ 3 = w64 (as_gp _) |- _ => H end in
let Htp := lazymatch goal with H : getr _ 4 = w64 (as_tp _) |- _ => H end in
let FFS := lazymatch goal with H : TRAWADD_STK = _ |- _ => H end in
let HROD := lazymatch goal with H : arodata_okP _ _ _ _ _ |- _ => H end in
let WFN := lazymatch goal with H : twcb_spec _ _ _ _ |- _ => H end in
let Rwfn := lazymatch type of WFN with twcb_spec _ _ ?wf _ => lazymatch goal with H : 0 <= wf < 2 ^ 64 /\ wf mod 2 = 0 |- _ => H end end in
let HDEEP := lazymatch goal with H : forall c, In c ?T -> (2 <= length c)%nat |- _ => H end in
let Hctx := lazymatch type of HDEEP with forall c, In c ?T -> _ => lazymatch goal with H : In _ T |- _ => H end end in
let LAWS := rnLAWS in let Bv := rnB in
lazymatch type of HJ3 with ajournal _ _ ?STK (spZ ?regs) ?FP ?ly ?S ?W ?mem ?md [(1, ?fpos)] ?ly3 ?S3 ?W3 _ ?md3 ?k =>
lazymatch type of HfinS3 with In (?cid, ?pos) _ =>
lazymatch type of Hing3 with In (?g, CGIF_SIZE) _ =>
lazymatch type of Hraw3 with In (?raw, RAW_SIZE) _ =>
lazymatch type of Hch with achain _ _ _ _ ?ch =>
lazymatch type of WFN with twcb_spec _ _ ?wfn ?hw =>
lazymatch type of HFpres3 with forall a, ?F <= a < _ -> _ =>
let Hfin := lazymatch goal with H : In (cid, pos) (frames S) |- _ => H end in
let P2 := fresh "P2" in let Prs := fresh "Prs" in let P8 := fresh "P8" in let P10 := fresh "P10" in
let P1 := fresh "P1" in let P3 := fresh "P3" in let P4 := fresh "P4" in
let Hchne := fresh "Hchne" in let Qtop := fresh "Qtop" in let Qtop64 := fresh "Qtop64" in let Qceil := fresh "Qceil" in let Qal8 := fresh "Qal8" in
let Qra := fresh "Qra" in let Qs0 := fresh "Qs0" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in let HRr := fresh "HRr" in
let Hch1 := fresh "Hch1" in let Vhw := fresh "Vhw" in let Vctx := fresh "Vctx" in let Vpf := fresh "Vpf" in
let matj := fresh "mat" in let msj := fresh "msj" in let Emsj := fresh "Emsj" in let HS1 := fresh "HSj" in let HS2 := fresh "HS2" in
let W4 := fresh "W" in let c4 := fresh "c" in let Hwle4 := fresh "Hwle" in let ly4 := fresh "ly" in let S4 := fresh "S" in
let regs4 := fresh "regs" in let mem4 := fresh "mem" in let md4 := fresh "md" in
let HJ4 := fresh "HJ4" in let HJc := fresh "HJc" in let HP4 := fresh "HP4" in let Ha04 := fresh "Ha0c" in let HPb4 := fresh "HPb" in
let HRK := fresh "HRK" in let HEv := fresh "HEv" in
prreg HS (2%bv : bv 5) P2; prreg HS rs Prs; prreg HS (8%bv : bv 5) P8;
assert (Hchne : ch <> []) by (let Hn := fresh "Hn" in let Hd := fresh "Hdeep" in intros Hn; pose proof (HDEEP _ Hctx) as Hd; rewrite Hn in Hd; cbn in Hd; clear - Hd; lia);
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Q1 & Q2 & _)]; [exfalso; exact (Hchne Hnil) | lia]);
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia;
assert (Qceil : alloc_ceiling <= spZ regs) by lia;
assert (Qal8 : spZ regs mod 8 = 0) by (let D := fresh "D" in pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult);
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (let Hq := fresh "Hq" in unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (let Hq := fresh "Hq" in unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq);
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i := match rsm with _ => idx_of_base_lo rsm 2%nat (-104) | _ => idx_of_base rsm 2%nat end in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(let Hq := fresh "Hq" in unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(let Hq := fresh "Hq" in unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview pa_segs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
let Etop := fresh "Etop" in
pose proof HJ3 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)
(rdword_of_val_mem _ _ _ _ _ Vra Qra) (rdword_of_val_mem _ _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end;
let i := idx_of_base rsm 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 54 0) hw HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 52 0) (bv_unsigned (ew Ex 52)) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity)
ltac:(let Q := fresh "Q" in pose proof (bv_unsigned_in_range 64 (ew Ex 52)) as Q; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Q; exact Q) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRr ltac:(evalE AG) ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
let HEIx := rnHEI Ex in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W3 Ex ssx _ _ _ wj (1%bv : bv 5) rs wfn HEIx HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite Prs; exact E53 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |];
clear HS; intros matj msj Emsj HS1;
prreg HS1 (1%bv : bv 5) P1; prreg HS1 (3%bv : bv 5) P3; prreg HS1 (4%bv : bv 5) P4; clear P8; prreg HS1 (8%bv : bv 5) P8; prreg HS1 (10%bv : bv 5) P10;
clear P2; prreg HS1 (2%bv : bv 5) P2;
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
eapply SRr_bind;
[ eapply (aj_call _ Bv LAWS pa_segs_low W3 Ex _ msq STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 mdq k
WCB_STK [] 0 (-320) (ew Ex 2) _ ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 0 /\ Permutation (ablocks Bv ly2 S2) (ablocks Bv ly3 S3)) HS1 eq_refl);
[ rewrite Emsj; cbn [ms_mem mkst]; apply (ajournal_materialize _ Bv LAWS pa_segs_low); exact HJ3
| rewrite P2; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; reflexivity
| reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; exact Usp
| reflexivity | lia | unfold WCB_STK; lia | rewrite FFS; unfold WCB_STK; lia
| rewrite P3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite P4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp;
rewrite Emsj; cbn [ms_mem mkst]; replace (spZ regs + -320) with (spZ regs - 320) by lia; exact Hch1
| let HPRE1 := fresh "HPRE1" in let HC := fresh "HC" in
intros HPRE1; eapply SRr_mono;
[ pose proof (WFN W3 ly3 S3 _ _ _ ((spZ regs, raZ regs, s0Z regs) :: ch) g (bv_unsigned (ew Ex 52)) HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC;
[ rewrite P10; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32; reflexivity
| exact Hing3 | | | | let Q := fresh "Q" in pose proof (bv_unsigned_in_range 64 (ew Ex 52)) as Q; change (bv_modulus 64) with (2 ^ 64) in Q; exact Q ];
rewrite Emsj; cbn [ms_mem mkst]; [exact Vhw | exact Vctx | exact Vpf]
| cbv beta; unfold wcb_post;
let W2 := fresh "W2" in let c2 := fresh "c2" in
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK & HPb);
exists ly2, S2, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | split; [exact HK | exact HPb]]]] ]
| let a := fresh "a" in intros a (r0 & Hr0 & _); destruct Hr0 ]
| ] end;
clear P3 P4 P10 Vra Vs0 Vhw Vctx Vpf Hch1 Prs;
cbv beta; intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & Ha04 & HPb4);
let K := run_K_hi HS1 in
lazymatch type of HS1 with st_ok _ _ ?ssy _ =>
let n := eval vm_compute in (length (ss_mem ssy)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 idxs HS2 end;
rewrite Emsj in HS2, HJc; cbn [ms_mem ms_regs restrict mkst] in HS2, HJc;
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3; aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
let HAR4 := fresh "HAR4" in let Hfrs4 := fresh "Hfrs4" in let Hfin4 := fresh "Hfin4" in let HfinS4 := fresh "HfinS4" in
let Hraw4 := fresh "Hraw4" in let Hing4 := fresh "Hing4" in let EFA4 := fresh "EFA4" in let EFL4 := fresh "EFL4" in
let HFpres4 := fresh "HFpres4" in let HFSpres4 := fresh "HFSpres4" in let Hrpres4 := fresh "Hrpres4" in let Hgpres4 := fresh "Hgpres4" in let HUP4 := fresh "HUP4" in
let Kgot4 := fresh "Kgot4" in let Kcell4 := fresh "Kcell4" in let Kguar4 := fresh "Kguar4" in let Kuar4 := fresh "Kuar4" in let Vgr4 := fresh "Vgr4" in
pose proof (proj1 HJ4) as HAR4;
assert (Hfrs4 : frames S4 = (1, fpos) :: frames S) by (let Hfr := fresh "Hfr" in pose proof HJc as (_ & _ & _ & _ & _ & Hfr & _); rewrite Hfr; cbn [app]; exact Hfrs3);
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity);
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; right; exact Hfin);
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks Bv ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hraw3]);
assert (Hing4 : In (g, CGIF_SIZE) (ablocks Bv ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hing3]);
(let HAR := lazymatch goal with H : AR _ Bv ly S W mem md |- _ => H end in destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _));
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros cc pp; unfold flag_addr; pose proof (EFA4 cc pp) as X; unfold frame_addr in X; lia);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4); change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4;
change (128 / 8) with 16 in HFSpres4; rewrite !EFA4 in HFpres4, HFSpres4; fold F in HFpres4, HFSpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR4 Hraw4) as (_ & _ & _ & _ & Hrpres4 & _); change (req_size RAW_SIZE) with 48 in Hrpres4;
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR4 Hing4) as (_ & _ & _ & _ & Hgpres4 & _); change (req_size CGIF_SIZE) with 96 in Hgpres4;
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview pa_segs (w_H W4) mem4 a = aview pa_segs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1;
[clear - Ha Qceil; lia | clear - Ha; lia]);
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4;
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 1 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; apply (fun H => proj1 (HFpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 1 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat lo hi wlo whi _ raw RAW_SIZE HJc);
[ evalE AG | exact Hraw3 | exact Hraw4 | lia | change (req_size RAW_SIZE) with 48; lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; apply (fun H => proj1 (Hrpres4 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub _ Bv); [exact HJc | exact HJ4 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=pa_segs) Bv Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat _ lo hi wlo whi _ cid pos HJc);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | intros aa Haa Hxa; exact (inFP_nil aa Hxa) | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub _ Bv); [exact HJc | evalE AG | exact Hing3 | exact Hing4 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| intros aa Haa Hxa; exact (inFP_nil aa Hxa) ]
| |- _ => keptIA I I AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
end
| ];
specialize (HS2 HRK); clear HRK HS1; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
rebaseE HS AG HEv; clear HEv;
let HS0 := fresh "HS0" in
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS0 end;
clear HS; rename HS0 into HS; norm_ss HS;
try (lazymatch goal with HPerm3 : Permutation (ablocks Bv ly3 S3) ?L |- _ =>
let HPerm4 := fresh "HPerm4" in
assert (HPerm4 : Permutation (ablocks Bv ly4 S4) L) by (eapply Permutation_trans; [exact HPb4 | exact HPerm3]);
clear HPerm3; rename HPerm4 into HPerm3 end);
try (lazymatch goal with Abb : forall blc i, In ?b blc -> 0 <= i < ?Lb -> awr_byte ?STKa ?spa ?FPa ?bl0 blc ly3 ?own (?bb + i) |- _ =>
let Abb4 := fresh "Abb4" in
assert (Abb4 : forall blcx ix, In b blcx -> 0 <= ix < Lb -> awr_byte STKa spa FPa bl0 blcx ly4 own (bb + ix))
by (let Hb := fresh "Hb" in let Hi := fresh "Hi" in
intros blcx ix Hb Hi; apply (wtac_awr_byte_ly _ _ _ _ _ ly3 ly4); [intros cc pp; rewrite EFA4, EFA3; reflexivity | exact (Abb blcx ix Hb Hi)]);
clear Abb; rename Abb4 into Abb end);
clear Hraw3 Hing3;
repeat match goal with Hb : In ?xb (ablocks Bv ly3 S3) |- _ =>
let Hb2 := fresh Hb in
assert (Hb2 : In xb (ablocks Bv ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPb4 | exact Hb]);
clear Hb; rename Hb2 into Hb end;
clear HJ3 HAR3 Hfin3 HfinS3 Hfrs3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3;
clear HJc HP4 HPb4 Ha04 Hwle4 P1 P2 P8 Hchne Qtop Qtop64 Qceil Qal8 Qra Qs0 Emsj; try clear matj;
(repeat match goal with H : context [ly3] |- _ => first [clear H | rewrite EFA3 in H | rewrite EFL3 in H | fail 2 "wcb_siteA: ly3 still used in" H] end);
(repeat match goal with H : context [S3] |- _ => first [clear H | fail 2 "wcb_siteA: S3 still used in" H] end);
(repeat match goal with H : context [W3] |- _ => first [clear H | fail 2 "wcb_siteA: W3 still used in" H] end);
try clear EFA3; try clear EFL3;
rename HJ4 into HJ3; rename HAR4 into HAR3; rename Hfin4 into Hfin3; rename HfinS4 into HfinS3; rename Hing4 into Hing3; rename Hraw4 into Hraw3;
rename Hfrs4 into Hfrs3; rename EFA4 into EFA3; rename EFL4 into EFL3; rename HFpres4 into HFpres3; rename HFSpres4 into HFSpres3;
rename Hrpres4 into Hrpres3; rename Hgpres4 into Hgpres3; rename HUP4 into HUP;
rename Kgot4 into Kgot3; rename Kcell4 into Kcell3; rename Kguar4 into Kguar3; rename Kuar4 into Kuar3; rename Vgr4 into Vgr3;
replace (k + 0) with k in HJ3 by lia;
try clear md3; try clear S3; try clear ly3; try clear W3;
try rename ly4 into ly3; try rename S4 into S3; try rename W4 into W3
end end end end end end end end.
