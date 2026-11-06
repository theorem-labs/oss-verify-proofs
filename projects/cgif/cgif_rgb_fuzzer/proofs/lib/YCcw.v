(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac enorm := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Ltac oblI RA n base off En Ebx :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff _ _)) _ =>
rewrite (U_atom_off Ex n base off ltac:(enorm; exact En)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 32 SB ltac:(enorm; exact Ebx)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac byte_at HS i n b HB od v Vname Rname :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_region) in
let HRr := fresh "HRr" in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion (Some n) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch eval cbv in (find (fun c => Z.eqb (YQ0b.c_off c) od) cs) with Some (YQ0b.mkChunk _ (CVal 1 ?e)) =>
pose proof (byte_of_region Ex _ n b cs lo hi wlo whi od e HRr HB ltac:(cbn; tauto)) as Vname;
set (v := bv_unsigned (sv_denot Ex e) mod 256) in Vname;
assert (Rname : 0 <= v < 256) by (subst v; apply Z.mod_pos_bound; lia) end end;
clear HRr; rewrite ?Z.add_0_r in Vname end.
Ltac idx_of_baseA rs n :=
lazymatch rs with
| YQ0b.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baseA tl n in constr:(S i)
end.
Ltac field_atD HS i n b HB od w e v dtac Vname :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_region) in
let HRr := fresh "HRr" in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion (Some n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ n b cs lo hi wlo whi od w e v HRr HB ltac:(cbn; tauto) ltac:(dtac) ltac:(cbn; lia) ltac:(cbn; lia)) as Vname end;
clear HRr; rewrite ?Z.add_0_r in Vname end.
Ltac oblsA HJx Hpdc RAst RAdst E10x E11x E36x E32x :=
lazymatch goal with
| |- range_addressable _ (U ?Ex _) (U _ (SOff 10 ?c)) _ =>
rewrite (U_atom_off Ex 10 _ c ltac:(enorm; exact E10x)) by lia;
eapply obl_of_range; [exact RAst | rewrite (U_atom Ex 32 SB ltac:(enorm; exact E32x)) by (unfold SB; lia); reflexivity | lia | lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) _ =>
rewrite (U_atom_off Ex 11 _ c ltac:(enorm; exact E11x)) by lia;
eapply obl_of_range; [exact RAdst | rewrite (U_atom Ex 32 SB ltac:(enorm; exact E32x)) by (unfold SB; lia); reflexivity | lia | lia]
| |- range_addressable _ (U ?Ex _) (U _ (SOff 36 ?c)) _ =>
rewrite (U_atom_off Ex 36 _ c ltac:(enorm; exact E36x)) by lia;
let L := lazymatch goal with L : AR_laws trasegs _ |- _ => L end in
eapply (obl_of_block trasegs _ L); [exact (proj1 HJx) | exact Hpdc | rewrite (U_atom Ex 32 SB ltac:(enorm; exact E32x)) by (unfold SB; lia); reflexivity | lia | lia]
end.
Ltac rregD HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_restrict_reg segs H E ss ms r HS)) end.
Ltac unrun HFr Zs Usp B18 B8 HTS Has UN :=
pose proof (kept_of_frame _ _ _ _ _ Zs HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hi := fresh "Hi" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
intros b wlo whi a Hi Hr; vm_compute in Hi;
repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?Usp, ?B18, ?B8 in Hr;
clear - Hr HTS Has; lia |]); destruct Hi)) as UN.
Ltac field_at HS AG i n b HB od w e v Ee Vname :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_region) in
let HRr := fresh "HRr" in
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion (Some n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ n b cs lo hi wlo whi od w (SOff e 0) v HRr HB ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; enorm; rewrite ?AG by lia; rewrite Ee, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as Vname end;
clear HRr; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vname; rewrite ?Z.add_0_r in Vname end.
Ltac rfj_subregion_tac :=
unfold subregion; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac rfj_submem_to := repeat (first [apply submem_keep; [rfj_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac rfj_incl_lit_tac :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn in Hx; cbn;
repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac rfj_set_regs_rec HS N vals i rl :=
lazymatch rl with
| [] => idtac
| ?r :: ?rl' =>
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hv := fresh "Hv" in
let n := eval vm_compute in (N + i)%nat in
assert (Hv : sv_denot Ev (SOff n 0) = getr (ms_regs msx) r);
[ cbn [sv_denot]; rewrite Z.add_0_r; rewrite Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict]; reflexivity | ];
pose proof (ast_ok_set_reg_fp trasegs Ev ssx msx r (SOff n 0) HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS; rfj_set_regs_rec HS N vals (S i) rl' end
end.
Ltac rfj_join HS target N deads :=
norm_ss HS;
let tg := eval vm_compute in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; rfj_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(rfj_incl_lit_tac) ltac:(rfj_incl_lit_tac) ltac:(rfj_incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval red in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
rfj_set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac rnLAWSrf := lazymatch goal with L : AR_laws trasegs _ |- _ => L end.
Ltac rf_prelude :=
let LAWS := rnLAWSrf in
let cx := fresh "cx" in
intros cx E kk ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HJB HKEPT HRAst HRAdst HINV HS;
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos E0];
pose proof HBASE as HBASE0;
unfold rf_base in HBASE; unfold rf_E in HEE; red in HINV;
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_E0] in HBASE, HEE, HJ3, Hfrs3, HJB, HKEPT, HRAst, HRAdst, HINV;
destruct HBASE as (HJ & Hsub & HPerm & Hpd & Hra & Hra4 & Hgp & Htp & G10 & G11 & G12 & Hal16 & Hwlo & Hwhi & Hown & Hcid & Hfal & Hdst1 & Hdst2 & Hdst8 &
Hst1 & Hst2 & Hst8 & RAst & RAdst & HN & Hcur & Hnb & Wp & Wn & Wc & HXU & Hev & Hlive & EE & EX32 & EX33 & EX34 & EX35 & EX36);
change RGBFC_SIZE with 24 in Hdst2, RAdst;
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _);
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); assert (HTS : TRRFC_STK = 128 + ASTACK) by reflexivity; assert (Has : ASTACK = 16384) by reflexivity;
assert (Hes : ESTACK = 4096) by reflexivity;
assert (Hpdc : In (pdata, nb) (ablocks _ lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpd]);
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpdc) as (Hp16 & Hp4096 & Hpceil & [Hph Hpapp] & Hppres & _ & HnbM);
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp;
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpdc) as Hph_img;
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]; unfold MALLOC_MAX in HnbM;
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown);
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & HFSpres); ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2;
pose proof (fs_frame_bytes_nonneg cid) as HFB;
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img;
assert (HSPB : alloc_ceiling <= spZ regs - TRRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia);
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia);
assert (HDSTB : (4096 <= dst /\ (dst + 24 <= 65536 \/ 6287360 <= dst) /\ (dst + 24 <= 2147446784 \/ 17594333495296 <= dst)) /\ dst + 24 <= alloc_ceiling)
by (try generalize HFhi2_img; clear - Hdst1 Hdst2 HFhi1 HFhi2 C1 C3; unfold off_img; intros; lia);
destruct HEE as (AG & E32 & E33 & E34 & E35 & E36);
assert (E10 : ew E 10 = Z_to_bv 64 st) by (rewrite (AG 10%nat) by lia; rewrite (EE 10%nat 10%bv eq_refl); exact G10);
assert (E11 : ew E 11 = Z_to_bv 64 dst) by (rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl); exact G11);
assert (E12 : ew E 12 = Z_to_bv 64 N) by (rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact G12);
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; rewrite (EE 2%nat 2%bv eq_refl); reflexivity);
pose proof (proj1 HJ3) as HAR3;
assert (HlyF : ly_F lyc = ly_F ly) by (destruct Hly as (_ & _ & _ & _ & _ & -> & _); reflexivity);
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
by (let c := fresh "c" in let p := fresh "p" in let Q := fresh "Q" in intros c p; unfold frame_addr; pose proof (proj1 (proj2 HJ3)) as Q;
destruct Q as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity);
assert (Hfin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact Hfin);
assert (X2 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity);
assert (X10 : ew E0 10 = Z_to_bv 64 st) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10);
assert (X11 : ew E0 11 = Z_to_bv 64 dst) by (rewrite (EE 11%nat 11%bv eq_refl); exact G11);
assert (HSEP : rfc_sep (spZ regs) Bb lyc Sc st dst) by (eapply (rfc_sep_intro _ LAWS); [exact HAR | exact HPerm | exact Hfin | clear - HSTB; lia | exact Hdst1 | exact Hdst2]);
assert (Hsd : rboxed (st + 24 <= dst \/ dst + 24 <= st)) by (unfold rboxed; right; clear - HSTB HDSTB; lia);
assert (B10 : bv_unsigned (ew E 10) = st) by (rewrite E10; apply unsigned_lit_small; clear - HSTB C1; lia);
assert (B11 : bv_unsigned (ew E 11) = dst) by (rewrite E11; apply unsigned_lit_small; clear - HDSTB C1; lia);
pose proof (sep_block_frame trasegs _ LAWS _ _ _ _ _ pdata nb cid pos HAR Hpdc Hfin) as DPF; unfold zdisjoint in DPF; cbn [fst snd] in DPF; rbox DPF.
Ltac rf_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (rf_post ?B ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : rf_base _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- rf_E _ (havoc _ _ _) => apply rf_E_havoc; [clear; cbn; lia|] | |- rf_E _ (ewset _ _ _) => apply rf_E_ewset; [clear; cbn; lia|] end);
unfold rf_E; cbn [x_E0 x_pdata x_nb x_cur]; split; [assumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_E0]
| exact HS ] end end.
Ltac rf_relow HS AG X2 X10 X11 X32 Usp E10 E11 E32 B10 B11 :=
try clear Usp; try clear B10; try clear B11; try clear E10; try clear E11; try clear E32;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of X2 with _ = ?v => assert (Usp : bv_unsigned (ew Ev 2) = v) by (rewrite (AG 2%nat) by lia; exact X2) end;
lazymatch type of X10 with _ = ?v => assert (E10 : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact X10) end;
lazymatch type of X11 with _ = ?v => assert (E11 : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact X11) end;
lazymatch type of X32 with _ = ?v => assert (E32 : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact X32) end;
lazymatch type of X10 with _ = Z_to_bv 64 ?v => assert (B10 : bv_unsigned (ew Ev 10) = v) by (rewrite E10; apply unsigned_lit_small; lia) end;
lazymatch type of X11 with _ = Z_to_bv 64 ?v => assert (B11 : bv_unsigned (ew Ev 11) = v) by (rewrite E11; apply unsigned_lit_small; lia) end end.
Ltac rf_after_run UsX B10X B11X :=
lazymatch goal with
| HFr : frame_of _ _ (mrestrict (w_H ?W3) ?mold) (mrestrict (w_H ?W3) ?mnew) |- _ =>
lazymatch goal with
| HK : rfc_kept _ _ W3 mold ?spz _ _ _ ?st ?dst, HSP : rfc_sep ?spz _ _ _ ?st ?dst,
RAs : range_addressable (aview trasegs (w_H W3) mold) SHADOW_OFF ?st 24,
RAd : range_addressable (aview trasegs (w_H W3) mold) SHADOW_OFF ?dst 24,
HTSx : TRRFC_STK = _, Hasx : ASTACK = _ |- _ =>
let UN := fresh "UN" in let SHK := fresh "SHK" in let K2 := fresh "HKEPT" in let RAs2 := fresh "HRAst" in let RAd2 := fresh "HRAdst" in
unrun HFr (fun a => spz - TRRFC_STK <= a < spz \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24) UsX B10X B11X HTSx Hasx UN;
pose proof (rfc_kept_step _ _ _ _ _ _ _ _ _ _ _ _ HK HSP UN ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact Ha) ltac:(lia)) as K2;
assert (SHK : forall a, 2147450880 <= a < kHighShadowEnd -> aview trasegs (w_H W3) mnew a = aview trasegs (w_H W3) mold a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply UN; [lia | cbn beta; lia]);
pose proof (RA_kept_low _ _ st 24 SHK ltac:(lia) ltac:(lia) RAs) as RAs2;
pose proof (RA_kept_low _ _ dst 24 SHK ltac:(lia) ltac:(lia) RAd) as RAd2;
clear HK RAs RAd UN SHK; rename K2 into HK; rename RAs2 into RAs; rename RAd2 into RAd;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
end end.
Ltac rf_pay HS HJx Hpdx c w Hcb E36x Usx B10x B11x :=
let L := rnLAWSrf in
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
lazymatch type of E36x with _ = Z_to_bv 64 (?pd + ?cu) =>
lazymatch type of Hpdx with In (_, ?nbv) _ =>
let HppresX := fresh "HppresX" in
destruct (al_blocks _ _ L _ _ _ _ _ pd nbv (proj1 HJx) Hpdx) as (_ & _ & _ & _ & HppresX & _);
let B36x := fresh "B36x" in
assert (B36x : bv_unsigned (ew Ev 36) = pd + cu) by (rewrite E36x; apply unsigned_lit_small; lia);
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in let K1 := eval vm_compute in (Datatypes.S K) in
let vals := lazymatch w with
| 2 => constr:([Z_to_bv 64 (abyte (w_H Wx) (ms_mem msx) (pd + cu + c)); Z_to_bv 64 (abyte (w_H Wx) (ms_mem msx) (pd + cu + (c + 1)))])
| 1 => constr:([Z_to_bv 64 (abyte (w_H Wx) (ms_mem msx) (pd + cu + c))]) end in
let chunks := lazymatch w with
| 2 => constr:([YQ0b.mkChunk c (CVal 1 (SOff K 0)); YQ0b.mkChunk (c + 1) (CVal 1 (SOff K1 0))])
| 1 => constr:([YQ0b.mkChunk c (CVal 1 (SOff K 0))]) end in
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trasegs K Ev ssx (restrict (w_H Wx) msx) vals HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
let EK0 := fresh "Eb" in let EK1 := fresh "Eb" in
assert (EK0 : ew (havoc Ev K vals) K = Z_to_bv 64 (abyte (w_H Wx) (ms_mem msx) (pd + cu + c))) by (exact (ew_havoc_new _ K vals 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
lazymatch w with
| 2 => assert (EK1 : ew (havoc Ev K vals) K1 = Z_to_bv 64 (abyte (w_H Wx) (ms_mem msx) (pd + cu + (c + 1)))) by (exact (ew_havoc_new _ K vals 1 (Z_to_bv 64 0) ltac:(cbn; lia)))
| 1 => idtac end;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK0; pose proof (abyte_range (w_H Wx) (ms_mem msx) (pd + cu + c));
rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS end;
lazymatch w with
| 2 => lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trasegs Ev2 ssx2 msx2 K1 (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EK1; pose proof (abyte_range (w_H Wx) (ms_mem msx) (pd + cu + (c + 1)));
rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS end
| 1 => idtac end;
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trasegs Ev2 _ _ (YQ0b.mkRegion (Some 36%nat) c (c + w) 0 0 chunks) HS
ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite (ew_havoc_old Ev K vals 36) by (cbn; lia); rewrite B36x;
split; [lia|]; split; [lia|];
split; [let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; exfalso; clear - Ho; lia |];
repeat (apply Forall_cons; [
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?od (CVal 1 (SOff ?n 0))) =>
apply (chunk_ok_val trasegs Ev2 _ (pd + cu) od 1 (SOff n 0) (abyte (w_H Wx) (ms_mem msx) (pd + cu + od)));
[ cbn [sv_denot]; first [rewrite EK0 | rewrite EK1]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (abyte_range (w_H Wx) (ms_mem msx) (pd + cu + od)); cbn; lia
| cbn; lia
| apply abyte_val; apply (proj1 (HppresX (pd + cu + od) ltac:(lia))) ] end |]);
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?(ew_havoc_old Ev K vals 36), ?(ew_havoc_old Ev K vals 2), ?(ew_havoc_old Ev K vals 10), ?(ew_havoc_old Ev K vals 11) by (cbn; lia);
rewrite ?B36x, ?B11x, ?B10x, ?Usx; unfold A_GOT_shadow, A_shadow_glob; runbox;
repeat split; first [zone_lia | match goal with |- ?g => idtac "PAY-DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end;
clear HppresX
end end end.
