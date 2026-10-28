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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACer ACfm ACf5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awrRT_rec AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 88%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 2, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 75%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 2, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear; cbn; unfold LLVMF_STK, ASTACK; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - 144 <= ?sp1 <= sp0 - 128 |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1; cbn; unfold LLVMF_STK, ASTACK; lia | clear -Hsp1; cbn; lia |] end
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "awrRT: no rule for the head region" ];
awrRT_rec AG fpos F EFA
end.
Ltac awrRT AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
awrRT_rec AG fpos F EFA.
Ltac keptRT HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold LLVMF_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; lia | unfold LLVMF_STK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob ];
keptRT HK HJx AG Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 ErT PrT
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| left; rewrite_frame_addr; change (fs_frame_bytes 2) with 256; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; unfold SB; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; first [lia | PrT] ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
lazymatch goal with Hb : ew _ n = Z_to_bv 64 ?b |- _ =>
let L := rnLAWS in
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true =>
first [ eapply (region_kept_block_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | lia | rqs_goal; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| eapply (region_kept_frame_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | rewrite_frame_addr; lia | rewrite_frame_addr; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ] ] end
| eapply (region_kept_block_ajw2 tfibsegs _ L _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | exact (proj1 HJx) | eassumption | evalE AG | eassumption | lia | rqs_goal; lia | lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| match goal with |- ?g => idtac "KEPTRT-FAIL" g end; fail ] end
end.
Ltac relowRT HS AG E10 E11 E32 E10n E11n E32n :=
try clear E10n; try clear E11n; try clear E32n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end end.
Ltac rt_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (?PP ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : rt_base _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end);
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1];
split; [assumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T]
| exact HS ] end end.
Ltac macc_go Ha :=
lazymatch goal with ML' : ameter_laws ?MTv, HN : RT_NEED1 _ <= ?Tv |- _ =>
let Hnn := fresh "Hnn" in let Hfn := fresh "Hfn" in
pose proof (mo_malloc_nonneg MTv ML' 196605 ltac:(clear; lia)) as Hnn; pose proof (mo_free_nonneg MTv ML') as Hfn;
first [ lazymatch goal with |- context [mo_malloc MTv (3 * ?x)] =>
let Hmo := fresh "Hmo" in pose proof (mo_malloc_mono MTv ML' (3 * x) 196605 ltac:(lia)) as Hmo;
unfold RT_NEED1, ACC_pal, ACC0 in Ha, HN |- *; cbn [c_T] in *; clear - Ha HN Hnn Hfn Hmo end
| unfold RT_NEED1, ACC_pal, ACC0 in Ha, HN |- *; cbn [c_T] in *; clear - Ha HN Hnn Hfn ];
first [ lia | match goal with |- ?g => idtac "MACC-FAIL" g end; fail ] end.
Ltac macc :=
first [ assumption
| lazymatch goal with Ha : ?a0 <= ACC0 |- _ => macc_go Ha | Ha : ?a0 <= ACC_pal _ |- _ => macc_go Ha end
| match goal with |- ?g => idtac "MACC-NOACC" g end; fail ].
Ltac rt_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws tfibsegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k acc ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HMLE HINV HS;
destruct cx as [ly S W regs mem md p n fpos sp1 E0 T];
pose proof HBASE as HBASE0;
unfold rt_base in HBASE; unfold rt_E in HEE; red in HINV; unfold rt_F, rt_FL in HBASE, HEE, HJ3, HINV;
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T] in HBASE, HEE, HJ3, Hfrs3, HMLE, HINV;
destruct HBASE as (HPRE & Hra & Hp & Hn & Hpn & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & EX32 & Usp & HMOK & HNEED);
destruct HEE as (AG & E70 & RF & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : LLVMF_STK = 32768) by reflexivity;
assert (HEV : EV_LIB = 2000) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (Hn26 : 0 <= n < 2 ^ 26) by (clear - Hpn; destruct Hpn as [[-> _] | [Hn' _]]; lia);
assert (E10 : ew E0 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact Hp);
assert (E11 : ew E0 11 = Z_to_bv 64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact Hn);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof EX32 as E32;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p0; unfold flag_addr; pose proof (EFA3 c p0) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as Hfin3_img;
destruct (frames_bounds tfibsegs _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 2) with 256 in *; change (256 / 8) with 32 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia);
let Hsp1r := fresh "Hsp1r" in
destruct (sp1_facts (spZ regs + -128) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia); clear Hsp1r;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms3) a = aview tfibsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in
aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
Lemma zs_chunk1 : forall E H (m : word -> option byte) r b o,
region_ok tfibsegs E (mrestrict H m) r -> base_val E (YP09.r_base r) = b ->
In (YP09.mkChunk o (CVal 1 (SLit 0))) (YP09.r_chunks r) -> 0 <= b + o -> b + o + 1 <= 2 ^ 64 ->
aview tfibsegs H m (b + o) = Some 0.
Proof.
intros E H m r b o Hr Hb Hin Hlo Hhi.
destruct Hr as (H1 & H2 & H3 & H4). rewrite Hb in *.
pose proof (proj1 (Forall_forall _ _) H4 _ Hin 0 ltac:(cbn; lia)) as (bt & Hc & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hc, Hm.
rewrite Z.add_0_r in Hm.
apply (aview_of_val_mem1 tfibsegs H m (b + o) 0).
- intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hm. injection Hc as <-. cbn [sv_denot]. vm_compute. reflexivity.
- lia.
Qed.
Lemma rt_val_mem_zero : forall H (m : word -> option byte) a (w : nat),
(forall i, 0 <= i < Z.of_nat w -> aview tfibsegs H m (a + i) = Some 0) -> val_mem tfibsegs (mrestrict H m) a w 0.
Proof.
intros H m a w Hz j Hj. destruct (aview_byte tfibsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Definition rt_trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (Z.max lo (YP09.r_lo r)) (Z.min hi (YP09.r_hi r)) (Z.max lo (YP09.r_wlo r)) (Z.min hi (YP09.r_whi r))
(List.filter (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) (YP09.r_chunks r)).
Fixpoint rt_trim_base (rs : smem) (n : nat) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some b => if Nat.eqb b n then rt_trim_region r lo hi :: t else r :: rt_trim_base t n lo hi
| None => r :: rt_trim_base t n lo hi end end.
Ltac trim_base HS n lo hi :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (rt_trim_base rs n lo hi) in
let HS3 := fresh "HS3" in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma rt_val_mem_byte1 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> exists v, 0 <= v < 256 /\ val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [b Hb]]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R. change (2 ^ 8) with 256 in R.
split; [lia|]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh. cbn. rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rt_val_mem_byte2 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> apresent H m (a + 1) -> exists v, 0 <= v < 65536 /\ val_mem tfibsegs (mrestrict H m) a 2 v.
Proof.
intros H m a Ha0 Ha1.
destruct (rt_val_mem_byte1 H m a Ha0) as (v0 & R0 & V0). destruct (rt_val_mem_byte1 H m (a + 1) Ha1) as (v1 & R1 & V1).
exists (v0 + 256 * v1). split; [lia|]. intros k Hk.
assert (L0 : YO0f.le_byte v0 1 0 = v0) by (unfold YO0f.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v0 256) by lia; reflexivity).
assert (L1 : YO0f.le_byte v1 1 0 = v1) by (unfold YO0f.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v1 256) by lia; reflexivity).
assert (M0 : YO0f.le_byte (v0 + 256 * v1) 2 0 = v0).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.shiftr_0_r, (Z.mod_small _ 65536) by lia.
replace (256 * v1) with (v1 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (M1 : YO0f.le_byte (v0 + 256 * v1) 2 1 = v1).
{ unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite (Z.mod_small _ 65536) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. replace (v0 + 256 * v1) with (v1 * 256 + v0) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small v0 256) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia. }
destruct k as [|[|k]]; [| |lia].
- specialize (V0 0%nat ltac:(lia)). cbn [Z.of_nat] in *. rewrite V0, L0, M0. reflexivity.
- specialize (V1 0%nat ltac:(lia)). change (Z.of_nat 1) with 1. cbn [Z.of_nat] in V1. rewrite Z.add_0_r in V1. rewrite V1, L1, M1. reflexivity.
Qed.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Ltac obl_pay HJx HEn HEbx Hin Hrq :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEn with _ = Z_to_bv 64 ?p =>
lazymatch type of Hin with In (_, ?sz) _ =>
first [ rewrite (U_atom_off Ex n p c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia | lia]
| rewrite (U_atom Ex n p); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEn | lia] ];
eapply (obl_of_block tfibsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len p sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HEbx | unfold SB; lia]
| lia | rewrite Hrq; lia ] end end end.
Ltac ws_pin HS r e Hr dtac :=
let HS3 := fresh "HS3" in
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv r e HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Hr; cbn [sv_denot]; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
Ltac idx_of_base_off rs n off :=
lazymatch rs with
| YP09.mkRegion (Some n) ?lo ?hi _ _ _ :: ?t =>
lazymatch (eval vm_compute in ((lo <=? off) && (off <? hi))%bool) with true => constr:(0%nat) | false => let i := idx_of_base_off t n off in constr:(S i) end
| _ :: ?t => let i := idx_of_base_off t n off in constr:(S i)
end.
Ltac idx_of_chunk cs off :=
lazymatch cs with
| YP09.mkChunk off _ :: _ => constr:(0%nat)
| _ :: ?t => let i := idx_of_chunk t off in constr:(S i)
end.
Ltac rechunk_at HS n off e' tac :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base_off rs n off in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let cs := eval vm_compute in (YP09.r_chunks r) in
let j := idx_of_chunk cs off in let j := eval vm_compute in j in
rechunk HS i j e' tac end.
Lemma denot_3x : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = Z_to_bv 64 (3 * x).
Proof.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite (U_atom E n x Hn) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma rt_denot_mul3 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * i).
Proof.
intros E n i Hn Hi. rewrite denot_lit_U. f_equal.
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n i Hn) by lia. rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_or_lit0 : forall E n r, ew E n = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 -> U E (SAlu ALU_OR (SLit 0) (SOff n 0)) = r.
Proof. intros E n r Hn Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n r Hn) by lia. change (zcanon 0) with 0. rewrite Z.lor_0_l. apply zcanon_id. unfold M64; lia. Qed.
Lemma U_or_litm1 : forall E e, U E (SAlu ALU_OR (SLit 18446744073709551615) e) = 18446744073709551615.
Proof.
intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 18446744073709551615) with (Z.ones 64).
pose proof (U_range E e) as Hr. unfold M64 in Hr.
rewrite Z.lor_comm. rewrite Z.lor_ones_low; [reflexivity | lia |].
destruct (Z.eq_dec (U E e) 0) as [-> | Hne]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma denot_add2 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_3x_add : forall E n m x c, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 c -> 0 <= x < 65536 -> 0 <= c < 2 ^ 26 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = 3 * x + c.
Proof.
intros E n m x c Hn Hm Hx Hc. rewrite U_SAlu. cbn [zalu_raw].
change (U E (SMd M_MUL (SOff n 0) (SLit 3))) with (bv_unsigned (sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)))).
rewrite (rt_denot_mul3 E n x Hn Hx), unsigned_lit_small by lia. rewrite (U_atom E m c Hm) by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma denot_3x_add : forall E n m x c, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 c -> 0 <= x < 65536 -> 0 <= c < 2 ^ 26 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (3 * x + c).
Proof. intros E n m x c Hn Hm Hx Hc. rewrite denot_lit_U. f_equal. apply (U_3x_add E n m x c Hn Hm Hx Hc). Qed.
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
Lemma unsigned_range_64' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
Lemma le_req_size : forall n, 0 <= n -> n <= req_size n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma req_size_le1 : forall n, 0 <= n -> req_size n <= Z.max n 1.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
Lemma U_mul16 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 65536 -> 0 <= y < 65536 ->
U E (SMd M_MUL (SOff a 0) (SOff b 0)) = x * y.
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E a x Ha) by lia. rewrite (U_atom E b y Hb) by lia.
apply zcanon_id. unfold M64; nia.
Qed.
Lemma denot_mul16 : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 65536 -> 0 <= y < 65536 ->
sv_denot E (SMd M_MUL (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x * y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite denot_lit_U. f_equal. apply (U_mul16 E a b x y Ha Hb Hx Hy). Qed.
Ltac add_fact HS n lo hi Hv tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev ssx msx n (mkAF lo hi 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv, unsigned_lit_small by tac; rewrite Z.pow_0_r, Z.mod_1_r; split; [tac | split; [reflexivity | clear; lia]])) as HS3;
clear HS; rename HS3 into HS end.
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
Ltac vkeep V H2 m2 etac :=
lazymatch type of V with val_mem _ (mrestrict ?Hh ?m) ?a ?n ?v =>
let V2 := fresh "V" in
assert (V2 : val_mem tfibsegs (mrestrict H2 m2) a n v) by (apply (val_mem_kept Hh H2 m m2 a n v V); intros i Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; etac);
clear V; rename V2 into V end.
Ltac vkeepUN UN Vp Vn Vc ztac :=
lazymatch type of UN with forall a, _ -> _ -> aview _ ?H2 ?m2 a = _ =>
vkeep Vp H2 m2 ltac:(apply UN; ztac); vkeep Vn H2 m2 ltac:(apply UN; ztac); vkeep Vc H2 m2 ltac:(apply UN; ztac) end.
Ltac gcfgRA HS E88x RAname :=
let ZS := fresh "ZS" in let HR88 := fresh "HR88" in let Hb88 := fresh "Hb88" in
lazymatch goal with HF8lo : 512 <= ?Fv / 8, HF8hi : ?Fv / 8 < _, HFq : ?Fv = 32 * _, HF8 : ?Fv / 8 = 4 * _ |- _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 88%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HR88; cbn [ms_mem restrict] in HR88;
assert (Hb88 : base_val Ex (Some 88%nat) = SB + Fv / 8)
by (cbn [base_val]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E88x; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall i, 0 <= i < 6 -> aview tfibsegs (w_H Wx) (ms_mem msX) (SB + Fv / 8 + 4 + i) = Some 0);
[ let i := fresh "i" in let Hi := fresh "Hi" in let Hi6 := fresh "Hi6" in
intros i Hi; assert (Hi6 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by (clear - Hi; lia);
destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
[ replace (SB + Fv / 8 + 4 + 0) with (SB + Fv / 8 + 4) by (clear; lia) | replace (SB + Fv / 8 + 4 + 1) with (SB + Fv / 8 + 5) by (clear; lia)
| replace (SB + Fv / 8 + 4 + 2) with (SB + Fv / 8 + 6) by (clear; lia) | replace (SB + Fv / 8 + 4 + 3) with (SB + Fv / 8 + 7) by (clear; lia)
| replace (SB + Fv / 8 + 4 + 4) with (SB + Fv / 8 + 8) by (clear; lia) | replace (SB + Fv / 8 + 4 + 5) with (SB + Fv / 8 + 9) by (clear; lia) ];
(eapply (zs_chunk1 _ _ _ _ _ _ HR88); [exact Hb88 | cbn; tauto | unfold SB; clear - HF8lo; lia | unfold SB; clear - HF8hi; lia])
| assert (RAname : range_addressable (aview tfibsegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (Fv + 32) 48);
[ apply zero_shadow_range; [replace (Fv + 32) with ((Fv / 8 + 4) * 8) by (clear - HFq HF8; lia); apply Z_mod_mult | reflexivity |];
let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace ((Fv + 32) / 8) with (Fv / 8 + 4) by (replace (Fv + 32) with ((Fv / 8 + 4) * 8) by (clear - HFq HF8; lia); rewrite Z.div_mul by (clear; lia); reflexivity);
replace (SB + (Fv / 8 + 4) + i) with (SB + Fv / 8 + 4 + i) by (clear; lia);
apply ZS; change (48 / 8) with 6 in Hi; exact Hi
| clear ZS HR88 Hb88 ] ] end end.
Ltac rebv HS E70 RF B70 B75 :=
try clear B70; try clear B75;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E70 with ew _ 70 = Z_to_bv 64 ?v => assert (B70 : bv_unsigned (ew Ev 70) = v) by (rewrite E70; apply unsigned_lit_small; unfold LLVMF_STK in *; lia) end;
lazymatch type of RF with ew _ 75 = Z_to_bv 64 ?v => assert (B75 : bv_unsigned (ew Ev 75) = v) by (rewrite RF; apply unsigned_lit_small; lia) end end.
Lemma sp1_st8 : forall x, x mod 32 = 0 -> (x + 8) mod 8 = 0.
Proof.
intros x Hx. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
rewrite D. replace (32 * (x / 32) + 8) with (8 + (4 * (x / 32)) * 8) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma land4_mod256 : forall x, 0 <= x -> Z.land (x mod 256) 4 = Z.land x 4.
Proof.
intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
destruct (Z.eq_dec n 2) as [-> | Hne].
- change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4 n) with false; [rewrite !andb_false_r; reflexivity|].
symmetry. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma unsigned_range_64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.
Lemma attr_test : forall E e, Z.land (U E (SExt false 8 e)) 4 = Z.land (bv_unsigned (sv_denot E e)) 4.
Proof. intros E e. rewrite U_zext. change (2 ^ Z.of_N 8) with 256. apply land4_mod256. apply (proj1 (unsigned_range_64 _)). Qed.
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
Lemma alu_or_lits : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
alu64 ALU_OR (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof.
intros x y Hx Hy. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])).
change (alu64 _ _ _) with (sv_denot E0 (SAlu ALU_OR (SLit x) (SLit y))).
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; apply Z_lor_bound; lia). reflexivity.
Qed.
Fixpoint idx_of {A} (f : A -> bool) (l : list A) : nat :=
match l with [] => 0%nat | x :: t => if f x then 0%nat else S (idx_of f t) end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma pal_prov_intro : forall B STK cx own ly4 S4 W4 memS md4 k4 (m5 m' : word -> option byte) pal ngp,
AR_laws tfibsegs B -> AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
ajournal tfibsegs B STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly4 S4 W4 memS md4 k4 ->
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) -> In (c_p cx, c_n cx) (ablocks B ly4 S4) -> req_size (c_n cx) = c_n cx ->
0 <= ngp -> 14 + 3 * ngp <= c_n cx ->
(forall i, 0 <= i < 3 * ngp -> aview tfibsegs (w_H W4) m5 (pal + i) = aview tfibsegs (w_H W4) memS (c_p cx + 14 + i)) ->
(forall i, 0 <= i < 3 * ngp -> aview tfibsegs (w_H W4) m' (pal + i) = aview tfibsegs (w_H W4) m5 (pal + i)) ->
pal_prov cx pal ngp (mrestrict (w_H W4) m').
Proof.
intros B STK cx own ly4 S4 W4 memS md4 k4 m5 m' pal ngp LAWS HAR0 HJ Hin0 Hin4 Hrq Hngp Hle Heff Hfr i Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR0 Hin0) as (_ & _ & _ & _ & Hpres & _). rewrite Hrq in Hpres.
destruct (rt_val_mem_byte1 _ _ (c_p cx + (14 + i)) (proj1 (Hpres (c_p cx + (14 + i)) ltac:(lia)))) as (b & Rb & Vb).
exists b. split; [split; [exact Rb | exact Vb]|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (M2 : forall H H1 (m m1 : word -> option byte) a a1, aview tfibsegs H1 m1 a1 = aview tfibsegs H m a ->
mbyte tfibsegs (mrestrict H1 m1) a1 = mbyte tfibsegs (mrestrict H m) a).
{ intros H H1 m m1 a a1 E; unfold aview in E; destruct (mbyte tfibsegs (mrestrict H1 m1) a1) as [b1|], (mbyte tfibsegs (mrestrict H m) a) as [b0|];
cbn in E; try discriminate; [|reflexivity]; injection E as E; f_equal; apply bv_eq; exact E. }
intros kk Hkk. pose proof (Vb kk Hkk) as V. rewrite <- V. destruct kk as [|kk]; [|cbn in Hkk; lia]. cbn [Z.of_nat]. rewrite !Z.add_0_r.
rewrite (M2 _ _ _ _ _ _ (Hfr i Hi)). rewrite (M2 _ _ _ _ _ _ (Heff i Hi)). replace (c_p cx + 14 + i) with (c_p cx + (14 + i)) by lia.
apply (M2 _ _ _ _ _ _).
apply (F2 (c_p cx) (c_n cx) (14 + i) Hin0 Hin4); [rewrite Hrq; lia | apply inFP_nil].
Qed.
Lemma PB_at_now : forall B STK cx own ly3 S3 W3 mem3 md3 k i,
AR_laws tfibsegs B -> AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
ajournal tfibsegs B STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W3 mem3 md3 k ->
In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)) -> In (c_p cx, c_n cx) (ablocks B ly3 S3) -> req_size (c_n cx) = c_n cx ->
0 <= i < c_n cx ->
exists b, PB cx i b /\ aview tfibsegs (w_H W3) mem3 (c_p cx + i) = Some b.
Proof.
intros B STK cx own ly3 S3 W3 mem3 md3 k i LAWS HAR0 HJ Hin0 Hin3 Hrq Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) HAR0 Hin0) as (_ & _ & _ & _ & Hpres & _). rewrite Hrq in Hpres.
destruct (aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) as [b|] eqn:Ev;
[| exfalso; exact (aview_some_of_apresent tfibsegs _ _ _ (proj1 (Hpres (c_p cx + i) ltac:(lia))) Ev)].
destruct (aview_byte tfibsegs _ _ _ b Ev) as (bb & _ & _ & Hb).
exists b. split.
- split; [exact Hb | apply val_mem1_of_aview; exact Ev].
- pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 (c_p cx) (c_n cx) i Hin0 Hin3); [exact Ev | rewrite Hrq; exact Hi | apply inFP_nil].
Qed.
End d.
Ltac rdkeep RD H2 m2 etac :=
lazymatch type of RD with ?rk = 0 -> forall i, 0 <= i < ?nk -> exists b, PB ?cx (?o + i) b /\ aview _ ?Hh ?m (?a + i) = Some b =>
let RD2 := fresh "RD" in
assert (RD2 : rk = 0 -> forall i, 0 <= i < nk -> exists b, PB cx (o + i) b /\ aview tfibsegs H2 m2 (a + i) = Some b)
by (let Hz := fresh "Hz" in intros Hz i Hi;
let b := fresh "b" in let HP := fresh "HP" in let HA := fresh "HA" in
destruct (RD Hz i Hi) as (b & HP & HA); exists b; split; [exact HP|]; rewrite <- HA; etac);
clear RD; rename RD2 into RD
| ?ty => fail "rdkeep: unexpected shape" ty end.
