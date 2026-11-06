(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the position-abstract Section form of lines 28-37 and 73-81, the entry/run/branch/ret chain) and proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (lines 41-140 fc_entry and lines 204-322 pb_freeCGIF, the entry lemma and the paj_run_tok / psrr_branch_tok / paj_ret_at walk) at c8557374ad2e to libreac/fuzz_knock's asan-ubsan image, as the twin of lib/A/APgHeard.v: lib_asan3_0_listing -> knock_asanubsan_listing (lib/Reusable/YI0y.v), PL_asan3_0 -> PL_knock_asanubsan, A_freeCGIFP -> BASE + AF_asanubsan_reac_knock_heard (0x650 = entry 0x7f520 - 0x7eed0), ss_fc -> ss_heard, fc_regions -> heard_regions, fc_facts -> heard_facts, fc_SH -> heard_SH, fc_extra -> heard_extra, fc_entry -> heard_entry, Bx = SOff 34 0 -> KBx = SOff 39 0, Bspan -> KBspan, TfibLib/PALib donor fields A_OBJ 0 (GOT shadow slot) and A_OBJ 12 (shadow-base cell) -> knock's A_OBJ 1 (asan-ubsan GOT slot 0x96618) and A_OBJ 7 (asan-ubsan shadow-base cell 0x9e578) through the re-pointed PALib of lib/Reusable/YC1f.v, CGIF_OBJ = 96 -> the 40-byte knock struct, LAY_CGIF -> LAY_Knock (lib/A/APgCSpec.v), FC_STK = 16400 -> T_heard_STK = 16 (addi sp,sp,-16 at 0x7f520), the own-journal post fc_post -> the caller-journal post kn_post_heard of lib/A/APgCSpec.v (donor A/ACey.v rfc_post), the destination block of the donor -> the 40-byte struct kp inside the caller's frame (cid, pos), written through awr_byte's in_frames case by In (cid, pos) own, its addressability carried by afobj (lib/A/APgBase.v); the donor's free call, its CTX / as_universe premises and its block permutation are dropped, because reac_knock_heard calls nothing; the UndefinedBehaviorSanitizer NULL check (beqz a0 at 0x7f528) and 8-byte alignment check (andi a3,a0,7; bnez a3 at 0x7f530) of kp, both into the trap unimp at 0x7f58c, are decided by the symbolic run from the entry fact on atom 10 (af_lo = 4096, af_al2 = 3), which heard_entry establishes from 4096 <= frame_addr <= kp and kp mod 8 = 0; SB = 0x7fff8000 = SHADOW_OFF is knock's shadow base, measured from the asan-ubsan GOT slot 0x96618 of __asan_shadow_memory_dynamic_address; the file states no image-end and no RELRO address. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0d YP0c YI0w YI0y YC4a.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YC80 YC1f.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma swrap32_big : forall x, 2 ^ 31 <= x < 2 ^ 32 -> bv_swrap 32 x = x - 2 ^ 32.
Proof.
intros x Hx. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
replace (x + 2 ^ 31) with ((x - 2 ^ 31) + 1 * 2 ^ 32) by lia.
rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.
Lemma zcanon_neg : forall x, - 2 ^ 63 <= x < 0 -> zcanon x = x + 2 ^ 64.
Proof.
intros x Hx. unfold zcanon, M64.
rewrite <- (Z_mod_plus_full x 1 (2 ^ 64)).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma U_sx32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = (if v <? 2 ^ 31 then v else v + 2 ^ 64 - 2 ^ 32).
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn ltac:(lia)).
change (Z.of_N 32) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite YI0m.swrap32_small by lia. apply zcanon_id. unfold M64. lia.
- rewrite swrap32_big by lia. rewrite zcanon_neg by lia. lia.
Qed.
Lemma U_sx32_eq0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
(U E (SExt true 32 (SOff n 0)) =? 0) = (v =? 0).
Proof.
intros E n v Hn Hv. rewrite (U_sx32 E n v Hn Hv).
destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
destruct (Z.eqb_spec v 0) as [->|Hne]; [lia|]. apply Z.eqb_neq. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg knock_asanubsan_listing}.
#[local] Notation SEGS := (@pa_segs _ knock_asanubsan_listing PI).
#[local] Notation VAL := (@pa_val _ knock_asanubsan_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ knock_asanubsan_listing PI).
#[local] Notation BASE := (@pa_val _ knock_asanubsan_listing PI A_TEXT).
Definition SBk : Z := 0x7fff8000.
Lemma SBk_SHADOW_OFF : SBk = SHADOW_OFF. Proof. reflexivity. Qed.
Definition KBx : sv := SOff 39 0.
Definition KBspan : Z * Z := (SBk, SBk + 2 ^ 44 - 1).
Definition knock_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 40 0 40 (obj_chunks_from LAY_Knock 32).
Definition heard_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 39; knock_region ].
Definition heard_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 3);
(32%nat, mkAF 0 4294967295 0); (39%nat, mkAF SBk SBk 0) ] [] [].
Definition ss_heard : sstate :=
mkSS AF_asanubsan_reac_knock_heard sr_atoms heard_regions None heard_facts.
Definition heard_SH : list shent := [ mkSHE 10 0 40 ].
Definition heard_extra (st p1 opened due heard g p2 : Z) : list word :=
map (Z_to_bv 64) [st; p1; opened; due; heard; g; p2] ++ map (Z_to_bv 64) [SBk].
Definition EK (regs : bvmap 5 word) (st p1 opened due heard g p2 : Z) : env :=
Eimg (Ereg regs (heard_extra st p1 opened due heard g p2)).
Lemma st_ok_pi_region_nth : forall E ss ms i r,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma field_of_regionK : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.
Lemma kept_outside : forall (E : env) (rs : smem) (H : word -> bool) (m m' : word -> option byte) (sp kp : Z),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall x, in_wrange E rs x -> (sp - 16 <= x < sp) \/ (kp <= x < kp + 40)) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> ~ (kp <= a < kp + 40) ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' sp kp HF HP a Ha H1 H2. apply (aview_eq_of SEGS). apply (HF (Z_to_bv 64 a)).
intros Hw. rewrite unsigned_lit_small in Hw by lia.
destruct (HP a Hw) as [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)].
Qed.
Ltac wrangeK Usp B10 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros ? (r & Hin & Ha);
cbv [ss_heard heard_regions knock_region ss_mem stack_region got_regionP bcell_regionP] in Hin;
repeat (destruct Hin as [<- | Hin]); try (destruct Hin);
cbv [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Ha;
rewrite ?Usp, ?B10 in Ha; lia.
Ltac awr_frame_obj n En Hown :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n);
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by lia; rewrite En; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; right; right; right; eexists; eexists; split;
[exact Hown | left; unfold in_zr; cbn [fst snd]; lia] | ].
Ltac awrK Usp E10 Hown :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| lazymatch goal with
| |- awr_ok ?E (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (bv_unsigned (ew E 2%nat) - sp0));
[ reflexivity | lia
| cbn [YP09.r_wlo ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn [YP09.r_whi ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by lia; rewrite Usp; lia | ]
| |- awr_ok _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ => awr_frame_obj 10%nat E10 Hown
end ].
Ltac ioK := repeat first
[ apply same_io_refl
| eapply same_io_trans; [| apply same_io_materialized; apply same_but_materialized_wvb_any] ].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_knock_asanubsan) (PI := PI).
Lemma frame_vs_area : forall ly S rd lo len p q,
ARm B ly S rd -> In (lo, len) (asyms_areas B) -> 0 < len -> 0 < q ->
(forall a, p <= a < p + q -> ~ aowned B ly S a) ->
p + q <= lo \/ lo + len <= p.
Proof.
intros ly S rd lo len p q M Hin Hlen Hq Hno.
destruct (Z.le_gt_cases (p + q) lo) as [HA | HA]; [left; exact HA|].
destruct (Z.le_gt_cases (lo + len) p) as [HB | HB]; [right; exact HB|]. exfalso.
apply (Hno (Z.max p lo)); [lia|].
eapply own_area; [exact M | exact Hin | cbn [fst snd]; lia].
Qed.
Lemma heard_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
(regs : bvmap 5 word) (kp now : Z) (cid pos : Z) (st p1 opened due heard g p2 : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 kp -> getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T_heard_STK -> spZ regs <= sp0 ->
In (cid, pos) own ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
kp mod 8 = 0 ->
afobj SEGS B lyc Sc W memc kp 40 ->
obj_at SEGS (mrestrict (w_H W) memc) kp LAY_Knock [st; p1; opened; due; heard; g; p2] ->
st_ok_pi SEGS VAL (EK regs st p1 opened due heard g p2) ss_heard
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asanubsan_reac_knock_heard)) memc (seg_rom SEGS)))
/\ sh_ok SEGS KBx heard_SH (EK regs st p1 opened due heard g p2) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp now cid pos st p1 opened due heard g p2
HJ G10 G11 Hnow Hal16 Hwlo Hwhi Hown Hkp1 Hkp2 Hkp8 HFOBJ HOBJ.
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_heard_STK = 16) by reflexivity.
destruct HFOBJ as (_ & _ & RAkp).
pose proof HOBJ as HR. unfold LAY_Knock in HR. cbn [obj_at] in HR. unfold field_ok in HR.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul] in HR.
destruct HR as ((_ & Rst) & (_ & Rp1) & (_ & Rop) & (_ & Rdue) & (_ & Rhe) & (_ & Rg) & (_ & Rp2) & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HARc Hfin) as (Hfal32 & Hfapp & HFpres & HFSpres).
destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HARc Hfin) as (HF4096 & HFceil & HFapp2).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 7 ltac:(lia)) as HcellR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HgotR, HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (am_syms _ _ _ _ (proj1 HARc)) as HSY.
assert (HnoOwn : forall a, kp <= a < kp + 40 -> ~ aowned B lyc Sc a)
by (intros a Ha; exact (proj2 (HFpres a ltac:(lia)))).
pose proof (frame_vs_area lyc Sc _ (as_got_shadow B) 8 kp 40 (proj1 HARc)
ltac:(cbn; tauto) ltac:(lia) ltac:(lia) HnoOwn) as HdGot.
pose proof (frame_vs_area lyc Sc _ (as_shadow_cell B) 8 kp 40 (proj1 HARc)
ltac:(cbn; tauto) ltac:(lia) ltac:(lia) HnoOwn) as HdCell.
rewrite HBgot in HdGot. rewrite HBcell in HdCell.
rewrite restrict_mkst_fx.
set (E := EK regs st p1 opened due heard g p2). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 kp)
by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 now)
by (subst E; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E32 : ew E 32 = Z_to_bv 64 st)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 0 st eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 p1)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 1 p1 eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 opened)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 2 opened eq_refl)).
assert (E35 : ew E 35 = Z_to_bv 64 due)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 3 due eq_refl)).
assert (E36 : ew E 36 = Z_to_bv 64 heard)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 4 heard eq_refl)).
assert (E37 : ew E 37 = Z_to_bv 64 g)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 5 g eq_refl)).
assert (E38 : ew E 38 = Z_to_bv 64 p2)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 6 p2 eq_refl)).
assert (E39 : ew E 39 = Z_to_bv 64 SBk)
by (subst E; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_more regs [st; p1; opened; due; heard; g; p2] [SBk] 0 SBk eq_refl)).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E248 : ew E (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7)))
by (subst E; unfold EK; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
split.
- unfold ss_heard. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold heard_regions, knock_region, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 7) 0) (VAL (A_OBJ 7)));
[cbn [sv_denot]; rewrite E248, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 7)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) E248) by (pose proof (pa_val_range (A_OBJ 7)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 7)) 0 8 KBx SBk);
[cbn [sv_denot KBx]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| unfold SBk; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* apply (region_ok_obj SEGS E _ 10%nat kp 40 0 40 LAY_Knock [st; p1; opened; due; heard; g; p2] 32%nat).
-- rewrite E10. apply unsigned_lit_small. lia.
-- lia.
-- lia.
-- exact HOBJ.
-- reflexivity.
-- intros j v Hj.
do 7 (destruct j as [|j];
[cbn [nth_error] in Hj; injection Hj as <-; cbn [Nat.add];
first [exact E32 | exact E33 | exact E34 | exact E35 | exact E36 | exact E37 | exact E38]|]).
destruct j as [|j]; cbn [nth_error] in Hj; discriminate Hj.
-- intros i Hi. apply (apresent_writable SEGS). exact (proj1 (HFpres (kp + i) ltac:(lia))).
+ apply pairwise_disjoint_of_extents.
unfold heard_regions, knock_region, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat kp E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 7) (VAL (A_OBJ 7)) E248) by (pose proof (pa_val_range (A_OBJ 7)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hstk0 HF4096 HFceil HgotR HcellR HgcD HdGot HdCell C1 C3 HTS Hwlo Hwhi Hkp1 Hkp2.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. clear. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [heard_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E39, !unsigned_lit_small by (unfold SBk; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.

revert Hslo Hshi H47 Hceil Hstk0 HF4096 HFceil C1 C3 HTS Hwlo Hwhi Hkp1 Hkp2 Hkp8 Hal16 Rst.
unfold SBk. clear. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, heard_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E KBx 10%nat kp 40 kp 0 40 RAkp).
+ unfold U, KBx. cbn [sv_denot]. rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SBk; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ cbn [Z.min Z.max]. intros x Hx.
destruct HFapp2 as (HA1 & [HA2 | (HA2 & HA3)]);
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.
Lemma heard_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
(regs regs2 : bvmap 5 word) (kp now : Z) (cid pos : Z) (st p1 opened due heard g p2 : Z)
mem2 md2 (stv : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
AR SEGS B lyc Sc W memc mdc ->
In (cid, pos) (frames Sc) ->
frame_addr lyc cid pos <= kp -> kp + 40 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
alloc_ceiling <= spZ regs - 16 -> spZ regs <= 2 ^ 47 ->
aregs_preserved regs regs2 -> same_io mdc md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
obj_at SEGS (mrestrict (w_H W) mem2) kp LAY_Knock [stv; p1; opened; due; now; g; p2] ->
stv = (if st =? 0 then 2 else st) ->
kn_post_heard SEGS B MT STK sp0 FP ly S W0 mem0 md0 own k regs kp now st p1 opened due heard g p2
lyc Sc W memc mdc W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 kp now cid pos
st p1 opened due heard g p2 mem2 md2 stv HJ HARc Hfin Hkp1 Hkp2 Hsplo Hsphi HP HIO KE HOBJ2 Hstv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [exact HJ | unfold EV_heard; lia]|].
split; [exact HP|]. split; [reflexivity|].
split; [apply Permutation_refl|]. split; [exact HIO|].
split; [exact (mo_le_refl MT MTL Sc)|].
split.
{ intros a Ha H1 H2. apply KE; [lia | exact H1 | exact H2]. }
split.
{ intros b m i Hb Hi.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
pose proof (sep_block_frame _ _ LAWS lyc Sc W memc mdc b m cid pos HARc Hb Hfin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
apply KE; [lia | lia | lia]. }
split.
{ intros c p a Hcp Hz Hk.
destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc c p HARc Hcp) as (HC4096 & HCceil & _).
pose proof (fs_frame_bytes_nonneg c) as HFB.
pose proof (Z.div_mod (frame_addr lyc c p) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (frame_addr lyc c p) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (fs_frame_bytes c) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (fs_frame_bytes c) 8 ltac:(lia)) as D4.
unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF in Hz. cbn [fst snd] in Hz.
apply KE; [lia | lia | exact Hk]. }
split.
{ intros a Hin Ho He.
pose proof (pa_img_range a Hin) as HIR. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HIR.
apply KE; [lia | lia |].
intros Hk.
destruct (al_client_img _ _ LAWS lyc Sc W memc mdc a HARc
ltac:(right; left; exists cid, pos; split; [exact Hfin | lia])) as (_ & Hni).
exact (Hni Hin). }
rewrite <- Hstv. exact HOBJ2.
Qed.
Theorem pb_knock_heardX : tknock_heard_specX SEGS B MT (BASE + AF_asanubsan_reac_knock_heard).
Proof.
unfold tknock_heard_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp now cid pos ch st p1 opened due heard g p2
HJ Hra Hra4 Hgp Htp G10 G11 Hnow Hch Hal16 Hwlo Hwhi Hown Hcid Hfal Hkp1 Hkp2 Hkp8 Hkp0 Hksep HFOBJ HOBJ Hev.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : T_heard_STK = 16) by reflexivity.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HARc Hfin) as (HF4096 & HFceil & HFapp2).
assert (Hsplo : alloc_ceiling <= spZ regs - 16) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
pose proof HOBJ as HR. unfold LAY_Knock in HR. cbn [obj_at] in HR. unfold field_ok in HR.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul] in HR.
destruct HR as ((_ & Rst) & (_ & Rp1) & (_ & Rop) & (_ & Rdue) & (_ & Rhe) & (_ & Rg) & (_ & Rp2) & _).
destruct (heard_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kp now cid pos
st p1 opened due heard g p2 HJ G10 G11 Hnow Hal16 Hwlo Hwhi Hown Hkp1 Hkp2 Hkp8 HFOBJ HOBJ) as [HS SHOK].
remember (EK regs st p1 opened due heard g p2) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold EK; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1)
by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 kp)
by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 now)
by (rewrite HE; unfold EK; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E32 : ew E 32 = Z_to_bv 64 st)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 0 st eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 p1)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 1 p1 eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 opened)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 2 opened eq_refl)).
assert (E35 : ew E 35 = Z_to_bv 64 due)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 3 due eq_refl)).
assert (E37 : ew E 37 = Z_to_bv 64 g)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 5 g eq_refl)).
assert (E38 : ew E 38 = Z_to_bv 64 p2)
by (rewrite HE; unfold EK, heard_extra; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (Ereg_vals regs [st; p1; opened; due; heard; g; p2] _ 6 p2 eq_refl)).
assert (HAE : env_agree 32 (Ereg regs (heard_extra st p1 opened due heard g p2)) E)
by (rewrite HE; unfold EK; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (B10 : bv_unsigned (ew E 10) = kp) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_asanubsan_reac_knock_heard)) with (Z_to_bv 64 (BASE + AF_asanubsan_reac_knock_heard)).
paj_run_tok RUN HS HJ SHOK KBspan. { awrK Usp E10 Hown. }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m1) =>
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) m1 a = aview SEGS (w_H W) memc a)
by (apply (kept_outside E _ (w_H W) memc m1 (spZ regs) kp HFr); wrangeK Usp B10) end.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK KBspan.
-
rewrite branch_ne_U, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
rewrite (U_sx32_eq0 E 32 st E32 ltac:(lia)) in Hc.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
paj_run_tok RUN HS HJ SHOK KBspan. { awrK Usp E10 Hown. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mB a = aview SEGS (w_H W) memc a)
by (intros a Ha H1 H2;
rewrite (kept_outside E _ (w_H W) mA mB (spZ regs) kp HFr ltac:(wrangeK Usp B10) a Ha H1 H2);
apply KE1; assumption) end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) R1.
pose proof (st_ok_pi_region_nth E _ _ 3%nat _ HS eq_refl) as HRk.
cbn [ms_mem restrict] in HRk.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs (heard_extra st p1 opened due heard g p2) HS HAE
ltac:(vm_compute; reflexivity)) as HPR.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem]. rewrite R1, E1, Hra.
eapply (heard_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ kp now cid pos
st p1 opened due heard g p2 _ _ st);
[ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
| exact HARc | exact Hfin | exact Hkp1 | exact Hkp2 | exact Hsplo | exact Hsphi
| exact HPR | ioK | intros a Ha H1 H2; apply KE2; assumption
| | rewrite (proj2 (Z.eqb_neq st 0) Hc); reflexivity ].
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 0 4 (SOff 32 0) st HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 4 4 (SOff 33 0) p1 HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V1.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 8 8 (SOff 34 0) opened HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V2.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 16 8 (SOff 35 0) due HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V3.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 24 8 (SOff 11 0) now HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V4.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 32 4 (SOff 37 0) g HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V5.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 36 4 (SOff 38 0) p2 HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V6.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V1, V2, V3, V4, V5, V6.
unfold LAY_Knock. cbn [obj_at]. unfold field_ok.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul].
repeat apply conj; first [exact V0 | exact V1 | exact V2 | exact V3 | exact V4 | exact V5 | exact V6 | lia | exact I].
-
rewrite branch_ne_U, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
rewrite (U_sx32_eq0 E 32 st E32 ltac:(lia)) in Hc.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
paj_run_tok RUN HS HJ SHOK KBspan. { awrK Usp E10 Hown. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ (kp <= a < kp + 40) ->
aview SEGS (w_H W) mB a = aview SEGS (w_H W) memc a)
by (intros a Ha H1 H2;
rewrite (kept_outside E _ (w_H W) mA mB (spZ regs) kp HFr ltac:(wrangeK Usp B10) a Ha H1 H2);
apply KE1; assumption) end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) R1.
pose proof (st_ok_pi_region_nth E _ _ 3%nat _ HS eq_refl) as HRk.
cbn [ms_mem restrict] in HRk.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs (heard_extra st p1 opened due heard g p2) HS HAE
ltac:(vm_compute; reflexivity)) as HPR.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem]. rewrite R1, E1, Hra.
eapply (heard_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ kp now cid pos
st p1 opened due heard g p2 _ _ 2);
[ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
| exact HARc | exact Hfin | exact Hkp1 | exact Hkp2 | exact Hsplo | exact Hsphi
| exact HPR | ioK | intros a Ha H1 H2; apply KE2; assumption
| | rewrite (proj2 (Z.eqb_eq st 0) Hc); reflexivity ].
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 0 4 (SLit 2) 2 HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 4 4 (SOff 33 0) p1 HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V1.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 8 8 (SOff 34 0) opened HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V2.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 16 8 (SOff 35 0) due HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V3.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 24 8 (SOff 11 0) now HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V4.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 32 4 (SOff 37 0) g HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V5.
pose proof (field_of_regionK E _ 10%nat kp _ _ _ _ _ 36 4 (SOff 38 0) p2 HRk B10
ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as V6.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0, V1, V2, V3, V4, V5, V6.
unfold LAY_Knock. cbn [obj_at]. unfold field_ok.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N Z.mul].
repeat apply conj; first [exact V0 | exact V1 | exact V2 | exact V3 | exact V4 | exact V5 | exact V6 | lia | exact I].
Qed.
End h.
End f.
End d.
