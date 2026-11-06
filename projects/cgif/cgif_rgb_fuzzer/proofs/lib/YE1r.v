(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8v YE1o YE1p YE07 YE1n YE09 YE1s YE06 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma region_ok_transport_chunks {imgk : img} : forall E E' mem mem' r,
region_ok tfxsegs E mem r ->
base_val E' (YQ0b.r_base r) = base_val E (YQ0b.r_base r) ->
(forall c, In c (YQ0b.r_chunks r) -> match YQ0b.c_val c with CVal _ e => sv_denot E' e = sv_denot E e | CData _ _ _ => False | _ => True end) ->
(forall c a, In c (YQ0b.r_chunks r) ->
base_val E (YQ0b.r_base r) + YQ0b.c_off c <= a < base_val E (YQ0b.r_base r) + YQ0b.c_off c + c_len c ->
mbyte tfxsegs mem' a = mbyte tfxsegs mem a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
writable_at tfxsegs mem a -> writable_at tfxsegs mem' a) ->
region_ok tfxsegs E' mem' r.
Proof.
intros E E' mem mem' r HR Hb Hcv Hrd Hwr. unfold region_ok in HR. cbv zeta in HR.
destruct HR as (Hlo & Hhi & Hw & Hcs).
unfold region_ok. cbv zeta. rewrite Hb. split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
- intros o Ho. img_apply Hwr; [img_lia|]. img_apply Hw. img_exact Ho.
- img_apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split.
+ specialize (Hcv c Hc). destruct (YQ0b.c_val c) as [w e|len|len|d s len]; cbn [cbyte] in *;
[img_try (rewrite Hcv; img_exact Hb1) | img_try (img_exact Hb1) | img_try (img_exact Hb1) | img_try (destruct Hcv)].
+ rewrite (Hrd c); [img_try (img_exact Hb2) | img_try (img_exact Hc) | img_lia].
Qed.

Definition A_vfprintf {imgk : img} : Z := (0x97ccc + D_10ec).
Definition VF_STK : Z := 912 + 2 * ESTACK.
Definition vf_regions {imgk : img} (apv : sv) : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YQ0b.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ) fw_file_chunks;
YQ0b.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YQ0b.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YQ0b.mkRegion None A_canary (A_canary + 8) 0 0 [YQ0b.mkChunk A_canary (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 12%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 apv)];
img_ro_region ].
Definition vf_sr {imgk : img} (fmt : Z) : list sv := sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit F_STDERR)) (11%bv : bv 5) (SLit fmt).
Definition vf_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3); (32%nat, mkAF 1 (2 ^ 47) 0) ] [] [].
Definition ss_vf {imgk : img} (fmt : Z) (apv : sv) : sstate := mkSS A_vfprintf (vf_sr fmt) (vf_regions apv) None vf_facts.
Lemma vf_entry {imgk : img} : forall (W : world tfxsegs) regs mem fmt apv ap argw cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 fmt -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfxsegs (mrestrict (w_H W) mem) ap 8 argw -> 1 <= argw < 2 ^ 47 ->
stderr_pristine (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
sv_denot (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) apv = Z_to_bv 64 argw ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) (ss_vf fmt apv)
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem fmt apv ap argw cval Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg Hargw HF Hgot Hcan Hcv Hro Hapv.
rewrite restrict_mkst_fx. unfold ss_vf.
set (E := Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E12 : bv_unsigned (ew E 12) = ap) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; img_apply unsigned_lit_small; img_lia)).
assert (E32 : ew E 32 = Z_to_bv 64 argw) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (HVF : VF_STK = 9104) by img_refl.
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) with E.
- unfold vf_sr. img_apply regs_ok_pin; [img_try (img_apply regs_ok_pin; [img_apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; img_refl])
| img_try (intros Hx; discriminate Hx) | img_try (rewrite H11; img_refl)].
- unfold vf_regions, img_ro_region, fw_file_chunks. cbn. destruct apv; img_refl.
- unfold vf_regions. repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold F_STDERR, FILE_SZ. split; [img_lia|]. split; [img_lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
img_apply (store_ok_all tfxsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDERR));
[img_try (rewrite unsigned_lit_small by (unfold F_STDERR; img_lia); unfold F_STDERR; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDERR in *; img_lia); unfold F_STDERR in *; cbn; img_lia)].
* unfold fw_file_chunks, stderr_fields. cbn [map].
unfold stderr_pristine, file_is, stderr_fields in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold STDERR_BUF; img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; unfold F_STDERR, STDERR_BUF in *; assumption)]).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_GOT_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold A_canary; img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact Hgot.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [| img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E12. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ ap 0 8 _ argw); [img_try (img_exact Hapv) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_r; img_exact Harg)].
+ img_apply Hro.
- img_apply pairwise_disjoint_of_extents. unfold vf_regions, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2, E12.
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [vf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12, E32, unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try img_lia.
Qed.
Fixpoint lit_chunks (o : Z) (zs : list Z) : list YQ0b.chunk :=
match zs with
| [] => []
| b :: zs' => YQ0b.mkChunk o (CVal 1 (SLit b)) :: lit_chunks (o + 1) zs'
end.
Lemma lit_chunks_In : forall zs o c, In c (lit_chunks o zs) ->
exists j, (j < length zs)%nat /\ c = YQ0b.mkChunk (o + Z.of_nat j) (CVal 1 (SLit (nth j zs 0))).
Proof.
induction zs as [|b zs IH]; intros o c Hc; cbn in Hc; [img_try (destruct Hc)|].
destruct Hc as [<- | Hc].
- exists 0%nat. split; [img_try (cbn; img_lia)|]. rewrite Z.add_0_r. img_refl.
- destruct (IH _ _ Hc) as (j & Hj & ->). exists (S j). split; [img_try (cbn; img_lia)|]. cbn [nth]. f_equal. img_lia.
Qed.
Definition vf_after_icpt (k : nat) (ss : sstate) (ra osp o : Z) (zs : list Z) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS ra (sr_sets (ss_regs ss) (junk_upd k CLOB))
(YQ0b.mkRegion (YQ0b.r_base r0) (YQ0b.r_lo r0) (YQ0b.r_hi r0) (YQ0b.r_wlo r0) (YQ0b.r_whi r0)
(lit_chunks o zs ++
List.filter (fun c => (osp <=? YQ0b.c_off c) && chunk_out o (o + Z.of_nat (length zs)) c) (YQ0b.r_chunks r0))
:: rest)
None (ss_facts ss)
| [] => ss
end.
Lemma Z_to_bv8_mod64 : forall z, Z_to_bv 8 (z mod 2 ^ 64) = Z_to_bv 8 z.
Proof.
intros z. img_apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 8) with (2 ^ 8).
symmetry. img_apply Znumtheory.Zmod_div_mod; [img_lia | img_lia | img_try (exists (2 ^ 56); img_refl)].
Qed.
Lemma unsigned_lit8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 8) with 256. img_apply Z.mod_small. img_exact Hz.
Qed.
Section l. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfxsegs B OCpy (pc_wrap_memcpy (as_code B)).
Let HBcode := ts_code B TL.
Lemma vf_stack_shadow : forall (W : world tfxsegs) ly S mem md sp0 a n,
AR tfxsegs B ly S W mem md ->
ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
sp0 - VF_STK + ESTACK <= a -> a + n <= sp0 -> 0 <= n ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF a n /\
(0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) a n).
Proof.
intros W ly S mem md sp0 a n HAR Hstk Htop Ha Han Hn.
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(img_try (left; img_refl))) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz.
split.
- intros y Hy. exists 0. split; [|img_try (left; img_refl)].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (img_try (unfold shadow_of_addr; img_lia)).
img_apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Ha Han Hn HVF HES. img_lia.
- intros Hn0 s Hs.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by img_lia.
rewrite Hz; [img_try (discriminate)|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn0 Lplo Lphi Hstk Htop Ltop Ha Han Hn HVF HES. unfold SHADOW_OFF in *. img_lia.
Qed.
Lemma vf_stack_amem : forall (W : world tfxsegs) ly S mem md sp0 a n,
AR tfxsegs B ly S W mem md ->
ly_stk_lo ly + VF_STK <= sp0 -> sp0 < kHighMemEnd ->
sp0 - VF_STK <= a -> a + n <= sp0 -> amem_range a n.
Proof.
intros W ly S mem md sp0 a n HAR Hstk HtopS Ha Han.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
right. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
Qed.
Lemma vf_icpt_memcpy : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp o (xsv : sv) (x : Z) n zs,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = SOff 2 o -> sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x -> sr_get (ss_regs ss) 12 = SLit (Z.of_nat n) ->
lit_buf tfxsegs (ss_mem ss) xsv n = Some zs ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= o -> o + Z.of_nat n <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + Z.of_nat n <= 2 ^ 47 -> (x + Z.of_nat n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(sp0 + o + Z.of_nat n <= x \/ x + Z.of_nat n <= sp0 + o) -> amem_range x (Z.of_nat n) ->
(forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (Z.of_nat n) ->
(0 < Z.of_nat n -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) x (Z.of_nat n)) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp o zs) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + o <= a < sp0 + o + Z.of_nat n) ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp o xsv x n zs HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 S11 Hxa S12 Hlit Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hon Hra Hra4 Hx0 Hxhi Hxs Hxd Hamx Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres Hra_x Hhull_x.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + o)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 10 HS), S10. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R11 : getr regsT 11 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 11 HS), S11; img_exact Hxa)).
assert (R12 : getr regsT 12 = w64 (Z.of_nat n)) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 12 HS), S12; img_refl)).
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (lit_buf_sound tfxsegs E (mrestrict (w_H W) memT) (ss_mem ss) xsv n zs HmemT Hlit) as Hsrc. rewrite Hxa in Hsrc.
pose proof (lit_buf_length tfxsegs _ _ _ _ Hlit) as Hzl.
apply (proj1 (rdn_mbytes tfxsegs (mrestrict (w_H W) memT) n x _)) in Hsrc as [_ Hsrc].
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(img_try (left; img_refl))) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md (sp0 + o) x (Z.of_nat n)).
-
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)].
- img_exact R10. - img_exact R11. - img_exact R12.
- img_lia. - img_lia. - img_lia.
-   intros a Ha. rewrite HspT. split; [img_try (img_apply apresent_writable; img_apply Hpres; img_lia)|]. split; [| img_lia].
img_exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(img_lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
-
intros y Hy. exists 0. split; [|img_try (left; img_refl)].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (img_try (unfold shadow_of_addr; img_lia)).
img_apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. img_lia.
-   intros Hn s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by img_lia.
rewrite Hz; [img_try (discriminate)|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. unfold SHADOW_OFF in *. img_lia.
-   split; [img_lia|]. split; [img_lia|]. split.
+ intros a Ha. rewrite HspT. split; [|img_lia].
specialize (Hsrc (Z.to_nat (a - x)) ltac:(img_lia)). rewrite Z2Nat.id in Hsrc by img_lia. replace (x + (a - x)) with a in Hsrc by img_lia.
unfold aview. rewrite Hsrc. rewrite nth_error_map.
destruct (nth_error zs (Z.to_nat (a - x))) eqn:En; [img_try (cbn; discriminate)|]. exfalso. apply nth_error_None in En. img_lia.
+ split; [img_lia|]. split; [img_try (img_exact Hamx)|]. split; [img_try (img_exact Hra_x) | img_try (img_exact Hhull_x)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split]])].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+
split; [img_try (img_exact Hwf2)|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2. img_apply Hpres. img_lia. }
img_apply Forall_app. split.
++ img_apply Forall_forall. intros c Hc. destruct (lit_chunks_In _ _ _ Hc) as (j & Hj & ->).
intros i Hi. cbn [YQ0b.c_off YQ0b.c_val c_len cv_len] in Hi |- *.
assert (Hi0 : i = 0) by img_lia. (subst i; cbv beta). rewrite Z.add_0_r.
specialize (Hsrc j ltac:(img_lia)). rewrite nth_error_map, (nth_error_nth' zs 0) in Hsrc by img_lia.
cbn [option_map] in Hsrc.
specialize (Heff (Z.of_nat j) ltac:(img_lia)). unfold aview in Heff. rewrite Hsrc in Heff. cbn [option_map] in Heff.
destruct (mbyte tfxsegs (mrestrict (w_H W) mem2) (sp0 + o + Z.of_nat j)) as [c|] eqn:Hc2; [|img_try (discriminate)].
cbn [option_map] in Heff. injection Heff as Heff.
exists c. split; [| img_try (rewrite <- Hc2; f_equal; img_lia)]. cbn [cbyte sv_denot]. unfold YQ0b.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv8_mod64.
f_equal. img_apply bv_eq. symmetry. img_exact Heff.
++ img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; [img_lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; img_lia.
** img_lia.
--
img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. img_apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; img_lia.
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- intros a Hr Hs Hd. img_apply Hfr; img_lia.
- img_exact Hpres2.
Qed.
Definition vf_after_icpt_n (k : nat) (ss : sstate) (ra osp whi ghi : Z) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS ra (sr_sets (ss_regs ss) (junk_upd k CLOB))
(YQ0b.mkRegion (YQ0b.r_base r0) (YQ0b.r_lo r0) (YQ0b.r_hi r0) (YQ0b.r_wlo r0) whi
(List.filter (fun c => (osp <=? YQ0b.c_off c) && chunk_out whi ghi c) (YQ0b.r_chunks r0))
:: rest)
None (ss_facts ss)
| [] => ss
end.
Lemma vf_icpt_memcpy_sym : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp whi ghi
(dsv xsv nsv : sv) (d x n : Z),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> whi <= YQ0b.r_whi r0 <= 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = Z_to_bv 64 (sp0 + d) ->
sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = Z_to_bv 64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
no_cdata (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= whi -> whi <= d -> d + n <= ghi -> ghi <= 0 -> 0 <= n ->
4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + n <= 2 ^ 47 -> (x + n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(sp0 + d + n <= x \/ x + n <= sp0 + d) -> amem_range x n ->
(forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, x <= a < x + n -> aview tfxsegs (w_H W) (ms_mem ms) a <> None) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) x n) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt_n k ss ra osp whi ghi) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) (ms_mem ms2) (sp0 + d + i) = aview tfxsegs (w_H W) (ms_mem ms) (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + d <= a < sp0 + d + n) ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp whi ghi dsv xsv nsv d x n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hda S11 Hxa S12 Hna Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hwd Hdn Hghi Hn Hra Hra4 Hx0 Hxhi Hxs Hxd Hamx Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres Hsrc Hra_x Hhull_x.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + d)) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 10 HS), S10; img_exact Hda)).
assert (R11 : getr regsT 11 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 11 HS), S11; img_exact Hxa)).
assert (R12 : getr regsT 12 = w64 n) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 12 HS), S12; img_exact Hna)).
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(img_try (left; img_refl))) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md (sp0 + d) x n).
-
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)].
- img_exact R10. - img_exact R11. - img_exact R12.
- img_lia. - img_lia. - img_lia.
-   intros a Ha. rewrite HspT. split; [img_try (img_apply apresent_writable; img_apply Hpres; img_lia)|]. split; [| img_lia].
img_exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(img_lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
-
intros y Hy. exists 0. split; [|img_try (left; img_refl)].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (img_try (unfold shadow_of_addr; img_lia)).
img_apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hwd Hdn Hghi Hn HVF HES. img_lia.
-   intros Hn0 s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by img_lia.
rewrite Hz; [img_try (discriminate)|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn0 Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hwd Hdn Hghi Hn HVF HES. unfold SHADOW_OFF in *. img_lia.
-   split; [img_lia|]. split; [img_lia|]. split.
+ intros a Ha. rewrite HspT. split; [img_try (img_apply Hsrc; img_exact Ha) | img_lia].
+ split; [img_lia|]. split; [img_try (img_exact Hamx)|]. split; [img_try (img_exact Hra_x) | img_try (img_exact Hhull_x)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0; cbv beta).
unfold vf_after_icpt_n in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split; [|split]]])].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+
split; [img_try (img_exact Hwf2)|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2. img_apply Hpres. img_lia. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; [img_lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; img_lia.
** img_lia.
--
img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. img_apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; img_lia.
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- img_exact Heff.
- intros a Hr Hs Hd. img_apply Hfr; img_lia.
- img_exact Hpres2.
Qed.
Lemma vf_icpt_memcpy_ext : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp
(dsv xsv nsv : sv) (d x n : Z),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = Z_to_bv 64 d ->
sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = Z_to_bv 64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 0 <= d -> (d + n <= sp0 - VF_STK \/ sp0 <= d) -> d + n <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + n <= 2 ^ 47 -> (x + n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(d + n <= x \/ x + n <= d) -> amem_range d n -> amem_range x n ->
(forall r, In r rest -> d + n <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r \/ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d) ->
(forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, x <= a < x + n -> aview tfxsegs (w_H W) (ms_mem ms) a <> None) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) x n) ->
(forall a, d <= a < d + n -> writable_at tfxsegs (mrestrict (w_H W) (ms_mem ms)) a /\ ~ aowned B ly S a) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) d n) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfxsegs (w_H W) (ms_mem ms2) (d + i) = aview tfxsegs (w_H W) (ms_mem ms) (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (d <= a < d + n) ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp dsv xsv nsv d x n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hda S11 Hxa S12 Hna Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hd0 Hdband Hdhi Hn Hra Hra4 Hx0 Hxhi Hxs Hxd Hamd Hamx Hrdisj Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres Hsrc Hra_x Hhull_x Hdw Hra_d Hhull_d.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (R10 : getr regsT 10 = w64 d) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 10 HS), S10; img_exact Hda)).
assert (R11 : getr regsT 11 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 11 HS), S11; img_exact Hxa)).
assert (R12 : getr regsT 12 = w64 n) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 12 HS), S12; img_exact Hna)).
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(img_try (left; img_refl))) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md d x n).
-
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)].
- img_exact R10. - img_exact R11. - img_exact R12.
- img_lia. - img_lia. - img_lia.
-   intros a Ha. rewrite HspT. destruct (Hdw a Ha) as [Hw1 Hw2]. split; [img_try (img_exact Hw1)|]. split; [img_try (img_exact Hw2) | img_lia].
- img_exact Hamd.
- img_exact Hra_d.
- img_exact Hhull_d.
-   split; [img_lia|]. split; [img_lia|]. split.
+ intros a Ha. rewrite HspT. split; [img_try (img_apply Hsrc; img_exact Ha) | img_lia].
+ split; [img_lia|]. split; [img_try (img_exact Hamx)|]. split; [img_try (img_exact Hra_x) | img_try (img_exact Hhull_x)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split; [|split]]])].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+
split; [img_try (img_exact Hwf2)|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2. img_apply Hpres. img_lia. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; img_lia.
--
img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. pose proof (Hrdisj r Hr) as Hdj. img_apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha, Hdj; cbn [base_val] in Ha, Hdj; img_lia.
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- img_exact Heff.
- intros a Hr Hs Hd. img_apply Hfr; img_lia.
- img_exact Hpres2.
Qed.
End l.
Section p. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis ASTRNLEN : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Lemma vf_icpt_strnlen : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp (xsv : sv) (x n L : Z),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_strnlen (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = xsv -> sv_denot E xsv = Z_to_bv 64 x -> sr_get (ss_regs ss) 11 = SLit n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> 2 * ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= n < 2 ^ 63 -> 0 < x -> 0 <= L -> L + 8 <= n -> L + 1 < 2 ^ 32 -> x + L + 1 <= 2 ^ 47 ->
(x + L + 1 <= sp0 + osp - 2 * ESTACK \/ sp0 + osp <= x) ->
(forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
first_byte tfxsegs W (ms_mem ms) x n 0 L ->
(forall a, x <= a < x + (L + 1) -> aview tfxsegs (w_H W) (ms_mem ms) a <> None) ->
amem_range x (L + 1) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) x (L + 1) ->
(forall a, x + L < a < x + L - (x + L) mod 8 + 8 -> aview tfxsegs (w_H W) (ms_mem ms) a <> None) ->
mconsts_view W (ms_mem ms) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
getr (ms_regs ms2) 10 = w64 L /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - 2 * ESTACK <= a < sp0 + osp) ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp xsv x n L HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hxa S11 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hn Hx0 HL HL8 HL32 Hxhi Hxs Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres Hfb Hsrc Hamx Hra_x Hhull_x Htail Hrom.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (R10 : getr regsT 10 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 10 HS), S10; img_exact Hxa)).
assert (R11 : getr regsT 11 = w64 n) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 11 HS), S11; img_refl)).
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof ASTRNLEN as AM. unfold astrnlen_realizesM, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md x n L).
- split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)].
-   rewrite HspT. img_lia.
- intros a Ha. rewrite HspT in Ha. img_apply Hpres. img_lia.
- img_exact R10. - img_exact R11.
- img_lia. - img_lia. - img_lia. - img_exact HL8. - img_exact HL32. - img_lia.
- img_exact Hfb.
- intros a Ha. rewrite HspT. split; [img_try (img_apply Hsrc; img_exact Ha) | img_lia].
- intros a Ha. rewrite HspT. img_lia.
- img_exact Hamx.
- img_exact Hra_x.
- img_exact Hhull_x.
- img_exact Htail.
- img_exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split; [img_exact Ha0 | split]]])].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_strnlen (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+ split; [img_try (img_exact Hwf2)|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2. img_apply Hpres. img_lia. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; img_lia.
-- img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. img_apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; img_lia.
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- intros a Hr Hs. img_apply Hfr; img_lia.
- img_exact Hpres2.
Qed.
End p.
Section u. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis AMEMSET : aintrin_realizes tfxsegs B OSet (pc_wrap_memset (as_code B)).
Lemma vf_icpt_memset : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp o (c : Z) n,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memset (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = SOff 2 o -> sr_get (ss_regs ss) 11 = SLit c -> 0 <= c < 256 -> sr_get (ss_regs ss) 12 = SLit (Z.of_nat n) ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= o -> o + Z.of_nat n <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp o (repeat c n)) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + o <= a < sp0 + o + Z.of_nat n) ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp o c n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 S11 Hc S12 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hon Hra Hra4 Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + o)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 10 HS), S10. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R11 : getr regsT 11 = w64 c) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 11 HS), S11; img_refl)).
assert (R12 : getr regsT 12 = w64 (Z.of_nat n)) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 12 HS), S12; img_refl)).
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
assert (Hzl : length (repeat c n) = n) by img_apply repeat_length.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(img_try (left; img_refl))) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMSET as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md (sp0 + o) c (Z.of_nat n)).
-
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)].
- img_exact R10. - img_exact R11. - img_exact R12.
- img_lia. - img_lia. - img_lia.
-   intros a Ha. rewrite HspT. split; [img_try (img_apply apresent_writable; img_apply Hpres; img_lia)|]. split; [| img_lia].
img_exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(img_lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
-
intros y Hy. exists 0. split; [|img_try (left; img_refl)].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (img_try (unfold shadow_of_addr; img_lia)).
img_apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. img_lia.
-   intros Hn s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by img_lia.
rewrite Hz; [img_try (discriminate)|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. unfold SHADOW_OFF in *. img_lia.
-   img_exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split]])].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memset (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+
split; [img_try (img_exact Hwf2)|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2. img_apply Hpres. img_lia. }
img_apply Forall_app. split.
++ img_apply Forall_forall. intros ch Hch. destruct (lit_chunks_In _ _ _ Hch) as (j & Hj & ->).
intros i Hi. cbn [YQ0b.c_off YQ0b.c_val c_len cv_len] in Hi |- *.
assert (Hi0 : i = 0) by img_lia. (subst i; cbv beta). rewrite Z.add_0_r.
specialize (Heff (Z.of_nat j) ltac:(img_lia)). unfold aview in Heff. rewrite Z.mod_small in Heff by img_lia.
destruct (mbyte tfxsegs (mrestrict (w_H W) mem2) (sp0 + o + Z.of_nat j)) as [cb|] eqn:Hc2; [|img_try (discriminate)].
cbn [option_map] in Heff. injection Heff as Heff.
exists cb. split; [| img_try (rewrite <- Hc2; f_equal; img_lia)]. cbn [cbyte sv_denot]. unfold YQ0b.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite nth_repeat_lt by img_lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv8_mod64.
f_equal. img_apply bv_eq. rewrite unsigned_lit8_small by img_lia. symmetry. img_exact Heff.
++ img_apply Forall_forall. intros ch Hch. apply filter_In in Hch as [Hch Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs ch Hch) as Hck.
pose proof (chunk_inside_facts _ ch (proj1 (forallb_forall _ _) Hci0 ch Hch)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; [img_lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; img_lia.
** img_lia.
--
img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros ch Hch. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr ch Hch) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val ch); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. img_apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; img_lia.
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- intros a Hr Hs Hd. img_apply Hfr; img_lia.
- img_exact Hpres2.
Qed.
End u.
Definition xret_realizes (segs : list Segment) (B : asyms) (pc : Z) (xw : Z -> Prop)
(xpre : world segs -> (word -> option byte) -> Prop) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md -> xpre W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ aowned B ly S a -> ~ xw a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ xw a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Section a0. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis HB : TfxSyms B.
Variable pcx : Z.
Variable XW : Z -> Prop.
Variable XPRE : world tfxsegs -> (word -> option byte) -> Prop.
Hypothesis XH : xret_realizes tfxsegs B pcx XW XPRE.
Lemma vf_icpt_xcall : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pcx -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> exists bz, base_val E (YQ0b.r_base r) = bz /\ 0 <= bz + YQ0b.r_lo r /\ bz + YQ0b.r_hi r <= 2 ^ 43) ->
(forall r a, In r rest -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
(is_canary_region r = true \/ ~ aowned B ly S a) /\ ~ XW a) ->
(forall a, XW a -> ~ (sp0 - VF_STK <= a < sp0)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
XPRE W (ms_mem ms) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ aowned B ly S a -> ~ XW a ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW a -> apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hrest HrestX HXWb HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres HXP.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof XH as AM. unfold xret_realizes, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md); [|img_try (img_exact HXP)].
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [|split; [img_exact HP | split]])].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 pcx) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+ split; [img_try (img_exact Hwf2)|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2; [img_lia | img_try (intros Hx; img_apply (HXWb _ Hx); img_lia) | img_try (img_apply Hpres; img_lia)]. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; [img_lia | img_lia | | img_try (intros Hx; img_apply (HXWb _ Hx); img_lia)].
img_apply (al_stack _ _ LAWS ly S W (ms_mem ms) md _ HAR). img_lia.
-- img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. destruct (HrestX r a Hr Ha) as [[Hcan|Ho] Hx].
{
destruct (is_canary_region_sound r Hcan) as (Hcb & Hclo & Hchi & _). rewrite Hcb in Ha. cbn [base_val] in Ha.
replace a with (A_GOT_CANARY + (a - A_GOT_CANARY)) by img_lia. rewrite Hsbm' in HAR2.
img_apply (canary_got_kept B HB _ _ _ _ _ _ _ _ _ _ _ HAR HAR2). img_lia. }
img_apply mbyte_of_aview.
destruct (Hrest r Hr) as (bz & Hbz & Hrl & Hrh). rewrite Hbz in Ha. img_apply Hfr; [img_lia | img_lia | img_try (img_exact Ho) | img_try (img_exact Hx)].
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- rewrite <- Hsbm'. img_exact HAR2.
- intros a Hr Hs Ho Hx. img_apply Hfr; assumption.
- img_exact Hpres2.
Qed.
End a0.
Definition xret_realizes_noar (segs : list Segment) (B : asyms) (pc : Z) (xw : Z -> Prop)
(xpre : world segs -> (word -> option byte) -> Prop) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md -> xpre W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ xw a ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ xw a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Section c0. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Variable pcx : Z.
Variable XW : Z -> Prop.
Variable XPRE : world tfxsegs -> (word -> option byte) -> Prop.
Hypothesis XH : xret_realizes_noar tfxsegs B pcx XW XPRE.
Lemma vf_icpt_xcall_noar : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pcx -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - VF_STK -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - VF_STK -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> exists bz, base_val E (YQ0b.r_base r) = bz /\ 0 <= bz + YQ0b.r_lo r /\ bz + YQ0b.r_hi r <= 2 ^ 43) ->
(forall r a, In r rest -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
(is_canary_region r = true \/ ~ aowned B ly S a) /\ ~ XW a) ->
(forall a, XW a -> ~ (sp0 - VF_STK <= a < sp0)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
XPRE W (ms_mem ms) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ aowned B ly S a -> ~ XW a ->
aview tfxsegs (w_H W) (ms_mem ms2) a = aview tfxsegs (w_H W) (ms_mem ms) a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW a -> apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hrest HrestX HXWb HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres HXP.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. img_refl. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_exact E4. }
assert (HspT : spZ regsT = sp0 + osp).
{ img_change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. img_apply unsigned_lit_small. img_lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof XH as AM. unfold xret_realizes_noar, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ img_apply (AM ly S W regsT (ms_mem ms) md); [|img_try (img_exact HXP)].
split; [img_try (img_exact HAR)|]. split; [img_try (rewrite R1; img_apply YK0s.ret_ok_even; rewrite unsigned_lit_small by img_lia; img_lia) |].
rewrite HspT. split; [img_try (rewrite Z.add_mod, Hsp16, Hal by img_lia; img_refl)|].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros a Ha; img_apply Hpres; img_lia)|]. split; [img_try (img_exact R3) | img_try (img_exact R4)]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HP & Hsbm & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (img_try (unfold raZ, w64; rewrite R1, unsigned_lit_small by img_lia; img_refl)).
split; [img_refl|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfxsegs)), (m_vm_materialized md2).
split; [img_try (rewrite <- Hsbm', Hraz; img_refl)|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [img_exact HP | split])].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs2 (Z_to_bv 64 pcx) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). img_apply HP. img_exact Hcs.
+ constructor.
+ split; [img_try (img_exact Hwf2)|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply apresent_writable. img_apply Hpres2; [img_lia | img_try (intros Hx; img_apply (HXWb _ Hx); img_lia) | img_try (img_apply Hpres; img_lia)]. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. img_apply Hfr; [img_lia | img_lia | img_try (intros Hx; img_apply (HXWb _ Hx); img_lia)].
-- img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. destruct (HrestX r a Hr Ha) as [_ Hx].
destruct (Hrest r Hr) as (bz & Hbz & Hrl & Hrh). rewrite Hbz in Ha. img_apply Hfr; [img_lia | img_lia | img_try (img_exact Hx)].
++ intros a Ha _. img_apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- intros a Hr Hs Ho Hx. img_apply Hfr; assumption.
- img_exact Hpres2.
Qed.
End c0.
Definition RA_FX {imgk : img} : Z := (0x979d0 + D_10ec).
Definition OSP_FX : Z := -976.
Definition RA_SN {imgk : img} : Z := (0x98494 + D_10ec).
Definition OSP_SN : Z := -912.
Definition vf_str {imgk : img} (W : world tfxsegs) (mem : word -> option byte) (s : Z) (str : list byte) : Prop :=
(forall i, (i < length str)%nat -> aview tfxsegs (w_H W) mem (s + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))) /\
aview tfxsegs (w_H W) mem (s + Z.of_nat (length str)) = Some 0 /\
Forall (fun b : byte => bv_unsigned b <> 0) str.
Lemma vf_str_xfer {imgk : img} : forall (W : world tfxsegs) mem mem' s str,
vf_str W mem s str ->
(forall a, s <= a < s + Z.of_nat (length str) + 1 -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
vf_str W mem' s str.
Proof.
intros W mem mem' s str (H1 & H2 & H3) HF. split; [|img_try (split; [|img_exact H3])].
- intros i Hi. rewrite HF by img_lia. img_apply H1. img_exact Hi.
- rewrite HF by img_lia. img_exact H2.
Qed.
Lemma vf_str_first_byte {imgk : img} : forall (W : world tfxsegs) mem s str n,
vf_str W mem s str -> Z.of_nat (length str) + 1 <= n ->
first_byte tfxsegs W mem s n 0 (Z.of_nat (length str)).
Proof.
intros W mem s str n (H1 & H2 & H3) Hn. split; [img_lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) str 0%bv)). split.
+ replace i with (Z.of_nat (Z.to_nat i)) at 1 by img_lia. img_apply H1. img_lia.
+ rewrite Forall_nth in H3. img_apply (H3 (Z.to_nat i) 0%bv). img_lia.
- intros _. img_exact H2.
Qed.
Lemma vf_str_readable {imgk : img} : forall (W : world tfxsegs) mem s str,
vf_str W mem s str ->
forall a, s <= a < s + Z.of_nat (length str) + 1 -> aview tfxsegs (w_H W) mem a <> None.
Proof.
intros W mem s str (H1 & H2 & H3) a Ha.
destruct (Z.eq_dec a (s + Z.of_nat (length str))) as [->|Hne]; [img_try (rewrite H2; discriminate)|].
replace a with (s + Z.of_nat (Z.to_nat (a - s))) by img_lia. rewrite H1 by img_lia. discriminate.
Qed.
Lemma vf_str_rdn {imgk : img} : forall (W : world tfxsegs) mem s str,
vf_str W mem s str -> rdn tfxsegs (mrestrict (w_H W) mem) (Z_to_bv 64 s) (length str) = Some str.
Proof.
intros W mem s str (H1 & H2 & H3). img_apply (proj2 (rdn_mbytes tfxsegs _ (length str) s str)). split; [img_refl|].
intros i Hi. specialize (H1 i Hi). unfold aview in H1.
destruct (mbyte tfxsegs (mrestrict (w_H W) mem) (s + Z.of_nat i)) as [b|] eqn:Hb; [|img_try (discriminate)].
cbn in H1. injection H1 as H1. symmetry. rewrite (nth_error_nth' str 0%bv Hi). f_equal. img_apply bv_eq. symmetry. img_exact H1.
Qed.
Lemma aview_mbyte {imgk : img} : forall (H : word -> bool) (m : word -> option byte) z v,
aview tfxsegs H m z = Some v -> exists b, mbyte tfxsegs (mrestrict H m) z = Some b /\ bv_unsigned b = v.
Proof.
intros H m z v Hv. unfold aview in Hv. destruct (mbyte tfxsegs (mrestrict H m) z) as [b|]; [|img_try (discriminate)].
cbn in Hv. injection Hv as Hv. exists b. split; [img_refl | img_try (img_exact Hv)].
Qed.
Lemma Forall_nth_range : forall (zs : list Z) i, Forall (fun z => 0 <= z < 256) zs -> (i < length zs)%nat -> 0 <= nth i zs 0 < 256.
Proof. intros zs i Hf Hi. rewrite Forall_nth in Hf. img_apply Hf. img_exact Hi. Qed.
Lemma lit_buf_aview {imgk : img} : forall (W : world tfxsegs) E (m : word -> option byte) rs xsv x n zs,
mem_ok tfxsegs E (mrestrict (w_H W) m) rs -> lit_buf tfxsegs rs xsv n = Some zs -> sv_denot E xsv = Z_to_bv 64 x ->
Forall (fun z => 0 <= z < 256) zs ->
forall i, (i < n)%nat -> aview tfxsegs (w_H W) m (x + Z.of_nat i) = Some (nth i zs 0).
Proof.
intros W E m rs xsv x n zs Hmem Hlit Hx Hzs i Hi.
pose proof (lit_buf_sound tfxsegs E _ rs xsv n zs Hmem Hlit) as Hrd. rewrite Hx in Hrd.
pose proof (lit_buf_length tfxsegs _ _ _ _ Hlit) as Hlen.
apply (proj1 (rdn_mbytes tfxsegs _ n x _)) in Hrd as [_ Hrd].
unfold aview. rewrite (Hrd i Hi), nth_error_map, (nth_error_nth' zs 0) by img_lia. cbn [option_map]. f_equal.
img_apply unsigned_lit8_small. img_exact (Forall_nth_range zs i Hzs ltac:(img_lia)).
Qed.
Lemma rdn_cat3 {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a (l1 : list Z) (str : list byte) (l2 : list Z),
Forall (fun z => 0 <= z < 256) l1 -> Forall (fun z => 0 <= z < 256) l2 ->
(forall i, (i < length l1)%nat -> aview tfxsegs H m (a + Z.of_nat i) = Some (nth i l1 0)) ->
(forall i, (i < length str)%nat -> aview tfxsegs H m (a + Z.of_nat (length l1) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))) ->
(forall i, (i < length l2)%nat ->
aview tfxsegs H m (a + Z.of_nat (length l1) + Z.of_nat (length str) + Z.of_nat i) = Some (nth i l2 0)) ->
rdn tfxsegs (mrestrict H m) (Z_to_bv 64 a) (length l1 + length str + length l2)
= Some (map (Z_to_bv 8) l1 ++ str ++ map (Z_to_bv 8) l2).
Proof.
intros H m a l1 str l2 Hl1 Hl2 A1 A2 A3.
img_apply (proj2 (rdn_mbytes tfxsegs _ _ a _)). split; [img_try (rewrite !length_app, !length_map; img_lia)|].
intros i Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [C1|C1].
{ destruct (aview_mbyte H m _ _ (A1 i C1)) as (b & Hb & Hbv). rewrite Hb.
rewrite nth_error_app1 by (img_try (rewrite length_map; img_exact C1)). rewrite nth_error_map, (nth_error_nth' l1 0) by img_exact C1.
cbn [option_map]. f_equal. img_apply bv_eq. rewrite Hbv, unsigned_lit8_small; [img_refl|]. img_exact (Forall_nth_range l1 i Hl1 C1). }
rewrite nth_error_app2 by (img_try (rewrite length_map; img_exact C1)). rewrite length_map.
destruct (Nat.lt_ge_cases (i - length l1) (length str)) as [C2|C2].
{ destruct (aview_mbyte H m _ _ (A2 (i - length l1)%nat C2)) as (b & Hb & Hbv).
replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by img_lia. rewrite Hb.
rewrite nth_error_app1 by img_exact C2. rewrite (nth_error_nth' str 0%bv) by img_exact C2. f_equal. img_apply bv_eq. img_exact Hbv. }
rewrite nth_error_app2 by img_exact C2.
destruct (aview_mbyte H m _ _ (A3 (i - length l1 - length str)%nat ltac:(img_lia))) as (b & Hb & Hbv).
replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (length str) + Z.of_nat (i - length l1 - length str)) by img_lia.
rewrite Hb. replace (i - length l1 - length str)%nat with (i - length l1 - length str)%nat by img_lia.
rewrite nth_error_map, (nth_error_nth' l2 0) by img_lia. cbn [option_map]. f_equal. img_apply bv_eq.
rewrite Hbv, unsigned_lit8_small; [img_refl|]. img_exact (Forall_nth_range l2 (i - length l1 - length str) Hl2 ltac:(img_lia)).
Qed.
Definition vf_band (sp0 a : Z) : Prop := sp0 - VF_STK <= a < sp0.
Definition vf_file {imgk : img} (a : Z) : Prop := F_STDERR <= a < F_STDERR + FILE_SZ.
Definition vf_tail {imgk : img} (W : world tfxsegs) (mem : word -> option byte) (s L : Z) : Prop :=
forall a, s + L < a < s + L - (s + L) mod 8 + 8 -> aview tfxsegs (w_H W) mem a <> None.
Lemma vf_tail_xfer {imgk : img} : forall (W : world tfxsegs) mem mem' sp0 s L,
vf_tail W mem s L ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
sp0 mod 16 = 0 -> 0 < s -> 0 <= L -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= sp0 - VF_STK \/ sp0 <= s) -> (s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) ->
vf_tail W mem' s L.
Proof.
intros W mem mem' sp0 s L Ht Hfr Hal Hs HL Hhi Hband Hfile a Ha. pose proof (Ht a Ha) as Hv.
pose proof (Z.mod_pos_bound (s + L) 8 ltac:(img_lia)) as Hm. pose proof (Z.div_mod (s + L) 8 ltac:(img_lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(img_lia)) as Hsp. rewrite Hal, Z.add_0_r in Hsp.
set (q := (s + L) / 8) in *. set (m := (s + L) mod 8) in *. set (p2 := sp0 / 16) in *.
clearbody q m p2.
unfold vf_band, vf_file, VF_STK, ESTACK, F_STDERR, FILE_SZ in *.
rewrite Hfr; [img_try (img_exact Hv) | img_lia | img_try (intros Hb; img_lia) | img_try (intros Hf; img_lia)].
Qed.
Lemma tfx_rom_low {imgk : img} : forall a, in_rom tfxsegs a -> 0 <= a < (0xa1000 + D_1000).
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfxsegs)).
{ img_exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfxsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. remember (seg_writable sg) as wr eqn:Ew. clear Eb Ez Ew.
img_destruct imgk. all: vm_compute in H.
all: destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-; try discriminate; img_lia.
Qed.

Lemma mconsts_view_xfer {imgk : img} : forall (W : world tfxsegs) mem mem' sp0,
mconsts_view W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
2 ^ 44 <= sp0 -> mconsts_view W mem'.
Proof.
intros W mem mem' sp0 Hr Hfr Hsp a Ha. pose proof mc_bounds as [MB1 MB2].
rewrite Hfr; [img_try (img_exact (Hr a Ha)) | img_lia | img_try (unfold vf_band, VF_STK, ESTACK; img_lia) | img_try (unfold vf_file, F_STDERR, FILE_SZ; img_lia)].
Qed.
Lemma stderr_img_bytes_ok {imgk : img} : zallb (img_byte_ok tfxsegs) F_STDERR (Z.to_nat FILE_SZ) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Section VI. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Hypothesis HFown : forall a, vf_file a -> ~ aowned B ly S a.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VI (mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfxsegs (w_H W) mem a = aview tfxsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VI_init : AR tfxsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VI mem0 md0.
Proof.
intros HAR Hp. split; [img_try (img_exact HAR)|]. split; [img_try (img_apply same_but_materialized_refl)|]. split; [img_try (img_exact Hp)|].
split; [img_try (intros; img_refl) | img_try (intros a _ _ Ha; img_exact Ha)].
Qed.
Lemma VI_run : forall mem md memB mat,
VI mem md ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ vf_file (bv_unsigned x) -> memB x = mem x) ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ vf_file (bv_unsigned x) -> mrestrict (w_H W) memB x = mrestrict (w_H W) mem x) ->
(forall a, vf_band sp0 a -> apresent (w_H W) memB a) ->
VI memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat (HAR & Hsbm & Hpb & Hfr & Hpm) HF HFr HpbB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HVF : VF_STK = 9104) by img_refl.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a).
{ intros a Hr H1 H2. img_apply aview_eq_of. img_apply HFr; rewrite unsigned_lit_small by img_lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|img_try (split; [|split; [img_exact HpbB | split]])].
- img_apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. img_apply AVB; [img_try (img_exact Hr) | |].
* intros Hb. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold vf_band in Hb; img_lia)) Hown).
* intros Hf. img_exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ vf_file a \/ (~ vf_band sp0 a /\ ~ vf_file a)) by (img_try (unfold vf_band, vf_file; img_lia)).
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* img_apply aview_some_of_apresent. img_apply HpbB. img_exact Hin.
*
unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [img_try (cbn; discriminate)|].
unfold vf_file in Hin.
pose proof (zallb_sound _ _ _ a stderr_img_bytes_ok ltac:(img_try (unfold FILE_SZ in *; img_lia))) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfxsegs (Z_to_bv 64 a)); [img_try (cbn; discriminate) | img_try (discriminate Hb)].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF. + img_apply MF. + img_apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (Hf' : ~ vf_file a) by (img_try (unfold in_band_rw, vf_file, F_STDERR, FILE_SZ, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)).
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin|Hout]; [img_try (exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh)|].
rewrite HF; [img_refl | |]; rewrite unsigned_lit_small by (img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)); assumption.
- eapply same_but_materialized_trans; [img_try (img_exact Hsbm) | img_try (img_apply with_vm_backing_same)].
- intros a Hr H1 H2. rewrite AVB by assumption. img_apply Hfr; assumption.
- intros a Hr Hf Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin | Hout]; [img_try (img_apply HpbB; img_exact Hin)|].
destruct (Hpm a Hr Hf Hp) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite HF; [img_try (img_exact Hb)| |]; rewrite unsigned_lit_small by img_lia; assumption.
Qed.
Lemma VI_splice : forall mem md memB mdB (Sx : Z -> Prop),
VI mem md ->
AR tfxsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VI memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
split; [img_try (img_exact HARB)|]. split; [img_try (eapply same_but_materialized_trans; [img_exact Hsbm | img_exact HsbmB])|].
split; [img_try (intros a Ha; img_apply HpmB; img_apply Hpb; img_exact Ha)|]. split.
- intros a Hr H1 H2. rewrite HfrB; [img_try (img_apply Hfr; assumption) | img_try (img_exact Hr) | img_try (intros Hs; img_exact (H1 (HSx a Hs)))].
- intros a Hr Hf Hp. img_apply HpmB. img_apply Hpm; assumption.
Qed.
End VI.
Lemma vf_shadow_xfer {imgk : img} : forall B ly S (W : world tfxsegs) sp0 mem0 md0 mem md x0 m x n,
VI B ly S W sp0 mem0 md0 mem md -> ly_stk_lo ly + VF_STK <= sp0 ->
range_addressable (aview tfxsegs (w_H W) mem0) SHADOW_OFF x0 m -> shadow_hull_vis (aview tfxsegs (w_H W) mem0) x0 m ->
0 <= x0 -> x0 <= x -> x + n <= x0 + m -> x0 + m <= kHighMemEnd ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n).
Proof.
intros B ly S W sp0 mem0 md0 mem md x0 m x n (HAR & _ & _ & Hfr & _) Hstk Hra Hh Hx0 Hx1 Hx2 Hx3.
assert (HVF : VF_STK = 9104) by img_refl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (SH : forall y, 0 <= y < kHighMemEnd -> forall s, shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8 ->
aview tfxsegs (w_H W) mem s = aview tfxsegs (w_H W) mem0 s).
{ intros y Hy s Hs. pose proof (shadow_addr_bounds y Hy) as [B1 B2].
img_apply Hfr; unfold vf_band, vf_file, F_STDERR, FILE_SZ; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; img_lia. }
split.
- intros y Hy. destruct (Hra y ltac:(img_lia)) as (v & Hv & Hok). exists v. split; [|img_try (img_exact Hok)].
rewrite (SH y ltac:(img_lia)); [img_try (img_exact Hv)|]. img_change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). img_lia.
- intros Hn s Hs.
assert (Hy : exists y, x <= y < x + n /\ shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8).
{ unfold shadow_addr in *.
destruct (Z_lt_le_dec s ((x + n - 1) / 8 + SHADOW_OFF)) as [Hlt|Hge].
+ exists (x + Z.max 0 ((s - SHADOW_OFF) * 8 - x)). split; [img_lia|]. img_lia.
+ exists (x + n - 1). img_lia. }
destruct Hy as (y & Hy1 & Hy2). rewrite (SH y ltac:(img_lia) s Hy2). img_apply Hh. unfold shadow_addr in *. img_lia.
Qed.
Definition vf_rest {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ((tl (vf_regions (SLit 0)))))).
Lemma In_skel : forall (rest : smem) r, In r rest -> In (skel r) (skeleton rest).
Proof. intros rest r Hr. unfold skeleton. img_apply in_map. img_exact Hr. Qed.
Lemma vf_rest_ok {imgk : img} : forall E sp0 ap (rest : smem),
skeleton rest = skeleton vf_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> ap + 8 <= 2 ^ 47 ->
forall r, In r rest -> (YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43) \/
(YQ0b.r_base r = Some 12%nat /\ 0 <= YQ0b.r_lo r /\ bv_unsigned (ew E 12) + YQ0b.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YQ0b.r_lo r).
Proof.
intros E sp0 ap rest Hsk H12 Hap1 Hap2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vf_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; (subst; cbv beta);
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI; first [left; repeat split; img_lia | right; repeat split; img_lia].
Qed.
Lemma vf_rest_w {imgk : img} : forall E (rest : smem), skeleton rest = skeleton vf_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vf_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val] in Ha; try img_lia.
unfold F_STDERR, FILE_SZ in Ha. unfold writable_at.
img_apply (store_ok_all tfxsegs m 232 (Z_to_bv 64 F_STDERR));
[img_try (rewrite unsigned_lit_small by (unfold F_STDERR; img_lia); unfold F_STDERR; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDERR in *; img_lia); unfold F_STDERR in *; cbn; img_lia)].
Qed.
Definition stderr_fields_after_vf {imgk : img} : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, (0x96d9c + D_10ec)); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, (0x96ee8 + D_10ec)); (80, 8%N, (0x96ee0 + D_10ec)); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stderr_after_vfprintf {imgk : img} : (word -> option byte) -> Prop := file_is stderr_fields_after_vf.
Lemma vf_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_runN tfxsegs tfxmusl_tbl FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Definition band_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (lo =? - VF_STK) && (hi <=? 0)
| _ => false
end.
Definition vf_windows_ok {imgk : img} (ss : sstate) : bool :=
forallb (fun t => band_winb t || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vf_windows_sound {imgk : img} : forall E ss sp0 a,
vf_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ vf_file a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vf_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [img_try (apply orb_prop in Hb as [Hb|Hb])|].
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. (subst lo; cbv beta).
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vf_file. img_lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. img_lia.
Qed.
Definition vf_stack0_ok (ss : sstate) : bool :=
match ss_mem ss with
| r :: _ => match YQ0b.r_base r with Some 2%nat => (YQ0b.r_wlo r =? - VF_STK) && (YQ0b.r_whi r =? 0) | _ => false end
| [] => false
end.
Lemma vf_band_present {imgk : img} : forall (W : world tfxsegs) E ss ms sp0,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> vf_stack0_ok ss = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, vf_band sp0 a -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 HS Hb Hsp Hhi a Ha. unfold vf_band in Ha. assert (HVF : VF_STK = 9104) by img_refl.
pose proof asan_consts as (_ & _ & _ & _ & C5).
img_apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_ok in Hb. destruct (ss_mem ss) as [|r rs]; [img_try (discriminate)|].
destruct (YQ0b.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma vf_band_present_ecall {imgk : img} : forall (W : world tfxsegs) E ss ms sp0,
st_ok_ecall tfxsegs E ss (restrict (w_H W) ms) -> vf_stack0_ok ss = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, vf_band sp0 a -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 HS Hb Hsp Hhi a Ha. unfold vf_band in Ha. assert (HVF : VF_STK = 9104) by img_refl.
pose proof asan_consts as (_ & _ & _ & _ & C5).
img_apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_ok in Hb. destruct (ss_mem ss) as [|r rs]; [img_try (discriminate)|].
destruct (YQ0b.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia.
Qed.
Definition band_winb_n (whi : Z) (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (lo =? - VF_STK) && (hi <=? whi)
| _ => false
end.
Definition vf_windows_okn {imgk : img} (ss : sstate) (whi : Z) : bool :=
forallb (fun t => band_winb_n whi t || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vf_windows_sound_n {imgk : img} : forall E ss sp0 whi a,
vf_windows_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> (sp0 - VF_STK <= a < sp0 + whi) \/ vf_file a.
Proof.
intros E ss sp0 whi a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vf_windows_okn in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [img_try (apply orb_prop in Hb as [Hb|Hb])|].
- unfold band_winb_n in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. (subst lo; cbv beta).
cbn [base_val] in Hr. rewrite Hsp in Hr. left. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vf_file. img_lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. img_lia.
Qed.
Definition vf_stack0_okn (ss : sstate) (whi : Z) : bool :=
match ss_mem ss with
| r :: _ => match YQ0b.r_base r with Some 2%nat => (YQ0b.r_wlo r =? - VF_STK) && (YQ0b.r_whi r =? whi) | _ => false end
| [] => false
end.
Lemma vf_band_present_n {imgk : img} : forall (W : world tfxsegs) E ss ms sp0 whi,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> vf_stack0_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 whi HS Hb Hsp Hhi a Ha Ha'. assert (HVF : VF_STK = 9104) by img_refl.
pose proof asan_consts as (_ & _ & _ & _ & C5).
img_apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_okn in Hb. destruct (ss_mem ss) as [|r rs]; [img_try (discriminate)|].
destruct (YQ0b.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma vf_band_present_n_ecall {imgk : img} : forall (W : world tfxsegs) E ss ms sp0 whi,
st_ok_ecall tfxsegs E ss (restrict (w_H W) ms) -> vf_stack0_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 whi HS Hb Hsp Hhi a Ha Ha'. assert (HVF : VF_STK = 9104) by img_refl.
pose proof asan_consts as (_ & _ & _ & _ & C5).
img_apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_okn in Hb. destruct (ss_mem ss) as [|r rs]; [img_try (discriminate)|].
destruct (YQ0b.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma vf_band_present_gap {imgk : img} : forall (W : world tfxsegs) (mem memB : word -> option byte) sp0 whi,
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) ->
(forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) memB a) ->
(forall a, sp0 + whi <= a < sp0 -> memB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
forall a, vf_band sp0 a -> apresent (w_H W) memB a.
Proof.
intros W mem memB sp0 whi Hp Hw Hg a Ha. unfold vf_band in Ha.
destruct (Z_lt_le_dec a (sp0 + whi)) as [Hlt|Hge]; [img_try (img_apply Hw; img_lia)|].
destruct (Hp a ltac:(img_try (unfold vf_band; img_lia))) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite Hg by img_lia. img_exact Hb.
Qed.
Lemma Forall_range_of_forallb : forall zs, forallb (fun z => (0 <=? z) && (z <? 256)) zs = true -> Forall (fun z => 0 <= z < 256) zs.
Proof.
intros zs H. rewrite forallb_forall in H. img_apply Forall_forall. intros z Hz. specialize (H z Hz).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. img_lia.
Qed.
Lemma F_118cdc {imgk : img} : fetch_word tfxsegs (Z_to_bv 64 (0x9849c + D_10ec)) = Some (0x0005c603%bv : bv 32).
Proof.
replace (0x0005c603%bv : bv 32) with (Z_to_bv 32 0x0005c603) by (img_try (img_apply bv_eq; img_refl)).
img_apply (tfxmusl_tbl_ok (0x9849c + D_10ec) 0x0005c603). img_case; vm_compute. all: img_refl.
Qed.
Lemma D_118cdc : decode_any (0x0005c603%bv : bv 32) = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. (img_case; vm_refl_bv). Qed.
Lemma vf_lbu_nul {imgk : img} : forall (W : world tfxsegs) E ss ms md k (z : Z),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = (0x9849c + D_10ec) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
getr (ms_regs ms) 11 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
aview tfxsegs (w_H W) (ms_mem ms) z = Some 0 ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfxsegs E (set_regs_pc ss [((12%bv : bv 5), SLit 0)] (0x984a0 + D_10ec)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md k z HS Hpc Hrv Hat R11 Hz Hnul. pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
unfold aview in Hnul. destruct (mbyte tfxsegs (mrestrict (w_H W) (ms_mem ms)) z) as [b|] eqn:Hb; [|img_try (discriminate)].
cbn [option_map] in Hnul. injection Hnul as Hb0.
assert (Hrd : rdn tfxsegs (mrestrict (w_H W) (ms_mem ms)) (v_addi (getr (ms_regs ms) 11) (bv_signed (0%bv : bv 12))) 1%nat = Some [b]).
{ rewrite R11. replace (v_addi (Z_to_bv 64 z) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 z)
by (img_try (img_apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; img_change (bv_signed (0%bv : bv 12)) with 0;
unfold bv_wrap; img_change (bv_modulus 64) with (2 ^ 64); rewrite Z.add_0_r, Z.mod_mod by img_lia; img_refl)).
img_apply (proj2 (rdn_mbytes tfxsegs _ 1 z [b])). split; [img_refl|]. intros i Hi. replace i with 0%nat by img_lia.
rewrite Z.add_0_r. img_exact Hb. }
rewrite Hshape. eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
- rewrite restrict_mkst_fx. img_apply (step_lbu tfxsegs _ _ _ _ _ 12 11 (0%bv : bv 12) b F_118cdc eq_refl D_118cdc Hrd).
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [bv_eqb].
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
img_apply SRr_ret. split; [img_refl|]. eexists _, _. split; [img_refl|]. split; [|img_refl].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (623772 + D_10ec)) 4) with (Z_to_bv 64 (0x984a0 + D_10ec) : word) by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
img_apply (st_ok_set_regs tfxsegs k E E ss _ _ _ (0x984a0 + D_10ec) _ [((12%bv : bv 5), SLit 0)] HS (env_agree_refl k E) Hat Hrv).
+ img_case; vm_compute. all: img_refl.
+ intros r Hr. replace (bv_eqb (12%bv : bv 5) (0%bv : bv 5)) with false by img_refl. cbv beta iota.
cbn in Hr. destruct (bv_eqb r 12) eqn:E12; [img_try (discriminate)|].
rewrite getr_other; [img_refl|]. intros ->. rewrite bv_eqb_refl in E12. discriminate.
+ constructor; [|img_try (constructor)]. cbn [fst snd]. split; [img_refl|].
replace (bv_eqb (12%bv : bv 5) (0%bv : bv 5)) with false by img_refl. cbv beta iota.
rewrite getr_same by (img_try (intros H'; discriminate H')). cbn [sv_denot]. img_apply bv_eq.
rewrite !unsigned_lit_small; [img_try (img_exact Hb0) | img_lia | img_try (pose proof (u8_range b); img_lia)].
Qed.
Definition vf_add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_fact {imgk : img} : forall E ss ms n lo hi,
st_ok tfxsegs E ss ms -> ss_resv ss = None ->
lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfxsegs E (vf_add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, vf_add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [img_try (assumption)|]). split; [|img_try (split; assumption)].
cbn [atoms_ok]. split; [|img_try (img_exact HA)]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [img_try (img_exact Hr)|]. split; [img_try (rewrite Z.pow_0_r; img_apply Z.mod_1_r) | img_lia].
Qed.
End g.
Definition fp_ranges {imgk : img} : list (Z * nat) := [((0x64484 + D_2c4), 24%nat)].
Definition tbl_fp {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_ranges fp_ranges tbl_icpt))).
Lemma tbl_fp_eq {imgk : img} : tbl_fp = build_ranges fp_ranges tbl_icpt. Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
Lemma tbl_fp_ok {imgk : img} : table_ok tfxsegs tbl_fp.
Proof. img_destruct imgk. all: rewrite tbl_fp_eq. all: img_apply build_ranges_ok; [img_try (unfold fp_ranges; repeat constructor; cbn; discriminate) | img_try (img_exact tbl_icpt_ok)]. Qed.
Definition x2_ranges {imgk : img} : list (Z * nat) := [((0x88344 + D_a2c), 12%nat); ((0x4006c + D_2c4), 26%nat); ((0x3fa34 + D_2c4), 371%nat); ((0x542d8 + D_2c4), 5%nat); ((0x542ec + D_2c4), 319%nat); ((0x591f8 + D_2c4), 6%nat); ((0x9b894 + D_10ec), 62%nat)].
Definition x13_ranges {imgk : img} : list (Z * nat) := [((0x7056c + D_2c4), 13%nat); ((0x30794 + D_150), 36%nat)].
Definition tbl_x213 {imgk : img} : ctable := ltac:(img_eval_sel (fun imgk : img => (build_ranges (x2_ranges ++ x13_ranges) tfxmusl_tbl))).
Lemma tbl_x213_eq {imgk : img} : tbl_x213 = build_ranges (x2_ranges ++ x13_ranges) tfxmusl_tbl. Proof. img_case; lazymatch goal with |- ?l_ = _ => vm_cast_no_check (@eq_refl _ l_) end. Qed.
Lemma tbl_x213_ok {imgk : img} : table_ok tfxsegs tbl_x213.
Proof. img_destruct imgk. all: rewrite tbl_x213_eq. all: img_apply build_ranges_ok; [img_try (unfold x2_ranges, x13_ranges; cbn [app]; repeat constructor; cbn; discriminate) | img_try (img_exact tfxmusl_tbl_ok)]. Qed.
