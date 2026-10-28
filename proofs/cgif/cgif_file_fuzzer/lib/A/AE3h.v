(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AE3e AE3f AE3g AE6g AE39 AE2p AE3i AE22 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma region_ok_transport_chunks : forall E E' mem mem' r,
region_ok tfibsegs E mem r ->
base_val E' (YP09.r_base r) = base_val E (YP09.r_base r) ->
(forall c, In c (YP09.r_chunks r) -> match YP09.c_val c with CVal _ e => sv_denot E' e = sv_denot E e | CData _ _ _ => False | _ => True end) ->
(forall c a, In c (YP09.r_chunks r) ->
base_val E (YP09.r_base r) + YP09.c_off c <= a < base_val E (YP09.r_base r) + YP09.c_off c + c_len c ->
mbyte tfibsegs mem' a = mbyte tfibsegs mem a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at tfibsegs mem a -> writable_at tfibsegs mem' a) ->
region_ok tfibsegs E' mem' r.
Proof.
intros E E' mem mem' r HR Hb Hcv Hrd Hwr. unfold region_ok in HR. cbv zeta in HR.
destruct HR as (Hlo & Hhi & Hw & Hcs).
unfold region_ok. cbv zeta. rewrite Hb. split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. apply Hwr; [lia|]. apply Hw. exact Ho.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split.
+ specialize (Hcv c Hc). destruct (YP09.c_val c) as [w e|len|len|d s len]; cbn [cbyte] in *;
[rewrite Hcv; exact Hb1 | exact Hb1 | exact Hb1 | destruct Hcv].
+ rewrite (Hrd c); [exact Hb2 | exact Hc | lia].
Qed.
Lemma region_ok_filter : forall E mem r (keep : YP09.chunk -> bool),
region_ok tfibsegs E mem r ->
region_ok tfibsegs E mem (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(List.filter keep (YP09.r_chunks r))).
Proof.
intros E mem r keep (Hlo & Hhi & Hw & Hcs). unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hw|].
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc _]. exact (proj1 (Forall_forall _ _) Hcs c Hc).
Qed.
Definition A_vfprintf : Z := 0x93ad0.
Definition VF_STK : Z := 912 + 2 * ESTACK.
Definition vf_regions (apv : sv) : smem :=
[ YP09.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YP09.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ) fw_file_chunks;
YP09.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YP09.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YP09.mkRegion None A_canary (A_canary + 8) 0 0 [YP09.mkChunk A_canary (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 12%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 apv)];
img_ro_region ].
Definition vf_sr (fmt : Z) : list sv := sr_set (sr_set sr_atoms (10%bv : bv 5) (SLit F_STDERR)) (11%bv : bv 5) (SLit fmt).
Definition vf_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (12%nat, mkAF (2 ^ 44) (2 ^ 47) 3); (32%nat, mkAF 1 (2 ^ 47) 0) ] [] [].
Definition ss_vf (fmt : Z) (apv : sv) : sstate := mkSS A_vfprintf (vf_sr fmt) (vf_regions apv) None vf_facts.
Lemma vf_entry : forall (W : world tfibsegs) regs mem fmt apv ap argw cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 fmt -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 argw -> 1 <= argw < 2 ^ 47 ->
stderr_pristine (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
sv_denot (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) apv = Z_to_bv 64 argw ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) (ss_vf fmt apv)
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_vfprintf) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem fmt apv ap argw cval Hsp1 Hsp2 Hal Hpres H10 H11 H12 Hap1 Hap2 Hap8 Harg Hargw HF Hgot Hcan Hcv Hro Hapv.
rewrite restrict_mkst_fx. unfold ss_vf.
set (E := Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E12 : bv_unsigned (ew E 12) = ap) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 argw) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HVF : VF_STK = 9104) by reflexivity.
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 argw; Z_to_bv 64 cval]) with E.
- unfold vf_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; reflexivity]
| intros Hx; discriminate Hx | rewrite H11; reflexivity].
- unfold vf_regions, img_ro_region, fw_file_chunks. cbn. destruct apv; reflexivity.
- unfold vf_regions. repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- VF_STK)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold F_STDERR, FILE_SZ. split; [lia|]. split; [lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDERR));
[rewrite unsigned_lit_small by (unfold F_STDERR; lia); unfold F_STDERR; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDERR in *; lia); unfold F_STDERR in *; cbn; lia].
* unfold fw_file_chunks, stderr_fields. cbn [map].
unfold stderr_pristine, file_is, stderr_fields in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold STDERR_BUF; zside | zside | rewrite Z.add_0_l; unfold F_STDERR, STDERR_BUF in *; assumption]).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold A_canary; zside | zside |].
rewrite Z.add_0_l. exact Hgot.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ ap 0 8 _ argw); [exact Hapv | zside | zside | rewrite Z.add_0_r; exact Harg].
+ apply Hro.
- apply pairwise_disjoint_of_extents. unfold vf_regions, img_ro_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E12.
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [vf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E12, E32, unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try lia.
Qed.
Fixpoint lit_chunks (o : Z) (zs : list Z) : list YP09.chunk :=
match zs with
| [] => []
| b :: zs' => YP09.mkChunk o (CVal 1 (SLit b)) :: lit_chunks (o + 1) zs'
end.
Lemma lit_chunks_In : forall zs o c, In c (lit_chunks o zs) ->
exists j, (j < length zs)%nat /\ c = YP09.mkChunk (o + Z.of_nat j) (CVal 1 (SLit (nth j zs 0))).
Proof.
induction zs as [|b zs IH]; intros o c Hc; cbn in Hc; [destruct Hc|].
destruct Hc as [<- | Hc].
- exists 0%nat. split; [cbn; lia|]. rewrite Z.add_0_r. reflexivity.
- destruct (IH _ _ Hc) as (j & Hj & ->). exists (S j). split; [cbn; lia|]. cbn [nth]. f_equal. lia.
Qed.
Definition vf_after_icpt (k : nat) (ss : sstate) (ra osp o : Z) (zs : list Z) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS ra (sr_sets (ss_regs ss) (junk_upd k CLOB))
(YP09.mkRegion (YP09.r_base r0) (YP09.r_lo r0) (YP09.r_hi r0) (YP09.r_wlo r0) (YP09.r_whi r0)
(lit_chunks o zs ++
List.filter (fun c => (osp <=? YP09.c_off c) && chunk_out o (o + Z.of_nat (length zs)) c) (YP09.r_chunks r0))
:: rest)
None (ss_facts ss)
| [] => ss
end.
Lemma Z_to_bv8_mod64 : forall z, Z_to_bv 8 (z mod 2 ^ 64) = Z_to_bv 8 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma unsigned_lit8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.
Section l.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Let HBcode := ts_code B TL.
Lemma vf_stack_shadow : forall (W : world tfibsegs) ly S mem md sp0 a n,
AR tfibsegs B ly S W mem md ->
ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
sp0 - VF_STK + ESTACK <= a -> a + n <= sp0 -> 0 <= n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n /\
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) a n).
Proof.
intros W ly S mem md sp0 a n HAR Hstk Htop Ha Han Hn.
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg). unfold page_aligned in Lplo, Lphi.
pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz. unfold zero_shadow in Hz.
split.
- intros y Hy. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Ha Han Hn HVF HES. lia.
- intros Hn0 s Hs.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn0 Lplo Lphi Hstk Htop Ltop Ha Han Hn HVF HES. unfold SHADOW_OFF in *. lia.
Qed.
Lemma vf_stack_amem : forall (W : world tfibsegs) ly S mem md sp0 a n,
AR tfibsegs B ly S W mem md ->
ly_stk_lo ly + VF_STK <= sp0 -> sp0 < kHighMemEnd ->
sp0 - VF_STK <= a -> a + n <= sp0 -> amem_range a n.
Proof.
intros W ly S mem md sp0 a n HAR Hstk HtopS Ha Han.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.
Lemma vf_icpt_memcpy : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp o (xsv : sv) (x : Z) n zs,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = SOff 2 o -> sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x -> sr_get (ss_regs ss) 12 = SLit (Z.of_nat n) ->
lit_buf tfibsegs (ss_mem ss) xsv n = Some zs ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp o zs)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= o -> o + Z.of_nat n <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + Z.of_nat n <= 2 ^ 47 -> (x + Z.of_nat n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(sp0 + o + Z.of_nat n <= x \/ x + Z.of_nat n <= sp0 + o) -> amem_range x (Z.of_nat n) ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (Z.of_nat n) ->
(0 < Z.of_nat n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x (Z.of_nat n)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp o zs) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + o <= a < sp0 + o + Z.of_nat n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp o xsv x n zs HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 S11 Hxa S12 Hlit Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hon Hra Hra4 Hx0 Hxhi Hxs Hxd Hamx Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres Hra_x Hhull_x.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + o)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R11 : getr regsT 11 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; exact Hxa).
assert (R12 : getr regsT 12 = w64 (Z.of_nat n)) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; reflexivity).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (lit_buf_sound tfibsegs E (mrestrict (w_H W) memT) (ss_mem ss) xsv n zs HmemT Hlit) as Hsrc. rewrite Hxa in Hsrc.
pose proof (lit_buf_length tfibsegs _ _ _ _ Hlit) as Hzl.
apply (proj1 (rdn_mbytes tfibsegs (mrestrict (w_H W) memT) n x _)) in Hsrc as [_ Hsrc].
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md (sp0 + o) x (Z.of_nat n)).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. split; [apply apresent_writable; apply Hpres; lia|]. split; [| lia].
exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
-
intros y Hy. exists 0. split; [|left; reflexivity].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. lia.
-   intros Hn s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. unfold SHADOW_OFF in *. lia.
-   split; [lia|]. split; [lia|]. split.
+ intros a Ha. rewrite HspT. split; [|lia].
specialize (Hsrc (Z.to_nat (a - x)) ltac:(lia)). rewrite Z2Nat.id in Hsrc by lia. replace (x + (a - x)) with a in Hsrc by lia.
unfold aview. rewrite Hsrc. rewrite nth_error_map.
destruct (nth_error zs (Z.to_nat (a - x))) eqn:En; [cbn; discriminate|]. exfalso. apply nth_error_None in En. lia.
+ split; [lia|]. split; [exact Hamx|]. split; [exact Hra_x | exact Hhull_x]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_app. split.
++ apply Forall_forall. intros c Hc. destruct (lit_chunks_In _ _ _ Hc) as (j & Hj & ->).
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
specialize (Hsrc j ltac:(lia)). rewrite nth_error_map, (nth_error_nth' zs 0) in Hsrc by lia.
cbn [option_map] in Hsrc.
specialize (Heff (Z.of_nat j) ltac:(lia)). unfold aview in Heff. rewrite Hsrc in Heff. cbn [option_map] in Heff.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (sp0 + o + Z.of_nat j)) as [c|] eqn:Hc2; [|discriminate].
cbn [option_map] in Heff. injection Heff as Heff.
exists c. split; [| rewrite <- Hc2; f_equal; lia]. cbn [cbyte sv_denot]. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv8_mod64.
f_equal. apply bv_eq. symmetry. exact Heff.
++ apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
** lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
Qed.
Definition vf_after_icpt_n (k : nat) (ss : sstate) (ra osp whi ghi : Z) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS ra (sr_sets (ss_regs ss) (junk_upd k CLOB))
(YP09.mkRegion (YP09.r_base r0) (YP09.r_lo r0) (YP09.r_hi r0) (YP09.r_wlo r0) whi
(List.filter (fun c => (osp <=? YP09.c_off c) && chunk_out whi ghi c) (YP09.r_chunks r0))
:: rest)
None (ss_facts ss)
| [] => ss
end.
Lemma vf_icpt_memcpy_sym : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp whi ghi
(dsv xsv nsv : sv) (d x n : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> whi <= YP09.r_whi r0 <= 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = Z_to_bv 64 (sp0 + d) ->
sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = Z_to_bv 64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
no_cdata (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt_n k ss ra osp whi ghi)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= whi -> whi <= d -> d + n <= ghi -> ghi <= 0 -> 0 <= n ->
4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + n <= 2 ^ 47 -> (x + n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(sp0 + d + n <= x \/ x + n <= sp0 + d) -> amem_range x n ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, x <= a < x + n -> aview tfibsegs (w_H W) (ms_mem ms) a <> None) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x n) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt_n k ss ra osp whi ghi) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) (ms_mem ms2) (sp0 + d + i) = aview tfibsegs (w_H W) (ms_mem ms) (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + d <= a < sp0 + d + n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp whi ghi dsv xsv nsv d x n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hda S11 Hxa S12 Hna Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hwd Hdn Hghi Hn Hra Hra4 Hx0 Hxhi Hxs Hxd Hamx Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres Hsrc Hra_x Hhull_x.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + d)) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10; exact Hda).
assert (R11 : getr regsT 11 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; exact Hxa).
assert (R12 : getr regsT 12 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; exact Hna).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md (sp0 + d) x n).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. split; [apply apresent_writable; apply Hpres; lia|]. split; [| lia].
exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
-
intros y Hy. exists 0. split; [|left; reflexivity].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hwd Hdn Hghi Hn HVF HES. lia.
-   intros Hn0 s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn0 Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hwd Hdn Hghi Hn HVF HES. unfold SHADOW_OFF in *. lia.
-   split; [lia|]. split; [lia|]. split.
+ intros a Ha. rewrite HspT. split; [apply Hsrc; exact Ha | lia].
+ split; [lia|]. split; [exact Hamx|]. split; [exact Hra_x | exact Hhull_x]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0.
unfold vf_after_icpt_n in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split; [|split]]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
** lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- exact Heff.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
Qed.
Lemma vf_icpt_memcpy_ext : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp
(dsv xsv nsv : sv) (d x n : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = Z_to_bv 64 d ->
sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = Z_to_bv 64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 0 <= d -> (d + n <= sp0 - VF_STK \/ sp0 <= d) -> d + n <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + n <= 2 ^ 47 -> (x + n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(d + n <= x \/ x + n <= d) -> amem_range d n -> amem_range x n ->
(forall r, In r rest -> d + n <= base_val E (YP09.r_base r) + YP09.r_lo r \/ base_val E (YP09.r_base r) + YP09.r_hi r <= d) ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, x <= a < x + n -> aview tfibsegs (w_H W) (ms_mem ms) a <> None) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x n) ->
(forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a /\ ~ aowned B ly S a) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) d n) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) (ms_mem ms2) (d + i) = aview tfibsegs (w_H W) (ms_mem ms) (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (d <= a < d + n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp dsv xsv nsv d x n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hda S11 Hxa S12 Hna Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hd0 Hdband Hdhi Hn Hra Hra4 Hx0 Hxhi Hxs Hxd Hamd Hamx Hrdisj Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres Hsrc Hra_x Hhull_x Hdw Hra_d Hhull_d.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 d) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10; exact Hda).
assert (R11 : getr regsT 11 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; exact Hxa).
assert (R12 : getr regsT 12 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; exact Hna).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md d x n).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. destruct (Hdw a Ha) as [Hw1 Hw2]. split; [exact Hw1|]. split; [exact Hw2 | lia].
- exact Hamd.
- exact Hra_d.
- exact Hhull_d.
-   split; [lia|]. split; [lia|]. split.
+ intros a Ha. rewrite HspT. split; [apply Hsrc; exact Ha | lia].
+ split; [lia|]. split; [exact Hamx|]. split; [exact Hra_x | exact Hhull_x]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split; [|split]]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. pose proof (Hrdisj r Hr) as Hdj. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha, Hdj; cbn [base_val] in Ha, Hdj; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- exact Heff.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
Qed.
End l.
Section p.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ASTRNLEN : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Lemma vf_icpt_strnlen : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp (xsv : sv) (x n L : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_strnlen (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = xsv -> sv_denot E xsv = Z_to_bv 64 x -> sr_get (ss_regs ss) 11 = SLit n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> 2 * ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= n < 2 ^ 63 -> 0 < x -> 0 <= L -> L + 8 <= n -> L + 1 < 2 ^ 32 -> x + L + 1 <= 2 ^ 47 ->
(x + L + 1 <= sp0 + osp - 2 * ESTACK \/ sp0 + osp <= x) ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
first_byte tfibsegs W (ms_mem ms) x n 0 L ->
(forall a, x <= a < x + (L + 1) -> aview tfibsegs (w_H W) (ms_mem ms) a <> None) ->
amem_range x (L + 1) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x (L + 1) ->
(forall a, x + L < a < x + L - (x + L) mod 8 + 8 -> aview tfibsegs (w_H W) (ms_mem ms) a <> None) ->
mconsts_view W (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
getr (ms_regs ms2) 10 = w64 L /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - 2 * ESTACK <= a < sp0 + osp) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp xsv x n L HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hxa S11 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hn Hx0 HL HL8 HL32 Hxhi Hxs Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres Hfb Hsrc Hamx Hra_x Hhull_x Htail Hrom.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10; exact Hxa).
assert (R11 : getr regsT 11 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; reflexivity).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof ASTRNLEN as AM. unfold astrnlen_realizesM, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md x n L).
- split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
-   rewrite HspT. lia.
- intros a Ha. rewrite HspT in Ha. apply Hpres. lia.
- exact R10. - exact R11.
- lia. - lia. - lia. - exact HL8. - exact HL32. - lia.
- exact Hfb.
- intros a Ha. rewrite HspT. split; [apply Hsrc; exact Ha | lia].
- intros a Ha. rewrite HspT. lia.
- exact Hamx.
- exact Hra_x.
- exact Hhull_x.
- exact Htail.
- exact Hrom. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split; [exact Ha0 | split]]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_strnlen (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; lia.
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- intros a Hr Hs. apply Hfr; lia.
- exact Hpres2.
Qed.
End p.
Section u.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet (pc_wrap_memset (as_code B)).
Lemma vf_icpt_memset : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp o (c : Z) n,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memset (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = SOff 2 o -> sr_get (ss_regs ss) 11 = SLit c -> 0 <= c < 256 -> sr_get (ss_regs ss) 12 = SLit (Z.of_nat n) ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= o -> o + Z.of_nat n <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp o (repeat c n)) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + o <= a < sp0 + o + Z.of_nat n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp o c n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 S11 Hc S12 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hon Hra Hra4 Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + o)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R11 : getr regsT 11 = w64 c) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; reflexivity).
assert (R12 : getr regsT 12 = w64 (Z.of_nat n)) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; reflexivity).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
assert (Hzl : length (repeat c n) = n) by apply repeat_length.
pose proof (al_zshadow _ _ LAWS ly S W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMSET as AM. unfold aintrin_realizes, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md (sp0 + o) c (Z.of_nat n)).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. split; [apply apresent_writable; apply Hpres; lia|]. split; [| lia].
exact (al_stack _ _ LAWS ly S W (ms_mem ms) md a HAR ltac:(lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
-
intros y Hy. exists 0. split; [|left; reflexivity].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. lia.
-   intros Hn s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. unfold SHADOW_OFF in *. lia.
-   exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memset (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_app. split.
++ apply Forall_forall. intros ch Hch. destruct (lit_chunks_In _ _ _ Hch) as (j & Hj & ->).
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
specialize (Heff (Z.of_nat j) ltac:(lia)). unfold aview in Heff. rewrite Z.mod_small in Heff by lia.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (sp0 + o + Z.of_nat j)) as [cb|] eqn:Hc2; [|discriminate].
cbn [option_map] in Heff. injection Heff as Heff.
exists cb. split; [| rewrite <- Hc2; f_equal; lia]. cbn [cbyte sv_denot]. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite nth_repeat_lt by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv8_mod64.
f_equal. apply bv_eq. rewrite unsigned_lit8_small by lia. symmetry. exact Heff.
++ apply Forall_forall. intros ch Hch. apply filter_In in Hch as [Hch Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs ch Hch) as Hck.
pose proof (chunk_inside_facts _ ch (proj1 (forallb_forall _ _) Hci0 ch Hch)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
** lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros ch Hch. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr ch Hch) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val ch); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
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
Section a0.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HB : TfibSyms B.
Variable pcx : Z.
Variable XW : Z -> Prop.
Variable XPRE : world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis XH : xret_realizes tfibsegs B pcx XW XPRE.
Lemma vf_icpt_xcall : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pcx -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> exists bz, base_val E (YP09.r_base r) = bz /\ 0 <= bz + YP09.r_lo r /\ bz + YP09.r_hi r <= 2 ^ 43) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
(is_canary_region r = true \/ ~ aowned B ly S a) /\ ~ XW a) ->
(forall a, XW a -> ~ (sp0 - VF_STK <= a < sp0)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
XPRE W (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ aowned B ly S a -> ~ XW a ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW a -> apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hrest HrestX HXWb HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres HXP.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof XH as AM. unfold xret_realizes, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md); [|exact HXP].
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 pcx) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2; [lia | intros Hx; apply (HXWb _ Hx); lia | apply Hpres; lia]. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia | lia | | intros Hx; apply (HXWb _ Hx); lia].
apply (al_stack _ _ LAWS ly S W (ms_mem ms) md _ HAR). lia.
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. destruct (HrestX r a Hr Ha) as [[Hcan|Ho] Hx].
{
destruct (is_canary_region_sound r Hcan) as (Hcb & Hclo & Hchi & _). rewrite Hcb in Ha. cbn [base_val] in Ha.
replace a with (A_GOT_CANARY + (a - A_GOT_CANARY)) by lia. rewrite Hsbm' in HAR2.
apply (canary_got_kept B HB _ _ _ _ _ _ _ _ _ _ _ HAR HAR2). lia. }
apply mbyte_of_aview.
destruct (Hrest r Hr) as (bz & Hbz & Hrl & Hrh). rewrite Hbz in Ha. apply Hfr; [lia | lia | exact Ho | exact Hx].
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- intros a Hr Hs Ho Hx. apply Hfr; assumption.
- exact Hpres2.
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
Section c0.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable pcx : Z.
Variable XW : Z -> Prop.
Variable XPRE : world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis XH : xret_realizes_noar tfibsegs B pcx XW XPRE.
Lemma vf_icpt_xcall_noar : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pcx -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> exists bz, base_val E (YP09.r_base r) = bz /\ 0 <= bz + YP09.r_lo r /\ bz + YP09.r_hi r <= 2 ^ 43) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
(is_canary_region r = true \/ ~ aowned B ly S a) /\ ~ XW a) ->
(forall a, XW a -> ~ (sp0 - VF_STK <= a < sp0)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
XPRE W (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ aowned B ly S a -> ~ XW a ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW a -> apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hrest HrestX HXWb HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres HXP.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof XH as AM. unfold xret_realizes_noar, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md); [|exact HXP].
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HP & Hsbm & Hfr & Hpres2).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [exact HP | split]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 pcx) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2; [lia | intros Hx; apply (HXWb _ Hx); lia | apply Hpres; lia]. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia | lia | intros Hx; apply (HXWb _ Hx); lia].
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. destruct (HrestX r a Hr Ha) as [_ Hx].
destruct (Hrest r Hr) as (bz & Hbz & Hrl & Hrh). rewrite Hbz in Ha. apply Hfr; [lia | lia | exact Hx].
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- intros a Hr Hs Ho Hx. apply Hfr; assumption.
- exact Hpres2.
Qed.
End c0.
Definition RA_FX : Z := 0x937d4.
Definition OSP_FX : Z := -976.
Definition RA_SN : Z := 0x94298.
Definition OSP_SN : Z := -912.
Definition vf_str (W : world tfibsegs) (mem : word -> option byte) (s : Z) (str : list byte) : Prop :=
(forall i, (i < length str)%nat -> aview tfibsegs (w_H W) mem (s + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))) /\
aview tfibsegs (w_H W) mem (s + Z.of_nat (length str)) = Some 0 /\
Forall (fun b : byte => bv_unsigned b <> 0) str.
Lemma vf_str_xfer : forall (W : world tfibsegs) mem mem' s str,
vf_str W mem s str ->
(forall a, s <= a < s + Z.of_nat (length str) + 1 -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
vf_str W mem' s str.
Proof.
intros W mem mem' s str (H1 & H2 & H3) HF. split; [|split; [|exact H3]].
- intros i Hi. rewrite HF by lia. apply H1. exact Hi.
- rewrite HF by lia. exact H2.
Qed.
Lemma vf_str_first_byte : forall (W : world tfibsegs) mem s str n,
vf_str W mem s str -> Z.of_nat (length str) + 1 <= n ->
first_byte tfibsegs W mem s n 0 (Z.of_nat (length str)).
Proof.
intros W mem s str n (H1 & H2 & H3) Hn. split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) str 0%bv)). split.
+ replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply H1. lia.
+ rewrite Forall_nth in H3. apply (H3 (Z.to_nat i) 0%bv). lia.
- intros _. exact H2.
Qed.
Lemma vf_str_readable : forall (W : world tfibsegs) mem s str,
vf_str W mem s str ->
forall a, s <= a < s + Z.of_nat (length str) + 1 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros W mem s str (H1 & H2 & H3) a Ha.
destruct (Z.eq_dec a (s + Z.of_nat (length str))) as [->|Hne]; [rewrite H2; discriminate|].
replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia. rewrite H1 by lia. discriminate.
Qed.
Lemma vf_str_rdn : forall (W : world tfibsegs) mem s str,
vf_str W mem s str -> rdn tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 s) (length str) = Some str.
Proof.
intros W mem s str (H1 & H2 & H3). apply (proj2 (rdn_mbytes tfibsegs _ (length str) s str)). split; [reflexivity|].
intros i Hi. specialize (H1 i Hi). unfold aview in H1.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (s + Z.of_nat i)) as [b|] eqn:Hb; [|discriminate].
cbn in H1. injection H1 as H1. symmetry. rewrite (nth_error_nth' str 0%bv Hi). f_equal. apply bv_eq. symmetry. exact H1.
Qed.
Lemma aview_mbyte : forall (H : word -> bool) (m : word -> option byte) z v,
aview tfibsegs H m z = Some v -> exists b, mbyte tfibsegs (mrestrict H m) z = Some b /\ bv_unsigned b = v.
Proof.
intros H m z v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H m) z) as [b|]; [|discriminate].
cbn in Hv. injection Hv as Hv. exists b. split; [reflexivity | exact Hv].
Qed.
Lemma Forall_nth_range : forall (zs : list Z) i, Forall (fun z => 0 <= z < 256) zs -> (i < length zs)%nat -> 0 <= nth i zs 0 < 256.
Proof. intros zs i Hf Hi. rewrite Forall_nth in Hf. apply Hf. exact Hi. Qed.
Lemma lit_buf_aview : forall (W : world tfibsegs) E (m : word -> option byte) rs xsv x n zs,
mem_ok tfibsegs E (mrestrict (w_H W) m) rs -> lit_buf tfibsegs rs xsv n = Some zs -> sv_denot E xsv = Z_to_bv 64 x ->
Forall (fun z => 0 <= z < 256) zs ->
forall i, (i < n)%nat -> aview tfibsegs (w_H W) m (x + Z.of_nat i) = Some (nth i zs 0).
Proof.
intros W E m rs xsv x n zs Hmem Hlit Hx Hzs i Hi.
pose proof (lit_buf_sound tfibsegs E _ rs xsv n zs Hmem Hlit) as Hrd. rewrite Hx in Hrd.
pose proof (lit_buf_length tfibsegs _ _ _ _ Hlit) as Hlen.
apply (proj1 (rdn_mbytes tfibsegs _ n x _)) in Hrd as [_ Hrd].
unfold aview. rewrite (Hrd i Hi), nth_error_map, (nth_error_nth' zs 0) by lia. cbn [option_map]. f_equal.
apply unsigned_lit8_small. exact (Forall_nth_range zs i Hzs ltac:(lia)).
Qed.
Lemma rdn_cat3 : forall (H : word -> bool) (m : word -> option byte) a (l1 : list Z) (str : list byte) (l2 : list Z),
Forall (fun z => 0 <= z < 256) l1 -> Forall (fun z => 0 <= z < 256) l2 ->
(forall i, (i < length l1)%nat -> aview tfibsegs H m (a + Z.of_nat i) = Some (nth i l1 0)) ->
(forall i, (i < length str)%nat -> aview tfibsegs H m (a + Z.of_nat (length l1) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))) ->
(forall i, (i < length l2)%nat ->
aview tfibsegs H m (a + Z.of_nat (length l1) + Z.of_nat (length str) + Z.of_nat i) = Some (nth i l2 0)) ->
rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) (length l1 + length str + length l2)
= Some (map (Z_to_bv 8) l1 ++ str ++ map (Z_to_bv 8) l2).
Proof.
intros H m a l1 str l2 Hl1 Hl2 A1 A2 A3.
apply (proj2 (rdn_mbytes tfibsegs _ _ a _)). split; [rewrite !length_app, !length_map; lia|].
intros i Hi.
destruct (Nat.lt_ge_cases i (length l1)) as [C1|C1].
{ destruct (aview_mbyte H m _ _ (A1 i C1)) as (b & Hb & Hbv). rewrite Hb.
rewrite nth_error_app1 by (rewrite length_map; exact C1). rewrite nth_error_map, (nth_error_nth' l1 0) by exact C1.
cbn [option_map]. f_equal. apply bv_eq. rewrite Hbv, unsigned_lit8_small; [reflexivity|]. exact (Forall_nth_range l1 i Hl1 C1). }
rewrite nth_error_app2 by (rewrite length_map; exact C1). rewrite length_map.
destruct (Nat.lt_ge_cases (i - length l1) (length str)) as [C2|C2].
{ destruct (aview_mbyte H m _ _ (A2 (i - length l1)%nat C2)) as (b & Hb & Hbv).
replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia. rewrite Hb.
rewrite nth_error_app1 by exact C2. rewrite (nth_error_nth' str 0%bv) by exact C2. f_equal. apply bv_eq. exact Hbv. }
rewrite nth_error_app2 by exact C2.
destruct (aview_mbyte H m _ _ (A3 (i - length l1 - length str)%nat ltac:(lia))) as (b & Hb & Hbv).
replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (length str) + Z.of_nat (i - length l1 - length str)) by lia.
rewrite Hb. replace (i - length l1 - length str)%nat with (i - length l1 - length str)%nat by lia.
rewrite nth_error_map, (nth_error_nth' l2 0) by lia. cbn [option_map]. f_equal. apply bv_eq.
rewrite Hbv, unsigned_lit8_small; [reflexivity|]. exact (Forall_nth_range l2 (i - length l1 - length str) Hl2 ltac:(lia)).
Qed.
Definition vf_band (sp0 a : Z) : Prop := sp0 - VF_STK <= a < sp0.
Definition vf_file (a : Z) : Prop := F_STDERR <= a < F_STDERR + FILE_SZ.
Definition vf_tail (W : world tfibsegs) (mem : word -> option byte) (s L : Z) : Prop :=
forall a, s + L < a < s + L - (s + L) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Lemma vf_tail_xfer : forall (W : world tfibsegs) mem mem' sp0 s L,
vf_tail W mem s L ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
sp0 mod 16 = 0 -> 0 < s -> 0 <= L -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= sp0 - VF_STK \/ sp0 <= s) -> (s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) ->
vf_tail W mem' s L.
Proof.
intros W mem mem' sp0 s L Ht Hfr Hal Hs HL Hhi Hband Hfile a Ha. pose proof (Ht a Ha) as Hv.
pose proof (Z.mod_pos_bound (s + L) 8 ltac:(lia)) as Hm. pose proof (Z.div_mod (s + L) 8 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hsp. rewrite Hal, Z.add_0_r in Hsp.
set (q := (s + L) / 8) in *. set (m := (s + L) mod 8) in *. set (p2 := sp0 / 16) in *.
clearbody q m p2.
unfold vf_band, vf_file, VF_STK, ESTACK, F_STDERR, FILE_SZ in *.
rewrite Hfr; [exact Hv | lia | intros Hb; lia | intros Hf; lia].
Qed.
Lemma tfib_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < 0x9d000.
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. remember (seg_writable sg) as wr eqn:Ew. clear Eb Ez Ew.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-; try discriminate; lia.
Qed.
Lemma rom_view_xfer : forall (W : world tfibsegs) mem mem' sp0,
rom_view tfibsegs W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
2 ^ 44 <= sp0 -> rom_view tfibsegs W mem'.
Proof.
intros W mem mem' sp0 Hr Hfr Hsp a Ha. pose proof (tfib_rom_low a Ha) as Hlow.
rewrite Hfr; [exact (Hr a Ha) | lia | unfold vf_band, VF_STK, ESTACK; lia | unfold vf_file, F_STDERR, FILE_SZ; lia].
Qed.
Lemma mconsts_view_xfer : forall (W : world tfibsegs) mem mem' sp0,
mconsts_view W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
2 ^ 44 <= sp0 -> mconsts_view W mem'.
Proof.
intros W mem mem' sp0 Hr Hfr Hsp a Ha. pose proof mc_bounds as [MB1 MB2].
rewrite Hfr; [exact (Hr a Ha) | lia | unfold vf_band, VF_STK, ESTACK; lia | unfold vf_file, F_STDERR, FILE_SZ; lia].
Qed.
Lemma stderr_img_bytes_ok : zallb (img_byte_ok tfibsegs) F_STDERR (Z.to_nat FILE_SZ) = true.
Proof. vm_compute. reflexivity. Qed.
Section VI.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Hypothesis HFown : forall a, vf_file a -> ~ aowned B ly S a.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VI (mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VI_init : AR tfibsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VI mem0 md0.
Proof.
intros HAR Hp. split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [exact Hp|].
split; [intros; reflexivity | intros a _ _ Ha; exact Ha].
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
assert (HVF : VF_STK = 9104) by reflexivity.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ vf_file a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2. apply aview_eq_of. apply HFr; rewrite unsigned_lit_small by lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|split; [|split; [exact HpbB | split]]].
- apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. apply AVB; [exact Hr | |].
* intros Hb. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold vf_band in Hb; lia) Hown).
* intros Hf. exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ vf_file a \/ (~ vf_band sp0 a /\ ~ vf_file a)) by (unfold vf_band, vf_file; lia).
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* apply aview_some_of_apresent. apply HpbB. exact Hin.
*
unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
unfold vf_file in Hin.
pose proof (zallb_sound _ _ _ a stderr_img_bytes_ok ltac:(unfold FILE_SZ in *; lia)) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [cbn; discriminate | discriminate Hb].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
+ apply MF. + apply MF. + apply MF.
+
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (Hf' : ~ vf_file a) by (unfold in_band_rw, vf_file, F_STDERR, FILE_SZ, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin|Hout]; [exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
rewrite HF; [reflexivity | |]; rewrite unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia); assumption.
- eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same].
- intros a Hr H1 H2. rewrite AVB by assumption. apply Hfr; assumption.
- intros a Hr Hf Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
destruct CASE as [Hin | Hout]; [apply HpbB; exact Hin|].
destruct (Hpm a Hr Hf Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite HF; [exact Hb| |]; rewrite unsigned_lit_small by lia; assumption.
Qed.
Lemma VI_splice : forall mem md memB mdB (Sx : Z -> Prop),
VI mem md ->
AR tfibsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VI memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
split; [exact HARB|]. split; [eapply same_but_materialized_trans; [exact Hsbm | exact HsbmB]|].
split; [intros a Ha; apply HpmB; apply Hpb; exact Ha|]. split.
- intros a Hr H1 H2. rewrite HfrB; [apply Hfr; assumption | exact Hr | intros Hs; exact (H1 (HSx a Hs))].
- intros a Hr Hf Hp. apply HpmB. apply Hpm; assumption.
Qed.
End VI.
Lemma vf_shadow_xfer : forall B ly S (W : world tfibsegs) sp0 mem0 md0 mem md x0 m x n,
VI B ly S W sp0 mem0 md0 mem md -> ly_stk_lo ly + VF_STK <= sp0 ->
range_addressable (aview tfibsegs (w_H W) mem0) SHADOW_OFF x0 m -> shadow_hull_vis (aview tfibsegs (w_H W) mem0) x0 m ->
0 <= x0 -> x0 <= x -> x + n <= x0 + m -> x0 + m <= kHighMemEnd ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros B ly S W sp0 mem0 md0 mem md x0 m x n (HAR & _ & _ & Hfr & _) Hstk Hra Hh Hx0 Hx1 Hx2 Hx3.
assert (HVF : VF_STK = 9104) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (SH : forall y, 0 <= y < kHighMemEnd -> forall s, shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8 ->
aview tfibsegs (w_H W) mem s = aview tfibsegs (w_H W) mem0 s).
{ intros y Hy s Hs. pose proof (shadow_addr_bounds y Hy) as [B1 B2].
apply Hfr; unfold vf_band, vf_file, F_STDERR, FILE_SZ; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia. }
split.
- intros y Hy. destruct (Hra y ltac:(lia)) as (v & Hv & Hok). exists v. split; [|exact Hok].
rewrite (SH y ltac:(lia)); [exact Hv|]. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y). lia.
- intros Hn s Hs.
assert (Hy : exists y, x <= y < x + n /\ shadow_addr y / 8 * 8 <= s < shadow_addr y / 8 * 8 + 8).
{ unfold shadow_addr in *.
destruct (Z_lt_le_dec s ((x + n - 1) / 8 + SHADOW_OFF)) as [Hlt|Hge].
+ exists (x + Z.max 0 ((s - SHADOW_OFF) * 8 - x)). split; [lia|]. lia.
+ exists (x + n - 1). lia. }
destruct Hy as (y & Hy1 & Hy2). rewrite (SH y ltac:(lia) s Hy2). apply Hh. unfold shadow_addr in *. lia.
Qed.
Definition vf_rest : smem := Eval vm_compute in (tl (vf_regions (SLit 0))).
Lemma In_skel : forall (rest : smem) r, In r rest -> In (skel r) (skeleton rest).
Proof. intros rest r Hr. unfold skeleton. apply in_map. exact Hr. Qed.
Lemma vf_rest_ok : forall E sp0 ap (rest : smem),
skeleton rest = skeleton vf_rest ->
bv_unsigned (ew E 12) = ap -> sp0 <= ap -> ap + 8 <= 2 ^ 47 ->
forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r).
Proof.
intros E sp0 ap rest Hsk H12 Hap1 Hap2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vf_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; subst;
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, IMG_RO_LO, IMG_RO_HI; first [left; repeat split; lia | right; repeat split; lia].
Qed.
Lemma vf_rest_w : forall E (rest : smem), skeleton rest = skeleton vf_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold vf_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]; symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha; try lia.
unfold F_STDERR, FILE_SZ in Ha. unfold writable_at.
apply (store_ok_all tfibsegs m 232 (Z_to_bv 64 F_STDERR));
[rewrite unsigned_lit_small by (unfold F_STDERR; lia); unfold F_STDERR; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDERR in *; lia); unfold F_STDERR in *; cbn; lia].
Qed.
Definition stderr_fields_after_vf : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x92ba0); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x92cec); (80, 8%N, 0x92ce4); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stderr_after_vfprintf : (word -> option byte) -> Prop := file_is stderr_fields_after_vf.
Lemma vf_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tfibmusl_tbl FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition band_winb (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (lo =? - VF_STK) && (hi <=? 0)
| _ => false
end.
Definition vf_windows_ok (ss : sstate) : bool :=
forallb (fun t => band_winb t || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vf_windows_sound : forall E ss sp0 a,
vf_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ vf_file a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vf_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|].
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo.
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vf_file. lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Definition vf_stack0_ok (ss : sstate) : bool :=
match ss_mem ss with
| r :: _ => match YP09.r_base r with Some 2%nat => (YP09.r_wlo r =? - VF_STK) && (YP09.r_whi r =? 0) | _ => false end
| [] => false
end.
Lemma vf_band_present : forall (W : world tfibsegs) E ss ms sp0,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> vf_stack0_ok ss = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, vf_band sp0 a -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 HS Hb Hsp Hhi a Ha. unfold vf_band in Ha. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof asan_consts as (_ & _ & _ & _ & C5).
apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_ok in Hb. destruct (ss_mem ss) as [|r rs]; [discriminate|].
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.
Lemma vf_band_present_ecall : forall (W : world tfibsegs) E ss ms sp0,
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> vf_stack0_ok ss = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, vf_band sp0 a -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 HS Hb Hsp Hhi a Ha. unfold vf_band in Ha. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof asan_consts as (_ & _ & _ & _ & C5).
apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_ok in Hb. destruct (ss_mem ss) as [|r rs]; [discriminate|].
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.
Definition band_winb_n (whi : Z) (t : option nat * Z * Z) : bool :=
match t with
| (Some 2%nat, lo, hi) => (lo =? - VF_STK) && (hi <=? whi)
| _ => false
end.
Definition vf_windows_okn (ss : sstate) (whi : Z) : bool :=
forallb (fun t => band_winb_n whi t || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ) || (snd t <=? snd (fst t)))
(windows (ss_mem ss)).
Lemma vf_windows_sound_n : forall E ss sp0 whi a,
vf_windows_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> (sp0 - VF_STK <= a < sp0 + whi) \/ vf_file a.
Proof.
intros E ss sp0 whi a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold vf_windows_okn in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht).
apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|].
- unfold band_winb_n in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo.
cbn [base_val] in Hr. rewrite Hsp in Hr. left. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold vf_file. lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Definition vf_stack0_okn (ss : sstate) (whi : Z) : bool :=
match ss_mem ss with
| r :: _ => match YP09.r_base r with Some 2%nat => (YP09.r_wlo r =? - VF_STK) && (YP09.r_whi r =? whi) | _ => false end
| [] => false
end.
Lemma vf_band_present_n : forall (W : world tfibsegs) E ss ms sp0 whi,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> vf_stack0_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 whi HS Hb Hsp Hhi a Ha Ha'. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof asan_consts as (_ & _ & _ & _ & C5).
apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_okn in Hb. destruct (ss_mem ss) as [|r rs]; [discriminate|].
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.
Lemma vf_band_present_n_ecall : forall (W : world tfibsegs) E ss ms sp0 whi,
st_ok_ecall tfibsegs E ss (restrict (w_H W) ms) -> vf_stack0_okn ss whi = true -> bv_unsigned (ew E 2) = sp0 -> 2 ^ 44 <= sp0 <= 2 ^ 47 ->
forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp0 whi HS Hb Hsp Hhi a Ha Ha'. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof asan_consts as (_ & _ & _ & _ & C5).
apply (apresent_of_writable (w_H W) (ms_mem ms) a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
unfold vf_stack0_okn in Hb. destruct (ss_mem ss) as [|r rs]; [discriminate|].
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hbase; try discriminate.
apply andb_prop in Hb as [Hw1 Hw2]. apply Z.eqb_eq in Hw1. apply Z.eqb_eq in Hw2.
apply Forall_inv in Hrs. destruct Hrs as (_ & _ & Hw & _). rewrite Hbase in Hw. cbn [base_val restrict ms_mem] in Hw.
rewrite Hsp, Hw1, Hw2 in Hw. replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.
Lemma vf_band_present_gap : forall (W : world tfibsegs) (mem memB : word -> option byte) sp0 whi,
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) ->
(forall a, sp0 - VF_STK <= a < sp0 + whi -> a < sp0 -> apresent (w_H W) memB a) ->
(forall a, sp0 + whi <= a < sp0 -> memB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
forall a, vf_band sp0 a -> apresent (w_H W) memB a.
Proof.
intros W mem memB sp0 whi Hp Hw Hg a Ha. unfold vf_band in Ha.
destruct (Z_lt_le_dec a (sp0 + whi)) as [Hlt|Hge]; [apply Hw; lia|].
destruct (Hp a ltac:(unfold vf_band; lia)) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hg by lia. exact Hb.
Qed.
Lemma Forall_range_of_forallb : forall zs, forallb (fun z => (0 <=? z) && (z <? 256)) zs = true -> Forall (fun z => 0 <= z < 256) zs.
Proof.
intros zs H. rewrite forallb_forall in H. apply Forall_forall. intros z Hz. specialize (H z Hz).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma F_118cdc : fetch_word tfibsegs (Z_to_bv 64 0x942a0) = Some (0x0005c603%bv : bv 32).
Proof.
replace (0x0005c603%bv : bv 32) with (Z_to_bv 32 0x0005c603) by (apply bv_eq; reflexivity).
apply (tfibmusl_tbl_ok 0x942a0 0x0005c603). vm_compute. reflexivity.
Qed.
Lemma D_118cdc : decode_any (0x0005c603%bv : bv 32) = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma vf_lbu_nul : forall (W : world tfibsegs) E ss ms md k (z : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = 0x942a0 -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
getr (ms_regs ms) 11 = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem ms) z = Some 0 ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [((12%bv : bv 5), SLit 0)] 0x942a4) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md k z HS Hpc Hrv Hat R11 Hz Hnul. pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
unfold aview in Hnul. destruct (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) z) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hnul. injection Hnul as Hb0.
assert (Hrd : rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (v_addi (getr (ms_regs ms) 11) (bv_signed (0%bv : bv 12))) 1%nat = Some [b]).
{ rewrite R11. replace (v_addi (Z_to_bv 64 z) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 z)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; change (bv_signed (0%bv : bv 12)) with 0;
unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.add_0_r, Z.mod_mod by lia; reflexivity).
apply (proj2 (rdn_mbytes tfibsegs _ 1 z [b])). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia.
rewrite Z.add_0_r. exact Hb. }
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_lbu tfibsegs _ _ _ _ _ 12 11 (0%bv : bv 12) b F_118cdc eq_refl D_118cdc Hrd).
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [bv_eqb].
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 606880) 4) with (Z_to_bv 64 0x942a4 : word) by (apply bv_eq; vm_compute; reflexivity).
apply (st_ok_set_regs tfibsegs k E E ss _ _ _ 0x942a4 _ [((12%bv : bv 5), SLit 0)] HS (env_agree_refl k E) Hat Hrv).
+ vm_compute. reflexivity.
+ intros r Hr. replace (bv_eqb (12%bv : bv 5) (0%bv : bv 5)) with false by reflexivity. cbv beta iota.
cbn in Hr. destruct (bv_eqb r 12) eqn:E12; [discriminate|].
rewrite getr_other; [reflexivity|]. intros ->. rewrite bv_eqb_refl in E12. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [reflexivity|].
replace (bv_eqb (12%bv : bv 5) (0%bv : bv 5)) with false by reflexivity. cbv beta iota.
rewrite getr_same by (intros H'; discriminate H'). cbn [sv_denot]. apply bv_eq.
rewrite !unsigned_lit_small; [exact Hb0 | lia | pose proof (u8_range b); lia].
Qed.
Definition vf_add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_fact : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None ->
lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (vf_add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, vf_add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
End g.
Definition fp_ranges : list (Z * nat) := [(0x63968, 24%nat)].
Definition tbl_fp : ctable := Eval vm_compute in build_ranges fp_ranges tbl_icpt.
Lemma tbl_fp_eq : tbl_fp = build_ranges fp_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_fp). Qed.
Lemma tbl_fp_ok : table_ok tfibsegs tbl_fp.
Proof. rewrite tbl_fp_eq. apply build_ranges_ok; [unfold fp_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok]. Qed.
Definition x2_ranges : list (Z * nat) := [(0x813d4, 12%nat); (0x3f898, 26%nat); (0x3f260, 371%nat); (0x537bc, 5%nat); (0x537d0, 319%nat); (0x586dc, 6%nat); (0x97698, 62%nat)].
Definition x13_ranges : list (Z * nat) := [(0x6fa50, 13%nat); (0x30398, 36%nat)].
Definition tbl_x213 : ctable := Eval vm_compute in build_ranges (x2_ranges ++ x13_ranges) tfibmusl_tbl.
Lemma tbl_x213_eq : tbl_x213 = build_ranges (x2_ranges ++ x13_ranges) tfibmusl_tbl. Proof. vm_cast_no_check (eq_refl tbl_x213). Qed.
Lemma tbl_x213_ok : table_ok tfibsegs tbl_x213.
Proof. rewrite tbl_x213_eq. apply build_ranges_ok; [unfold x2_ranges, x13_ranges; cbn [app]; repeat constructor; cbn; discriminate | exact tfibmusl_tbl_ok]. Qed.
