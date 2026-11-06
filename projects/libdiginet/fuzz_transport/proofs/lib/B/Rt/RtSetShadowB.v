(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10 [image A's note, kept from grant A's header; its numbers are fuzz_grant.asan's]: the shadow-fill entries __asan_set_shadow_00 (0x546bc), __asan_set_shadow_f5 (0x547c4) and __asan_set_shadow_f8 (0x547dc) of libreac/fuzz_grant, over the asan-state definitions and the musl memset walk of the cgif_file_fuzzer proof as libreac/fuzz_grant holds them; one image instead of the two-image selector; addresses; module names; tfxsegs and TfxSyms become tfibsegs and GrantSyms. The f8 entry has the stub shape of f5 (same GOT slot 0x9c890, value 0xf8), as in cgif_rgb_fuzzer lib/YF8u.v tfx_set_shadow_f8. *)
(* Modified by Theorem Labs, 2026-10: relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) from lib/A/Rt/SetShadow.v, whose presence clause is a working branch 29b0734a150's: the entries __asan_set_shadow_00 / _f5 / _f8 are 0x54a48 / 0x54b50 / 0x54b68, the GOT chain read from image B is 0x9d6f0 -> 0x9f538 (__interception::real_memset) -> 0x96c94 (memset, YB1w's tfib_A_musl_memset), the A twins are the B core's lib/B/Y* twins and the per-image core modules lib.B's; the three theorems are renamed grantB_set_shadow_00 / _f5 / _f8. Every other line is image A's text. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Rt/SetShadow.v, with its module paths and addresses changed; 6 of its 189 lines of code are new or changed and 6 lines of the source are left out. *)
(* RtSetShadowB: the walks of the shadow-fill entries __asan_set_shadow_00 (0x552ac), __asan_set_shadow_f5 (0x553b4) and
   __asan_set_shadow_f8 (0x553cc) of fuzz_transport.asan-ubsan (41113a03c82f) against
   TransportRtCg.aset_shadow_realizes (lib/A/Prog/TransportRtCg.v, image-free), relocated from the released proof
   libreac/fuzz_grant proofs/lib/B/Rt/SetShadow.v (commit c3777b3715d0; image B of that unit, entries 0x54a48 / 0x54b50 /
   0x54b68). Each entry is a 24-byte stub (6 words) of this image, EQUAL-mod-pcrel to the donor's (2 pc-relative words
   each: the auipc / ld pair of one GOT read):
     _00 at 0x552ac: mv a2,a1; auipc a1,0x4f; ld a1,-0x5a0(a1); ld t1,0(a1); li a1,0; jr t1
     _f5 at 0x553b4: auipc a2,0x4f; ld a2,-0x6a4(a2); ld t1,0(a2); mv a2,a1; li a1,0xf5; jr t1
     _f8 at 0x553cc: auipc a2,0x4f; ld a2,-0x6bc(a2); ld t1,0(a2); mv a2,a1; li a1,0xf8; jr t1
   Each GOT read is of the word 0xa3d10, which holds 0xa5b58 (__interception::real_memset), which holds 0x9d270: musl
   memset (lib/B/YB1w.v tfib_A_musl_memset, EQUAL to the donor's). The symbolic run of a stub stops at musl memset with
   a1 = the fill value and a2 = the entry's a1 (stub_shape); lib/B/YE3d.v tfib_memset then fills the n shadow bytes.
   Changed from the donor: the three entries, the two words of ssh_rodata, module paths, GrantSyms -> TransportSyms, the
   theorem names, and the contract's file (lib/A/Prog/TransportRtCg.v; the donor's lib/Reusable/SetShadowDef.v has the
   same Definition text). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YB1w YE34 YF0l YF0m YF0x YE2y YE3d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportRtCg.
Definition SS00_ENTRY : Z := 0x552ac.
Definition SSF5_ENTRY : Z := 0x553b4.
Definition SSF8_ENTRY : Z := 0x553cc.
Definition ssh_ranges : list (Z * nat) := [(SS00_ENTRY, 6%nat); (SSF5_ENTRY, 6%nat); (SSF8_ENTRY, 6%nat)].
Definition tbl_ssh : ctable := Eval vm_compute in build_ranges ssh_ranges TEmpty.
Lemma tbl_ssh_eq : tbl_ssh = build_ranges ssh_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_ssh). Qed.
Lemma tbl_ssh_ok : table_ok tfibsegs tbl_ssh.
Proof. rewrite tbl_ssh_eq. apply build_ranges_ok; [unfold ssh_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.
Definition ssh_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := [(0xa3d10, 8, [(0, 8%N, 0xa5b58)]); (0xa5b58, 8, [(0, 8%N, 0x9d270)])].
Lemma ssh_rodata_chk : forall ly, rodata_chk ly ssh_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ssh FUEL s.
Definition ss_ent (pc : Z) : sstate := mkSS pc sr_atoms (map ro_region ssh_rodata) None (mkFacts [] [] []).
Definition e_00 : sstate := Eval vm_compute in fst (RUN (ss_ent SS00_ENTRY)).
Definition e_f5 : sstate := Eval vm_compute in fst (RUN (ss_ent SSF5_ENTRY)).
Definition e_f8 : sstate := Eval vm_compute in fst (RUN (ss_ent SSF8_ENTRY)).
Lemma r_00 : RUN (ss_ent SS00_ENTRY) = (e_00, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma r_f5 : RUN (ss_ent SSF5_ENTRY) = (e_f5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma r_f8 : RUN (ss_ent SSF8_ENTRY) = (e_f8, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition keep_regs : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 10].
Definition stub_shape (ss : sstate) (v : Z) : bool :=
(ss_pc ss =? tfib_A_musl_memset) && (match ss_resv ss with None => true | _ => false end) &&
sv_eqb (sr_get (ss_regs ss) 11%bv) (SLit v) && sv_eqb (sr_get (ss_regs ss) 12%bv) (SOff 11 0) &&
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep_regs.
Lemma shape_00 : stub_shape e_00 0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape_f5 : stub_shape e_f5 0xf5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape_f8 : stub_shape e_f8 0xf8 = true. Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ssh_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_ssh FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_ssh tbl_ssh_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TransportSyms B.
Variables (pc v : Z) (e1 : sstate).
Hypothesis Hrun : RUN (ss_ent pc) = (e1, RS_stopped SR_fetch).
Hypothesis Hshape : stub_shape e1 v = true.
Hypothesis Hv : 0 <= v < 256.
Theorem set_shadow_gen : TransportRtCg.aset_shadow_realizes tfibsegs B pc v.
Proof.
intros ly S W regs mem md cid pos q n HPRE Hin G10 G11 Hn Hq1 Hq2.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx.
set (H := w_H W) in *.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & Happ & _ & Hsh).
set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
assert (PR : forall a, q <= a < q + n -> apresent H mem a /\ ~ aowned B ly S a).
{ intros a Ha. replace a with (shadow_addr fa + (a - shadow_addr fa)) by lia. apply Hsh. lia. }
assert (RNG : TFIB_IMG_END <= q /\ q + n <= 2 ^ 46).
{ destruct Happ as [F0 F1]. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (F2 : fa + fb <= 2 ^ 47) by (destruct F1 as [F1 | [_ F1]]; unfold kLowShadowBeg, YG0f.ASAN_CEIL in *; lia).
assert (D1 : 0 <= fa / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (D2 : fb / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
unfold shadow_addr, SHADOW_OFF, TFIB_IMG_END in *. lia. }
destruct RNG as [Rlo Rhi]. assert (Rimg0 : 0 <= TFIB_IMG_END) by (unfold TFIB_IMG_END; lia).
set (EE := YE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (HS0 : st_ok tfibsegs EE (ss_ent pc) (restrict H (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ent, EE, YE2y.Env. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- exact (rodata_ok B TB ssh_rodata ly S H mem _ (ssh_rodata_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents. unfold ssh_rodata, ro_region, extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. exact I. }
unfold cfg_at. change (w64 pc) with (Z_to_bv 64 pc).
eapply SRr_bind; [apply (ssh_phase W EE _ _ _ _ _ HS0 Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z, ms_mem ms1 z = mem z).
{ intros z. apply HF1. intros Hw. destruct (in_wrange_windows EE _ _ Hw) as (b & lo & hi & Ht & Hb).
cbn in Ht. destruct Ht as [Hq|[Hq|[]]]; injection Hq as <- <- <-; cbn [base_val] in Hb; lia. }
unfold stub_shape in Hshape. apply andb_prop in Hshape as [Hshape KR]. apply andb_prop in Hshape as [Hshape S12].
apply andb_prop in Hshape as [Hshape S11]. apply andb_prop in Hshape as [Spc Srv].
apply Z.eqb_eq in Spc. assert (Hrv : ss_resv e1 = None) by (destruct (ss_resv e1); [discriminate | reflexivity]).
apply sv_eqb_eq in S11. apply sv_eqb_eq in S12. rewrite forallb_forall in KR.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 Hrv) as Hshape1. rewrite Spc in Hshape1.
set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
assert (KEEP1 : forall r, In r keep_regs -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H EE e1 ms1 _ HS1). specialize (KR r Hr). apply sv_eqb_eq in KR. rewrite KR.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EEreg.
unfold keep_regs in Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (A10 : getr regs1 10 = w64 q) by (rewrite <- G10; exact (KEEP1 10 ltac:(unfold keep_regs; cbn [In]; tauto))).
assert (A11 : getr regs1 11 = w64 v) by (unfold regs1; rewrite (st_ok_restrict_reg tfibsegs H EE e1 ms1 11%bv HS1), S11; reflexivity).
assert (A12 : getr regs1 12 = w64 n).
{ unfold regs1. rewrite (st_ok_restrict_reg tfibsegs H EE e1 ms1 12%bv HS1), S12. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEreg 11%nat 11%bv eq_refl). exact G11. }
assert (A1 : getr regs1 1 = getr regs 1) by (exact (KEEP1 1 ltac:(unfold keep_regs; cbn [In]; tauto))).
assert (DW : forall a, q <= a < q + n -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (PR a Ha) as [[Hh [b Hb]] _]. split; [|exact Hh].
apply YE2y.apresent_writable. split; [exact Hh|]. exists b. unfold mem1. rewrite MEQ1. exact Hb. }
set (nn := Z.to_nat n). assert (Hnn : Z.of_nat nn = n) by (subst nn; lia).
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 q) nn = true).
{ apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (tfib_memset (w64 q) (w64 v) (w64 n) nn (mrestrict H mem1) (seg_rom tfibsegs) regs1 A10 A11 A12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) SOK ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & B10 & Hkeep).
rewrite A1, Hra in Hms.
set (cb := Z_to_bv 8 (bv_unsigned (w64 v) mod 256)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 q) (repeat cb nn)) in Hms.
set (mem2 := munrestrict H mem1 m2r).
rewrite Hshape1. fold regs1 mem1.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _.
pose proof (same_but_materialized_trans _ _ _ (with_vm_backing_same md mat1) Hsbm) as HSBM.
change (unrestrict H mem1 (mkst regs2 (getr regs 1) m2r (seg_rom tfibsegs))) with (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)).
assert (LEN : Z.of_nat (length (repeat cb nn)) = n) by (rewrite repeat_length; exact Hnn).
assert (M2out : forall z : word, ~ (q <= bv_unsigned z < q + n) -> mem2 z = mem z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. rewrite <- (MEQ1 z). fold mem1. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 q) (repeat cb nn) z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) q) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LEN, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LEN, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (q + i)) = Some cb).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (q + i) ltac:(lia))).
subst m2r. rewrite (YE2y.wbytes_inside (repeat cb nn) m1r (w64 q) (Z_to_bv 64 (q + i)));
unfold w64; rewrite ?LEN, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (q + i - q)) with (Z.to_nat i) by lia. apply nth_error_repeat. lia. }
assert (CB : bv_unsigned cb = v).
{ subst cb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (AVout : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply M2out. rewrite unsigned_lit_small by lia. exact Ha. }
assert (AVin : forall i, 0 <= i < n -> aview tfibsegs H mem2 (q + i) = Some v).
{ intros i Hi. unfold aview, mbyte, mrestrict. rewrite (proj2 (DW (q + i) ltac:(lia))), (M2in i Hi). cbn [option_map]. rewrite CB. reflexivity. }
assert (PRES : forall a, apresent H mem a -> apresent H mem2 a).
{ intros a [Hh [b Hb]]. split; [exact Hh|]. set (z := Z_to_bv 64 a) in *.
destruct (Z_lt_le_dec (bv_unsigned z) q) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned z) (q + n)) as [L2|L2]].
- exists b. rewrite M2out; [exact Hb | lia].
- exists cb. assert (Ez : Z_to_bv 64 (q + (bv_unsigned z - q)) = z) by (replace (q + (bv_unsigned z - q)) with (bv_unsigned z) by lia; apply Z_to_bv_bv_unsigned).
rewrite <- Ez. apply M2in. lia.
- exists b. rewrite M2out; [exact Hb | lia]. }
apply SRr_ret. split; [reflexivity|]. exists regs2, mem2, model'.
pose proof (same_but_materialized_frame md model' HSBM) as MF.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|split; [|split; [exact HSBM|split; [exact AVin|split; [exact AVout|split; [intros a Ha; exact (PRES a (HpresE a Ha)) | exact PRES]]]]]].
-
apply (al_frame _ _ LAWS ly S W mem md mem2 model' HAR).
+ intros a Hr Hown. apply AVout; [exact Hr|]. intros Ha. exact (proj2 (PR a Ha) Hown).
+ intros a Hvw. rewrite (YE2y.aview_mod _ mem2 a). rewrite (YE2y.aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' q) as [L1|L1]; [rewrite AVout by lia; exact Hvw|].
destruct (Z_lt_le_dec a' (q + n)) as [L2|L2]; [|rewrite AVout by lia; exact Hvw].
replace a' with (q + (a' - q)) by lia. rewrite AVin by lia. discriminate.
+ apply MF. + apply MF. + apply MF.
+ intros a Hb Hh. change (w_H W (w64 a)) with (H (Z_to_bv 64 a)) in Hh. apply M2out. unfold w64. rewrite unsigned_lit_small by (exact (YE2y.in_band_rw_u64 a Hb)).
intros Ha. rewrite (proj2 (DW a Ha)) in Hh. discriminate.
-
intros r Hr.
assert (NE : forall x : bv 5, 11 <= bv_unsigned x <= 16 -> Z_to_bv 5 r <> x).
{ intros x Hx E. rewrite <- E in Hx. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. change (bv_modulus 5) with 32 in Hx.
unfold acallee_saved in Hr. rewrite Z.mod_small in Hx by lia. lia. }
rewrite Hkeep; [apply KEEP1; unfold acallee_saved in Hr; unfold keep_regs; cbn [In]; lia | | | | | |]; apply NE; (split; apply Z.leb_le; reflexivity).
Qed.
End d.
Theorem transportB_set_shadow_00 : forall (B : asyms), AR_laws tfibsegs B -> TransportSyms B -> TransportRtCg.aset_shadow_realizes tfibsegs B SS00_ENTRY 0.
Proof. intros B LAWS TB. exact (set_shadow_gen B LAWS TB SS00_ENTRY 0 e_00 r_00 shape_00 ltac:(lia)). Qed.
Theorem transportB_set_shadow_f5 : forall (B : asyms), AR_laws tfibsegs B -> TransportSyms B -> TransportRtCg.aset_shadow_realizes tfibsegs B SSF5_ENTRY 0xf5.
Proof. intros B LAWS TB. exact (set_shadow_gen B LAWS TB SSF5_ENTRY 0xf5 e_f5 r_f5 shape_f5 ltac:(lia)). Qed.
Theorem transportB_set_shadow_f8 : forall (B : asyms), AR_laws tfibsegs B -> TransportSyms B -> TransportRtCg.aset_shadow_realizes tfibsegs B SSF8_ENTRY 0xf8.
Proof. intros B LAWS TB. exact (set_shadow_gen B LAWS TB SSF8_ENTRY 0xf8 e_f8 r_f8 shape_f8 ltac:(lia)). Qed.
End c.
