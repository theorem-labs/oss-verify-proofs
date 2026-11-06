(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPmK.v at a working branch b6bc009d623, relocated A->B by Theorem Labs tools; PIMG_RANGES is B's ReusableB/YE3i.v img_ro_chunks (gen_ye3i.py from B's YF0m), as the A file's list is A/AE3i.v's. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 19 address literal(s) rewritten, module paths changed; SH_LO/SH_HI recomputed as the 8-aligned shadow window of the format string at its fm address (shadow_addr FMT / 8 * 8, shadow_addr (FMT + len) / 8 * 8 + 8). *)
(* Modified by Theorem Labs, 2026-10: kit for ASan's printf_common (fm.asan 0x44d84) walks: pcm_scheck is A/YE2t.v
   pc_scheck with printf_common's own frame (sp0 = printf_common's entry sp, OSP = -2240), the string in any atom, the
   regions after the stack region constrained by the window they must avoid, and Poison's ARU in place of AR
   (pfs_check_srrU, lib/A/FMsnprintfPmChk.v); the entry regions (pimg, shz, slots) and their region_ok lemmas are new. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE3i YE39 YE3h YE38 YE7d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require YE2t YE35.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPmChk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- printf_common (ctx, format, aq), fm.asan ---- *)
Definition PC_ENTRY : Z := 0x44d84.   (* entry *)
Definition PC_FMTD : Z := 0x44de0.    (* after internal_strlen (format) *)
Definition PC_LW : Z := 0x45238.      (* lw a1, -0x1c(s8): dir.fieldPrecision, zeroed by internal_memset *)
Definition PC_SLCALL : Z := 0x452b0.  (* return point of internal_strlen (%s argument) *)
Definition PC_CHKEND : Z := 0x45210.  (* after COMMON_INTERCEPTOR_READ_RANGE (p, len + 1) *)
Definition WIN : Z := 4096.           (* the stack window the walk writes, below printf_common's entry sp *)
Definition OSP : Z := -2240.          (* printf_common's sp after its prologue, from the entry sp *)
Definition MSC : sv := SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2216))) (SLit 15).  (* internal_memset's alignment test *)
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fp FUEL stop s.
Definition RUNTOS (s : sstate) := RUNTO A_ISL s.
Definition LW0 (ss : sstate) : sstate := set_regs_pc ss [((11%bv : bv 5), SLit 0)] (PC_LW + 4).
Definition pc_after (k : nat) (ss : sstate) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS PC_CHKEND (sr_sets (ss_regs ss) (junk_upd k YE2t.CLOBP))
(YP09.mkRegion (YP09.r_base r0) (YP09.r_lo r0) (YP09.r_hi r0) (YP09.r_wlo r0) (YP09.r_whi r0)
(List.filter (fun c => OSP <=? YP09.c_off c) (YP09.r_chunks r0)) :: rest)
None (ss_facts ss)
| [] => ss
end.
(* ---- the entry state: stack, the format's shadow hull, the argument slots at P (atom 12), the read-only image,
   the interceptor constants; the arguments are atoms 32, 33, ... ---- *)
Definition stk : YP09.region := YP09.mkRegion (Some 2%nat) (- WIN) 0 (- WIN) 0 [].
(* the format's shadow hull: the 8-byte words of the bytes hb from lo, little-endian *)
Definition hw (hb : list Z) (k : nat) : Z := fold_right (fun i acc => nth (8 * k + i) hb 0 + 256 * acc) 0 (seq 0 8).
Definition shz (lo : Z) (hb : list Z) : YP09.region :=
YP09.mkRegion None lo (lo + 8 * Z.of_nat (length hb / 8)) lo lo
(map (fun k => YP09.mkChunk (lo + 8 * Z.of_nat k) (CVal 8 (SLit (hw hb k)))) (seq 0 (length hb / 8))).
Definition slots (n : nat) : YP09.region :=
YP09.mkRegion (Some 12%nat) 0 (8 * Z.of_nat n) 0 0 (map (fun j => YP09.mkChunk (8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 n)).
(* the read-only image bytes that are not runtime-owned statics (Tfib_owned_static: fm's .rodata global redzones and
   runtime cells), the bytes rom_viewN pins *)
Definition PIMG_RANGES : list (Z * Z) :=
[(0x10000, 0x102e8); (0x102f0, 0x10308); (0x10310, 0x10328); (0x10330, 0x10390); (0x103a0, 0x103a8); (0x103b0, 0x10418); (0x10458, 0x10518); (0x10558, 0x1cc5f); (0x1cc74, 0x20a88); (0x20a8c, 0x20d07); (0x20d20, 0x20d27); (0x20d40, 0x20d41); (0x20d60, 0x20d79); (0x20da0, 0x20dba); (0x20de0, 0x20e0d); (0x20e40, 0x20e6a); (0x20ea0, 0x20ecb); (0x20f00, 0x20f2e); (0x20f60, 0x20fa5); (0x20fc0, 0x20fc7); (0x20fe0, 0x20fe7); (0x21000, 0x21584); (0x21588, 0x215e8); (0x215ea, 0x2f1ac)].
Definition pimg_chunks : list YP09.chunk := map (fun lh => YP09.mkChunk (fst lh) (CImg (snd lh - fst lh))) PIMG_RANGES.
Definition pimg : YP09.region := YP09.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 pimg_chunks.
Definition sregs0 (f : Z) : list sv := firstn 11 sr_atoms ++ [SLit f] ++ skipn 12 sr_atoms.
Definition sfacts (fj : list nat) : facts :=
mkFacts ((2%nat, mkAF (2^44) (2^47) 4) :: map (fun j => ((32 + j)%nat, mkAF 4096 (2^47) 0)) fj) [] [].
Definition st0 (f lo : Z) (hb : list Z) (n : nat) (fj : list nat) : sstate :=
mkSS PC_ENTRY (sregs0 f) (stk :: shz lo hb :: slots n :: pimg :: map ro_region icpt_rodata) None (sfacts fj).
Section q.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
(* internal_strlen (p) then READ_RANGE (p, len + 1) (pfs_check_srrU), from the call at A_ISL to PC_CHKEND *)
Lemma pcm_scheck : forall (W : world tfibsegs) E ss ms md ly S U (sp0 : Z) r0 rest k (xi : nat) (x L : Z) (str : list byte),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = A_ISL -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E xi = Z_to_bv 64 x ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - WIN -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - WIN -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit PC_SLCALL -> sr_get (ss_regs ss) 2 = SOff 2 OSP -> sr_get (ss_regs ss) 10 = SOff xi 0 -> sr_get (ss_regs ss) 22 = SOff xi 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (pc_after k ss)) = true ->
no_cdata (ss_mem (pc_after k ss)) = true ->
mem_atoms_lt k (ss_mem (pc_after k ss)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
(forall r, In r rest -> YP09.r_whi r <= YP09.r_wlo r) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
0 <= a < 2 ^ 64 /\ ~ (sp0 + OSP - 72 <= a < sp0 + OSP)) ->
ARU tfibsegs B ly S U W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + WIN <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - WIN <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
vf_str W (ms_mem ms) x str -> L = Z.of_nat (length str) -> L + 1 < 2 ^ 32 -> 0 < x -> x + L + 1 <= 2 ^ 47 ->
amem_range x (L + 1) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x (L + 1) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 md2,
c' = mkCfg ms2 md2 /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) YE2t.CLOBP)) (pc_after k ss) (restrict (w_H W) ms2) /\
ARU tfibsegs B ly S U W (ms_mem ms2) md2 /\ same_but_materialized md md2 /\
(forall z : word, ~ (sp0 + OSP - 72 <= bv_unsigned z < sp0 + OSP) -> ms_mem ms2 z = ms_mem ms z) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S U sp0 r0 rest k xi x L str HS Hpc Hrv Usp E12 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 S10 S22
Hat Hwf2 Hnc2 Hma2 Hci0 HrestW Hrest HAR Hsp44 Hsp16 Hstk Htop Hpres HSTR HL HL32 Hx0 Hxhi Hamx Hra_x Hhull_x.
pose proof YF0x.Hwx_tfa as Hwx. unfold WIN, OSP in *.
assert (HISL : A_ISL = 409512) by reflexivity. assert (HSLC : PC_SLCALL = 283312) by reflexivity.
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W (ms_mem ms) md HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hamr : x + L + 1 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamx; lia).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *. set (H := w_H W) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 PC_SLCALL) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 - 2240)) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 2 HS), S2; cbn [sv_denot]; rewrite Usp; f_equal; lia).
assert (R10 : getr regsT 10 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 10 HS), S10; cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (R22 : getr regsT 22 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 22 HS), S22; cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
destruct HSTR as (Hsb & Hs0 & Hnz).
assert (LEN : Z.of_nat (length str) = L) by lia.
assert (Hnul : ~ In NUL str).
{ intros Hin. apply In_nth with (d := NUL) in Hin as (j & Hj & Hnj). pose proof (proj1 (Forall_forall _ _) Hnz _ (nth_In str NUL Hj)) as Hb. apply Hb. rewrite Hnj. reflexivity. }
assert (Hrd : forall j, (j <= length str)%nat -> rdn tfibsegs (mrestrict H memT) (Z_to_bv 64 (bv_unsigned (w64 x) + Z.of_nat j)) 1 = Some [nth j (str ++ [NUL]) NUL]).
{ intros j Hj. unfold w64. rewrite unsigned_lit_small by lia.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
destruct (Nat.lt_ge_cases j (length str)) as [Hlt|Hge].
- rewrite app_nth1 by lia. rewrite (YF0x.aview_byte H memT _ (bv_unsigned (nth j str 0%bv))); [rewrite Z_to_bv_bv_unsigned; rewrite (nth_indep _ 0%bv NUL) by lia; reflexivity|]. exact (Hsb j Hlt).
- assert (Hj' : j = length str) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
rewrite (YF0x.aview_byte H memT _ 0); [reflexivity|]. exact Hs0. }
destruct (tfib_istrlen str (w64 x) (mrestrict H memT) (seg_rom tfibsegs) regsT R10 Hnul Hrd ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)) as (regs2 & Hms & A10 & KEEP).
rewrite R1 in Hms. replace (v_jalr (Z_to_bv 64 PC_SLCALL) 0) with (Z_to_bv 64 PC_SLCALL : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
rewrite Hshape. unfold memT in Hms |- *.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H (ms_mem ms) (mrestrict H (ms_mem ms))).
assert (M2 : forall z, mem2 z = ms_mem ms z) by (intros z; subst mem2; apply YE7d.munrestrict_mrestrict_same).
assert (AV2 : forall a, aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms) a) by (intros a; apply aview_same; apply M2).
assert (K2 : forall (rr : bv 5), rr <> 10%bv -> rr <> 11%bv -> rr <> 12%bv -> getr regs2 rr = getr regsT rr) by (intros rr; apply KEEP).
assert (R2sp : spZ regs2 = sp0 - 2240) by (unfold spZ; rewrite (K2 2%bv) by (intros H'; discriminate H'); rewrite R2; apply unsigned_lit_small; lia).
assert (HAR2 : ARU tfibsegs B ly S U W mem2 model').
{ apply (ARU_frame tfibsegs B LAWS ly S U W (ms_mem ms) md mem2 _ HAR); [intros a _ _; apply AV2 | intros a Hv; rewrite AV2; exact Hv | | | | exact (YE2y.hs_kept_eq _ _ _ M2)]; apply (same_but_materialized_frame md _ Hsbm). }
eapply SRr_bind.
{ apply (pfs_check_srrU B LAWS TB ly S W regs2 mem2 model' x (L + 1) U HAR2).
- rewrite R2sp. replace (sp0 - 2240) with (sp0 + (-140) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
- rewrite R2sp. unfold RC_SCR. lia.
- rewrite R2sp. lia.
- intros a Ha. rewrite R2sp in Ha. unfold RC_SCR in Ha. apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). apply Hpres. lia.
- rewrite A10, LEN. unfold w64. f_equal; lia.
- rewrite (K2 22%bv) by (intros H'; discriminate H'). exact R22.
- exact Hx0.
- lia.
- lia.
- lia.
- exact Hamx.
- eapply range_addressable_agree; [|exact Hra_x]. intros z Hz. apply AV2.
- intros s' Hs. rewrite AV2. exact (Hhull_x s' Hs). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & _ & Hfr3 & Hpm3 & Hptw3).
rewrite R2sp in Hfr3, Hptw3. unfold RC_SCR in Hfr3, Hptw3.
apply SRr_ret. split; [reflexivity|]. exists (mkst regs3 (w64 RC_END) mem3 (seg_rom tfibsegs)), md3.
split; [reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold pc_after in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [exact HAR3 | split; [|split]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst]. change (w64 RC_END) with (Z_to_bv 64 PC_CHKEND).
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs3 (Z_to_bv 64 A_ISL) PC_CHKEND
(mrestrict H (ms_mem ms)) (mrestrict H mem3) rs [] YE2t.CLOBP HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (YE2t.not_clobp_cases r Hr) as [-> | [Hcs Hne]]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (K3 (bv_unsigned r) Hcs Hne). rewrite Z_to_bv_bv_unsigned.
apply K2; intros ->; clear -Hcs Hne; unfold acallee_saved in Hcs;
match type of Hne with bv_unsigned ?x <> _ => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v in * end; lia.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply YE2y.apresent_writable. apply Hpm3. apply (apresent_same H (ms_mem ms) mem2 _ (M2 _)). apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk1]. apply Z.leb_le in Hk1. unfold OSP in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. rewrite Hfr3; [apply AV2 | lia | lia].
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
pose proof (HrestW r Hr) as Hrw.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. destruct (Hrest r a Hr Ha) as [Ha64 Hout]. rewrite Hfr3; [apply AV2 | exact Ha64 | unfold OSP in Hout; lia].
++ intros a Ha _. exfalso. lia.
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- eapply same_but_materialized_trans; [exact Hsbm | exact Hsbm3].
- intros z Hz. cbn [ms_mem mkst]. rewrite Hptw3 by exact Hz. apply M2.
- intros a Hp. cbn [ms_mem mkst]. apply Hpm3. apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). exact Hp.
Qed.
End q.
(* ---- the entry regions ---- *)
Lemma in_img_lo : forall a, 0x10000 <= a < 0x30000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|].
cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. lia.
Qed.
Lemma in_rom_lo : forall a, 0x10000 <= a < 0x30000 -> in_rom tfibsegs a.
Proof.
intros a Ha. unfold in_rom.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|].
cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. split; [exact P3|]. lia.
Qed.
Lemma pimg_bytes_ok : forallb (fun c => zallb (img_byte_ok tfibsegs) (YP09.c_off c) (Z.to_nat (c_len c))) pimg_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pimg_inside : Forall (fun c => IMG_RO_LO <= YP09.c_off c /\ YP09.c_off c + c_len c <= IMG_RO_HI /\ exists n, YP09.c_val c = CImg n) pimg_chunks.
Proof.
unfold pimg_chunks, PIMG_RANGES, IMG_RO_LO, IMG_RO_HI. cbn [map fst snd].
repeat (apply Forall_cons; [cbn; split; [lia|]; split; [lia | eexists; reflexivity]|]). apply Forall_nil.
Qed.
Lemma pimg_unowned :
forallb (fun c => forallb (fun r => (fst r + snd r <=? YP09.c_off c) || (YP09.c_off c + c_len c <=? fst r)) Tfib_owned_static) pimg_chunks = true.
Proof. vm_compute. reflexivity. Qed.
(* the hull bytes: a byte of the shadow of the image [0x10000, 0x30000), either a constant cell or in a zero-shadow range *)
Definition zsh_in (s : Z) : bool :=
existsb (fun r => (shadow_addr (fst r) <=? s) && (s <? shadow_addr (fst r) + snd r / 8)) Tfib_zero_shadow.
Definition hb_ok (ly : alayout) (s v : Z) : bool :=
(0x7fffa000 <=? s) && (s <? 0x7fffe000) && (0 <=? v) && (v <? 256) &&
(const_chk ly s 1 v || ((v =? 0) && zsh_in s)).
Definition hull_ok (ly : alayout) (lo : Z) (hb : list Z) : bool :=
forallb (fun i => hb_ok ly (lo + Z.of_nat i) (nth i hb 0)) (seq 0 (length hb)) &&
forallb (fun k => forallb (fun i => YO0f.le_byte (hw hb k) 8 i =? nth (8 * k + i) hb 0) (seq 0 8) && (0 <=? hw hb k) && (hw hb k <? 2 ^ 64))
(seq 0 (length hb / 8)) &&
(0x7fffa000 <=? lo) && (lo + Z.of_nat (length hb) <=? 0x7fffe000).
End k.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma pimg_ok : forall (W : world tfibsegs) mem E, rom_viewN tfibsegs B W mem -> region_ok tfibsegs E (mrestrict (w_H W) mem) pimg.
Proof.
intros W mem E Hr.
assert (Hm : forall c, In c pimg_chunks -> forall a, YP09.c_off c <= a < YP09.c_off c + c_len c ->
mbyte tfibsegs (mrestrict (w_H W) mem) a = img_byte tfibsegs a).
{ intros c Hc a Ha.
pose proof (proj1 (Forall_forall _ _) pimg_inside c Hc) as (Hlo & Hhi & _).
pose proof (proj1 (forallb_forall _ _) pimg_unowned c Hc) as Hown. cbn beta in Hown. rewrite forallb_forall in Hown.
assert (HA : 0x10000 <= a < 0x30000) by (unfold IMG_RO_LO, IMG_RO_HI in *; lia).
pose proof (Hr a (in_rom_lo a HA)) as Hi.
assert (Hno : ~ Exists (in_zr a) (as_owned_static B)).
{ rewrite (ts_owned B TB). intros Hex. apply Exists_exists in Hex as (r & Hrin & Hz). pose proof (Hown r Hrin) as Ho.
unfold in_zr in Hz. apply orb_prop in Ho as [Ho|Ho]; apply Z.leb_le in Ho; lia. }
assert (Hne : ~ (as_errno B <= a < as_errno B + 4)) by (rewrite (ts_errno B TB); unfold TFIB_ERRNO; lia).
specialize (Hi Hno Hne). unfold aview in Hi. unfold img_byte.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) a) as [b|]; destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b'|]; cbn in Hi;
[f_equal; apply bv_eq; injection Hi as Hi; exact Hi | discriminate | discriminate | reflexivity]. }
unfold region_ok, pimg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold IMG_RO_LO; lia|]. split; [unfold IMG_RO_HI; lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) pimg_bytes_ok c Hc) as Hz. cbn beta in Hz.
pose proof (zallb_sound _ _ _ (YP09.c_off c + i) Hz ltac:(rewrite Z2Nat.id by lia; lia)) as Hb.
rewrite !Z.add_0_l. rewrite (Hm c Hc (YP09.c_off c + i)) by lia.
pose proof (proj1 (Forall_forall _ _) pimg_inside c Hc) as (_ & _ & nn & Hv).
destruct c as [co cv]; cbn [YP09.c_off YP09.c_val] in *. subst cv. cbn [cbyte].
unfold img_byte_ok in Hb. destruct (img_byte tfibsegs (co + i)) as [b|]; [|discriminate Hb]. exists b. split; reflexivity.
Qed.
Lemma hb_byte : forall ly S U W mem md s v, ARU tfibsegs B ly S U W mem md -> hb_ok ly s v = true ->
mbyte tfibsegs (mrestrict (w_H W) mem) s = Some (Z_to_bv 8 v).
Proof.
intros ly S U W mem md s v HAR Hb. unfold hb_ok in Hb.
apply andb_prop in Hb as [Hb Hc]. apply andb_prop in Hb as [Hb Hv1]. apply andb_prop in Hb as [Hb Hv0]. apply andb_prop in Hb as [Hs1 Hs2].
apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2. apply Z.leb_le in Hv0. apply Z.ltb_lt in Hv1.
assert (Hs64 : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit_small; lia).
assert (Hns : in_ush U s = false).
{ destruct (in_ush U s) eqn:E; [|reflexivity]. exfalso.
destruct (ush_granule B ly S U s (ARU_ok tfibsegs B ly S U W mem md HAR) E) as (g & p & n & Hblk & G8 & Gs & Gp & Gn).
pose proof (Z.div_mod g 8 ltac:(lia)) as Gd. unfold shadow_addr, SHADOW_OFF in Gs.
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
set (gq := g / 8) in *. set (gm := g mod 8) in *. set (rq := req_size n / 8) in *.
apply (YCbq.blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p n g (ARU_AR tfibsegs B ly S U W mem md HAR) Hblk ltac:(lia)).
apply in_img_lo. lia. }
rewrite (mbyte_of_aview (w_H W) (w_H W) (unpoison U mem) mem s) by (symmetry; apply aview_unpoison_out; rewrite Hs64; exact Hns).
pose proof (ARU_ARm tfibsegs B ly S U W mem md HAR) as HM.
apply orb_prop in Hc as [Hc|Hc].
- pose proof (YF0x.tfib_const_lookup B TB ly S (w_H W) (unpoison U mem) s 1 v HM (const_chk_sound ly s 1 v Hc)) as Hvm.
specialize (Hvm 0%nat ltac:(lia)). rewrite Z.add_0_r in Hvm. rewrite Hvm.
replace (YO0f.le_byte v 1 0) with v; [reflexivity|]. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity.
- apply andb_prop in Hc as [Hv Hz]. apply Z.eqb_eq in Hv. subst v.
pose proof (am_zshadow _ _ _ _ HM) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ. rewrite (ts_zsh B TB) in HZ.
apply Forall_inv_tail in HZ. unfold zsh_in in Hz. apply existsb_exists in Hz as (r & Hr & Hrs).
apply andb_prop in Hrs as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
pose proof (proj1 (Forall_forall _ _) HZ r Hr (s - shadow_addr (fst r))) as Hz0.
unfold shadow_of_addr in Hz0. unfold shadow_addr in R1, R2, Hz0.
set (q1 := fst r / 8) in *. set (q2 := snd r / 8) in *.
replace (SHADOW_OFF + q1 + (s - (SHADOW_OFF + q1))) with s in Hz0 by lia.
apply (YF0x.aview_byte (w_H W) (unpoison U mem) s 0). apply Hz0. lia.
Qed.
Lemma shz_ok : forall ly S U W mem md E lo hb, ARU tfibsegs B ly S U W mem md -> hull_ok ly lo hb = true ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (shz lo hb).
Proof.
intros ly S U W mem md E lo hb HAR Hh. unfold hull_ok in Hh.
apply andb_prop in Hh as [Hh Hhi]. apply andb_prop in Hh as [Hh Hlo]. apply andb_prop in Hh as [Hb Hw].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold SHADOW_OFF in Hlo, Hhi. rewrite forallb_forall in Hb, Hw.
pose proof (Nat.Div0.mul_div_le (length hb) 8) as LD.
unfold region_ok, shz. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_map. apply Forall_forall. intros k Hk. apply in_seq in Hk.
specialize (Hw k ltac:(apply in_seq; lia)). apply andb_prop in Hw as [Hw Hw2]. apply andb_prop in Hw as [Hw Hw1].
apply Z.leb_le in Hw1. apply Z.ltb_lt in Hw2. rewrite forallb_forall in Hw.
apply (chunk_ok_val tfibsegs E _ 0 (lo + 8 * Z.of_nat k) 8 (SLit (hw hb k)) (hw hb k)); [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | change (Z.of_N 8) with 8; lia |].
intros kk Hkk. change (N.to_nat 8) with 8%nat in *.
specialize (Hw kk ltac:(apply in_seq; lia)). apply Z.eqb_eq in Hw. rewrite Hw.
specialize (Hb (8 * k + kk)%nat ltac:(apply in_seq; lia)).
replace (0 + (lo + 8 * Z.of_nat k) + Z.of_nat kk) with (lo + Z.of_nat (8 * k + kk)) by lia.
exact (hb_byte ly S U W mem md _ _ HAR Hb).
Qed.
End e.
