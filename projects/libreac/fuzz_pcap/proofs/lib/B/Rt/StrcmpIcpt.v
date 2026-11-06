From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build. *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane): asan-ubsan twin of lib/A/Rt/StrcmpIcpt.v (a working branch
   38a189401aa; it differs from the first copy's 4076c51a596 only at its line 339, the img_ro_chunks piece, which
   this file replaces with the asan-ubsan chunk): the same proof, Requires lib.A.A<n> -> lib.Reusable.Y<n> and lib.A.Rt -> lib.B.Rt, and 37 image
   numerals relocated by symbol + offset, each containing symbol pair VERIFIED equal on the pinned images (code:
   same size and mnemonic + register sequence; data: equal bytes). Table and method:
   pcap-btwin-strcmp.md (sha256 8aa32cf20eb0; internal record). Not relocated (not addresses): the instruction words
   0x63603 / 0x6b683 / 0x73703 / 0x81010113 / 0x5c40006f / 0xff010113 (the same words at the same offsets in
   asan-ubsan), the shadow constants and byte masks. *)
(* The walk of the strcmp interceptor at the one call site of the reach, in cgif_file's interceptor-contract
   vocabulary: the literal-instance form of A/AE2j.v (tfib_strchr_lit) over the symbolic-run phases of A/AE2s.v
   (mc_phase) and the shadow-word loads of A/AE6z.v (icpt_ld8, hull_rdword, ra_last).
   Proves A/Rt/StrcmpDef.v's astrcmp_lit_realizes, statement unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE2y YE3i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN32 YG0q YN01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Rt Require Import StrcmpDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* One read-only slice of the loaded image, as A/AE2h.v's img_piece / img_piece_ok (same statements). *)
Definition img_piece (a n : Z) : YP09.region := YP09.mkRegion None a (a + n) a a [YP09.mkChunk a (CImg n)].
Lemma img_piece_ok : forall (m : word -> option byte) E a0 n0 a n,
ro_img m -> In (YP09.mkChunk a0 (CImg n0)) img_ro_chunks -> a0 <= a -> 0 <= n -> a + n <= a0 + n0 ->
region_ok tfibsegs E m (img_piece a n).
Proof.
intros m E a0 n0 a n Hro Hin Hlo Hn Hhi.
pose proof (Hro E) as (B0 & B1 & _ & HCS). unfold img_ro_region in B0, B1, HCS.
cbn [YP09.r_chunks YP09.r_base YP09.r_lo YP09.r_hi base_val] in B0, B1, HCS.
pose proof (proj1 (Forall_forall _ _) HCS _ Hin) as HC.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside _ Hin) as (I0 & I1 & _).
cbn [YP09.c_off c_len cv_len YP09.c_val] in I0, I1.
unfold img_piece, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold IMG_RO_LO, IMG_RO_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
specialize (HC (a - a0 + i)). cbn [YP09.c_off YP09.c_val c_len cv_len] in HC.
destruct (HC ltac:(lia)) as (bb & Hc & Hm). exists bb. rewrite !Z.add_0_l in *. cbn [cbyte] in Hc |- *.
replace (a + i) with (a0 + (a - a0 + i)) by lia. exact (conj Hc Hm).
Qed.

(* The code of the walk, MEASURED on fuzz_pcap.asan v1.9.0 (unstripped twin, sha256 36da3052...):
   __sanitizer_weak_hook_strcmp 0x41b74 (4 B, one `ret`) and ___interceptor_strcmp 0x41b78 (1328 B, 332 insns),
   i.e. 333 four-byte words from 0x41b74. tbl_icpt already holds the trampoline 0x415b4 (range 0x415ac, 38) and
   the callee __asan::TryAsanInitFromRtl 0x598e4 (range 0x598e4, 40). *)
Definition scmp_ranges : list (Z * nat) := [((symaddr Symbols.AsanUbsan.s___sanitizer_weak_hook_strcmp), (symwords Symbols.AsanUbsan.s___sanitizer_weak_hook_strcmp (Symbols.AsanUbsan.s____interceptor_strcmp + 0x530)%Z))].
Definition tbl_sc : ctable := Eval vm_compute in build_ranges scmp_ranges tbl_icpt.
Lemma tbl_sc_eq : tbl_sc = build_ranges scmp_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_sc). Qed.
Lemma tbl_sc_ok : table_ok tfibsegs tbl_sc.
Proof.
rewrite tbl_sc_eq. apply build_ranges_ok; [| apply tbl_icpt_ok].
unfold scmp_ranges. repeat constructor; cbn; discriminate.
Qed.
Lemma tbl_sc_probe :
clookup tbl_sc (symaddr Symbols.AsanUbsan.s___wrap_strcmp) = Some 0x5c40006f /\ clookup tbl_sc (symaddr Symbols.AsanUbsan.s___interceptor_strcmp) = Some 0x81010113 /\
clookup tbl_sc (symaddr Symbols.AsanUbsan.s__ZN6__asan18TryAsanInitFromRtlEv) = Some 0xff010113 /\ clookup tbl_sc (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x198)%Z) = Some RET_WORD_r /\ clookup tbl_sc (symaddr Symbols.AsanUbsan.s_bcmp) = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sc_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_sc FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_sc tbl_sc_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
(* YE2y.icpt_ld8 over tbl_sc: one `ld rd, 0(rs)` whose address is a literal outside every symbolic region. *)
Lemma sc_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_sc (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_sc_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (YE2y.val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* Frame: 0x7f0 + 0xa0 = 2192 B for the interceptor, 16 B more for TryAsanInitFromRtl; the weak hook adds none
   (one `ret`). SM_SCR = 2208 <= ESTACK (MEASURED: `addi sp,sp,-2032` 0x41b78, `addi sp,sp,-160` 0x41bb4,
   `addi sp,sp,-16` 0x598e4). SM_RETPC 0x41d10 is the `ret`. *)
Definition SM_SCR : Z := 2208.
Definition SM_RETPC : Z := (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x198)%Z).
(* The shadow word of the literal: shadow_addr 0x20d00 = 0x7fff8000 + 0x20d00 / 8 = 0x7fffc1a0, and
   shadow_addr (0x20d00 + 13 - 1) = 0x7fffc1a1, so both granules are in the one aligned 8-byte word at A_SH. *)
Definition A_SH : Z := 0x7fffc1a0.
(* The runtime cells the walk reads, all at addresses MEASURED on fuzz_pcap.asan v1.9.0. The proof takes their
   values from AF0m's Tfib_const (the AR const law). The two .got cells hold the same values in the image; the
   .bss cells (asan_inited, the shadow base, the flags block) are zero in the image, so their values are
   start-up state:
   - 0xa2498 __asan::asan_inited = 1, read by TryAsanInitFromRtl (`lb` 0x598f8, address from `auipc` 0x598f0);
   - 0x996e8 (.got) = 0x1332e8 __sanitizer::common_flags_dont_use, read at 0x41bf4; image value, same in AF0m;
   - 0x996f8 (.got) = 0xa17b8 __asan_shadow_memory_dynamic_address, read at 0x41c28 / 0x41c78; image, same in AF0m;
   - 0xa17b8 = 0x7fff8000 (= SHADOW_OFF), the shadow base read at 0x41c30 / 0x41c80;
   - common_flags + 0xfa = 0x1333e2 intercept_strcmp, read at 0x41bfc: byte 2 of AF0m's 0x1333e0 word
     0x0101010101010101 = 1, so the interceptor does check the ranges;
   - common_flags + 0xf5 = 0x1333dd strict_string_checks, read at 0x41c04 / 0x41c60: byte 5 of AF0m's 0x1333d8
     word 0x0101000100000000 = 0, so internal_strlen (0x63db4) is not called.
   The two common_flags cells are declared as the 8-byte words AF0m holds, so the walk depends on bytes
   0xf0..0xff of the flags block. *)
Definition sm_const : list (Z * Z * list (Z * N * Z)) :=
[ ((symaddr Symbols.AsanUbsan.s__ZN6__asanL11asan_initedE), 1, [(0, 1%N, 1)]); ((symaddr (Symbols.AsanUbsan.Sec.s_got + 0x50)%Z), 8, [(0, 8%N, (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE))]); ((symaddr (Symbols.AsanUbsan.Sec.s_got + 0x60)%Z), 8, [(0, 8%N, (symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address))]);
((symaddr Symbols.AsanUbsan.s___asan_shadow_memory_dynamic_address), 8, [(0, 8%N, 0x7fff8000)]); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE + 0xf0)%Z), 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)]) ].
Lemma sm_const_chk : forall ly, rodata_chk ly sm_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition shR : YP09.region :=
YP09.mkRegion None A_SH (A_SH + 2) A_SH A_SH [YP09.mkChunk A_SH (CVal 1 (SLit 0)); YP09.mkChunk (A_SH + 1) (CVal 1 (SOff 32 0))].
Definition stkS : YP09.region := YP09.mkRegion (Some 2%nat) (- SM_SCR) 0 (- SM_SCR) 0 [].
Definition memS : smem := [stkS; img_piece A_FUZZ_PATH 13; shR] ++ map ro_region sm_const.
Definition ssS : sstate := mkSS SM_ENTRY (sr_set (sr_set sr_atoms 10%bv (SLit A_FUZZ_PATH)) 11%bv (SLit A_FUZZ_PATH)) memS None
  (mkFacts [(2%nat, mkAF (2^44) (2^47) 4); (32%nat, mkAF 0 7 0)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sc FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition shapeS (ss : sstate) : bool :=
(ss_pc ss =? SM_RETPC) && match ss_resv ss with None => true | _ => false end &&
reg_is ss 10 (SLit 0) && reg_is ss 1 (SOff 1 0) &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - SM_SCR) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
(* The symbolic run. Atom 32 = the last shadow byte of the literal, atom 33 = the shadow word at A_SH.
   The two `ld` pairs (0x41c50/0x41c54 for a0, 0x41ca0/0x41ca4 for a1) read A_SH, which is in no region, so the
   runner stops with SR_load and sc_ld8 takes the step. *)
Definition e0 : sstate := Eval vm_compute in fst (RUN ssS).
Definition e1s : sstate := Eval vm_compute in set_regs_pc (set_regs_pc e0 [((13%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xdc)%Z)) [((14%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xe0)%Z).
Definition e1 : sstate := Eval vm_compute in fst (RUN e1s).
Definition z0 : sstate := Eval vm_compute in fst (RUN (AC e1 BC_EQ (RG e1 13) (SLit 0))).
Definition z1s : sstate := Eval vm_compute in set_regs_pc (set_regs_pc z0 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) [((13%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x130)%Z).
Definition z1 : sstate := Eval vm_compute in fst (RUN z1s).
Definition n0 : sstate := Eval vm_compute in fst (RUN (AC e1 BC_NE (RG e1 13) (SLit 0))).
Definition n1 : sstate := Eval vm_compute in fst (RUN (AC n0 BC_EQ (RG n0 10) (SLit 0))).
Definition n2s : sstate := Eval vm_compute in set_regs_pc (set_regs_pc n1 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) [((13%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x130)%Z).
Definition n2 : sstate := Eval vm_compute in fst (RUN n2s).
Lemma r_e0 : RUN ssS = (e0, RS_stopped (SR_load None A_SH)). Proof. vm_compute. reflexivity. Qed.
Lemma r_e1 : RUN e1s = (e1, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 33 0) (SOff 33 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_z0 : RUN (AC e1 BC_EQ (RG e1 13) (SLit 0)) = (z0, RS_stopped (SR_load None A_SH)). Proof. vm_compute. reflexivity. Qed.
Lemma r_z1 : RUN z1s = (z1, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition QC : sv :=
SAlu ALU_AND (SAlu ALU_OR (SLit 0) (SAlu ALU_AND (SAlu ALU_SLTU (SLit 0) (SOff 32 0))
  (SAlu ALU_XOR (SAlu ALU_SLT (SLit 4) (SOff 32 0)) (SLit 1)))) (SLit 255).
Lemma r_n0 : RUN (AC e1 BC_NE (RG e1 13) (SLit 0)) = (n0, RS_stopped (SR_branch BC_EQ QC (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_n1 : RUN (AC n0 BC_EQ (RG n0 10) (SLit 0)) = (n1, RS_stopped (SR_load None A_SH)). Proof. vm_compute. reflexivity. Qed.
Lemma r_n2 : RUN n2s = (n2, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma shape_z1 : shapeS z1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma shape_n2 : shapeS n2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma pc_e0 : ss_pc e0 = (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xd8)%Z). Proof. vm_compute. reflexivity. Qed.
(* The quick check of ASan's ACCESS_MEMORY_RANGE on the last granule: with the shadow byte b1 of the last
   address of the literal, `saddr_ok (x + n - 1) b1` makes the flag zero, so the walk does not call
   __asan_region_is_poisoned (its `jal 0x54450` at 0x41ebc / 0x41f9c is not reached). *)
Lemma qc_zero : forall E b1, ew E 32 = Z_to_bv 64 b1 -> saddr_ok (A_FUZZ_PATH + 13 - 1) b1 -> 0 <= b1 < 8 ->
branch_taken BC_EQ (sv_denot E QC) (sv_denot E (SLit 0)) = true.
Proof.
intros E b1 Hb Hok Hr. unfold saddr_ok, A_FUZZ_PATH in Hok.
change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) + 13 - 1) mod 8) with 4 in Hok.
assert (Hc : b1 = 0 \/ b1 = 5 \/ b1 = 6 \/ b1 = 7) by lia. clear Hok Hr.
unfold QC, branch_taken. cbn [sv_denot]. rewrite Hb.
destruct Hc as [E1 | [E1 | [E1 | E1]]]; subst b1; vm_compute; reflexivity.
Qed.
(* shadow_addr is `simpl never`; these are the two concrete bounds hull_rdword needs. *)
Lemma sh_lo : shadow_addr A_FUZZ_PATH / 8 * 8 = A_SH.
Proof. unfold shadow_addr, SHADOW_OFF, A_FUZZ_PATH, A_SH. vm_compute. reflexivity. Qed.
Lemma sh_hi : shadow_addr (A_FUZZ_PATH + 13 - 1) / 8 * 8 = A_SH.
Proof. unfold shadow_addr, SHADOW_OFF, A_FUZZ_PATH, A_SH. vm_compute. reflexivity. Qed.
Lemma sh_last : SB + (A_FUZZ_PATH + 13 - 1) / 8 = A_SH + 1.
Proof. unfold SB, A_FUZZ_PATH, A_SH. vm_compute. reflexivity. Qed.
Lemma sh_first : SB + 0x41a0 = A_SH.
Proof. unfold SB, A_SH. vm_compute. reflexivity. Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
(* Both paths end at SM_RETPC with shapeS; this closes either one. *)
Lemma sm_finish : forall ly S (W : world tfibsegs) regs mem md E ss ms md',
shapeS ss = true -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
env_agree 32 (YE2y.Env regs []) E ->
YK0s.ret_ok (getr regs 1) ->
(forall a, spZ regs - SM_SCR <= a < spZ regs -> apresent (w_H W) mem a) ->
ly_stk_lo ly + ESTACK <= spZ regs -> spZ regs <= ly_stk_hi ly ->
AR tfibsegs B ly S W mem md ->
same_but_materialized md md' ->
bv_unsigned (ew E 2) = spZ regs ->
(forall z : word, ~ (spZ regs - SM_SCR <= bv_unsigned z < spZ regs) -> ms_mem ms z = mem z) ->
SRr tfibsegs W (mkCfg ms md') (astrcmp_post B ly S W regs mem md 0).
Proof.
intros ly S W regs mem md E ss ms md' Hsh HS HEA Hra HpresE Hslo Htop HAR Hsbm EE2 MEQ.
pose proof YF0x.Hwx_tfa as Hwx.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ESTACK in Hslo.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
unfold shapeS in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HCS].
apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Hrv].
apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv ss = None) by (destruct (ss_resv ss); [discriminate | reflexivity]).
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold SM_SCR in W0b, W0c.
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
  apply (YF0x.st_ok_reg_denot H E ss ms r HS). }
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r).
{ intros i r Hi. destruct HEA as [HA _].
  assert (Hlt : (i < 32)%nat) by (pose proof (bv_unsigned_in_range 5 r); unfold bv_modulus in *; cbn in *; lia).
  rewrite (HA i Hlt). apply YE2y.Env_reg. exact Hi. }
assert (P1 : getr (ms_regs ms) 1 = getr regs 1)
  by (rewrite (RD 1%bv (SOff 1 0) R1); cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SM_SCR <= a < sp0) -> aview tfibsegs H (ms_mem ms) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply YF0x.aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - SM_SCR <= a < sp0 -> apresent H (ms_mem ms) a).
{ intros a Ha.
  assert (HN : nth_error (ss_mem ss) 0%nat = Some r0) by (rewrite Hmem; reflexivity).
  assert (HB : base_val E (YP09.r_base r0) + YP09.r_wlo r0 <= a < base_val E (YP09.r_base r0) + YP09.r_whi r0).
  { rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. unfold SM_SCR in Ha. lia. }
  assert (HT : YF0x.TFIB_IMG_END <= a < 2 ^ 64)
    by (unfold YF0x.TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP; unfold SM_SCR in Ha; lia).
  exact (YF0x.st_ok_window_apresent H E ss ms 0%nat r0 a HS HN HB HT). }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms) a).
{ intros a Hp. rewrite (YE2y.apresent_mod _ (ms_mem ms) a). rewrite (YE2y.apresent_mod _ mem a) in Hp.
  assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
  destruct (Z_lt_le_dec a' (sp0 - SM_SCR)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
  (apply (YF0x.apresent_same H mem (ms_mem ms) a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
eapply (SRr_ret_at tfibsegs tbl_sc tbl_sc_ok Hwx W E); [exact HS | exact Hresv | rewrite Hpc; vm_compute; reflexivity |].
intros mat'.
assert (HARf : AR tfibsegs B ly S W (ms_mem ms) (with_vm_backing (m_vm_lazy md') mat' md')).
{ pose proof (same_but_materialized_trans md md' _ Hsbm (with_vm_backing_same md' mat')) as SBM.
  pose proof (same_but_materialized_frame _ _ SBM) as MF.
  apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms) _ HAR).
  + intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs.
    exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold ESTACK, SM_SCR, sp0 in *; lia) Hown).
  + intros a Hv. rewrite (YE2y.aview_mod _ (ms_mem ms) a). rewrite (YE2y.aview_mod _ mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
    destruct (Z_lt_le_dec a' (sp0 - SM_SCR)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
    destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
    apply YE2y.aview_some_of_apresent. apply PRS1. lia.
  + apply MF. + apply MF. + apply MF.
  + exact (YE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ HpresE ltac:(unfold sp0, SM_SCR in *; lia) ltac:(lia)). }
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md') mat' md').
split; [unfold cfg_at; rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [exact HARf|].
split; [exact (YE2y.aregs_preserved_of_st_ok H E ss ms regs [] HS HEA HCS)|].
split; [eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same]|].
split; [rewrite (RD 10%bv (SLit 0) R10); reflexivity|].
split; [intros a Hr Ha; apply AV1; [exact Hr | unfold ESTACK, SM_SCR, sp0 in *; lia] | exact PM1].
Qed.

Lemma strcmp_walk : forall ly S (W : world tfibsegs) regs mem md,
ecall_pre tfibsegs B ly S W regs mem md ->
getr regs 10 = w64 A_FUZZ_PATH -> getr regs 11 = w64 A_FUZZ_PATH ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF A_FUZZ_PATH 13 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) A_FUZZ_PATH 13 ->
SRr tfibsegs W (cfg_at tfibsegs SM_ENTRY regs mem md) (astrcmp_post B ly S W regs mem md 0).
Proof.
intros ly S W regs mem md HPRE G10 G11 HIMG HRA HHULL.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ESTACK in Hslo, HpresE.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
assert (HpresW : forall a, sp0 - SM_SCR <= a < sp0 -> apresent H mem a) by (intros a Ha; apply HpresE; unfold SM_SCR in Ha; lia).
(* the two shadow bytes of the literal *)
pose proof (YE2y.ra_granule_zero (aview tfibsegs H mem) A_FUZZ_PATH 13 0x41a0 HRA ltac:(unfold A_FUZZ_PATH; lia) ltac:(unfold A_FUZZ_PATH; lia)) as Hb0.
rewrite sh_first in Hb0.
destruct (YE2y.ra_last (aview tfibsegs H mem) A_FUZZ_PATH 13 HRA ltac:(lia)) as (b1 & Hb1 & Hok).
rewrite sh_last in Hb1.
assert (Hb8 : 0 <= b1 < 8).
{ destruct Hok as [-> | [Hlt Hb]]; [lia|]. unfold A_FUZZ_PATH in Hlt. change (((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68128)%Z) + 13 - 1) mod 8) with 4 in Hlt. lia. }
destruct (YE2y.hull_rdword H mem A_FUZZ_PATH 13 A_SH HHULL ltac:(rewrite sh_lo; lia) ltac:(rewrite sh_hi; lia)) as (q & Hq & Rq).
set (EE := YE2y.Env regs [b1; q]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew EE 32 = Z_to_bv 64 b1) by (apply (YE2y.Env_x _ _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 q) by (apply (YE2y.Env_x _ _ 1); reflexivity).
assert (HEA : env_agree 32 (YE2y.Env regs []) EE).
{ split; [|reflexivity]. intros n Hn. unfold EE, YE2y.Env. rewrite !ew_Ereg_nat with (r := Z_to_bv 5 (Z.of_nat n));
  try (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). reflexivity. }
unfold cfg_at. change (w64 SM_ENTRY) with (Z_to_bv 64 SM_ENTRY).
assert (HS0 : st_ok tfibsegs EE ssS (restrict H (mkst regs (Z_to_bv 64 SM_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssS.
apply (st_ok_pin_reg EE (mkSS SM_ENTRY (sr_set sr_atoms 10%bv (SLit A_FUZZ_PATH)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4); (32%nat, mkAF 0 7 0)] [] [])) _ 11%bv (SLit A_FUZZ_PATH));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
apply (st_ok_pin_reg EE (mkSS SM_ENTRY sr_atoms memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4); (32%nat, mkAF 0 7 0)] [] [])) _ 10%bv (SLit A_FUZZ_PATH));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
rewrite restrict_mkst_fx. unfold EE, YE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [b1; q])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memS. apply Forall_cons.
{ unfold stkS, SM_SCR. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2208)); [exact EE2 | lia | lia |].
  intros a Ha. apply YE2y.apresent_writable. apply HpresW. unfold SM_SCR. lia. }
(* asan-ubsan: the img_ro_chunks piece around the literal is Reusable/YE3i.v:34 (a working branch
   0ee17446f70) `mkChunk 0x20a84 (CImg (0x20d0d - 0x20a84))`, which ends exactly at the literal's NUL (0x20d00 + 13 =
   0x20d0d). The asan file's 0x20b80 / 0x20e0d is the asan image's chunk and does not exist in asan-ubsan. *)
apply Forall_cons; [apply (img_piece_ok _ EE (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68141)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z))); [exact HIMG | unfold img_ro_chunks; cbn; tauto | unfold A_FUZZ_PATH; lia | lia | unfold A_FUZZ_PATH; lia]|].
apply Forall_cons.
{ unfold shR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold A_SH; lia|]. split; [unfold A_SH; lia|]. split; [intros o Ho; exfalso; lia|].
  apply Forall_cons.
  { eapply (chunk_ok_val tfibsegs EE _ 0 A_SH 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_l. apply YE2y.val_mem1_of_aview. exact Hb0. }
  apply Forall_cons; [|apply Forall_nil].
  eapply (chunk_ok_val tfibsegs EE _ 0 (A_SH + 1) 1%N (SOff 32 0) b1);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_l. apply YE2y.val_mem1_of_aview. exact Hb1. }
exact (YE2y.rodata_ok B TB sm_const ly S H mem EE (sm_const_chk ly) (proj1 HAR)).
- apply pairwise_disjoint_of_extents. unfold memS, stkS, shR, img_piece, sm_const, ro_region, extent_of_region, A_SH, A_FUZZ_PATH, SM_SCR.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, E32, unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | apply Z.mod_1_r | lia]. }
(* phase 1: entry .. the first shadow load *)
eapply SRr_bind; [exact (sc_phase W EE ssS e0 _ _ md HS0 r_e0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
  unshelve epose proof (in_wrange_single_b EE memS (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X;
  [vm_compute; reflexivity|]. lia. }
clear HF1 HFr1.
assert (HW : forall (mm : machine_state), (forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem mm z = mem z) ->
  rdword (aview tfibsegs H (ms_mem mm)) A_SH = Some (bv_unsigned (ew EE 33))).
{ intros mm Hm. rewrite E33, unsigned_lit_small by lia. apply (YF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq].
  intros i Hi. apply YF0x.aview_same. apply Hm. rewrite unsigned_lit_small by (unfold A_SH; lia). unfold A_SH, SM_SCR. lia. }
(* the two `ld` of the first range check: 0x41c50 (a3) and 0x41c54 (a4) *)
eapply SRr_bind; [apply (sc_ld8 W EE e0 ms1 _ 13%bv 13%bv 0x0006b683 A_SH 33 34 HS1 eq_refl
  ltac:(vm_compute; reflexivity) ltac:(rewrite pc_e0; vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
  ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms1 MEQ1))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HM2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z) by (intros z Hz; rewrite HM2; apply MEQ1; exact Hz).
rewrite pc_e0 in HS2.
eapply SRr_bind; [apply (sc_ld8 W EE (set_regs_pc e0 [((13%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xdc)%Z)) ms2 _ 14%bv 14%bv 0x00073703 A_SH 33 34 HS2 eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
  ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms2 MEQ2))|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HM3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z) by (intros z Hz; rewrite HM3; apply MEQ2; exact Hz).
change (set_regs_pc (set_regs_pc e0 [((13%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xdc)%Z)) [((14%bv : bv 5), SOff 33 0)] ((symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0xdc)%Z) + 4)) with e1s in HS3.
eapply SRr_bind; [exact (sc_phase W EE e1s e1 _ _ _ HS3 r_e1)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; exact Hz|]. intros Hin.
  unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
clear HF4 HFr4.
pose proof (YE2y.br_hull EE 33 33 q q E33 E33 Rq Rq) as Hbr.
destruct (Z.eq_dec (Z.lor q q) 0) as [Hz|Hz].
- (* the quick check passes: no call to __asan_region_is_poisoned *)
  pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG e1 13) (SLit 0) HS4
    (eq_trans Hbr (f_equal negb (proj2 (Z.eqb_eq _ _) Hz)))) as HS4'.
  change (neg_bc BC_NE) with BC_EQ in HS4'.
  eapply SRr_bind; [exact (sc_phase W EE _ z0 _ _ _ HS4' r_z0)|].
  cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
  assert (MEQ5 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
  { intros z Hz'. rewrite (HF5 z); [apply MEQ4; exact Hz'|]. intros Hin.
    unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
  clear HF5 HFr5.
  eapply SRr_bind; [apply (sc_ld8 W EE z0 ms5 _ 12%bv 12%bv 0x00063603 A_SH 33 34 HS5 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
    ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms5 MEQ5))|].
  cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HM6). rewrite ?wvb_wvb in *.
  assert (MEQ6 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z) by (intros z Hz'; rewrite HM6; apply MEQ5; exact Hz').
  eapply SRr_bind; [apply (sc_ld8 W EE (set_regs_pc z0 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) ms6 _ 13%bv 13%bv 0x0006b683 A_SH 33 34 HS6 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
    ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms6 MEQ6))|].
  cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7). rewrite ?wvb_wvb in *.
  assert (MEQ7 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z) by (intros z Hz'; rewrite HM7; apply MEQ6; exact Hz').
  change (set_regs_pc (set_regs_pc z0 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) [((13%bv : bv 5), SOff 33 0)] ((symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z) + 4)) with z1s in HS7.
  eapply SRr_bind; [exact (sc_phase W EE z1s z1 _ _ _ HS7 r_z1)|].
  cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
  assert (MEQ8 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
  { intros z Hz'. rewrite (HF8 z); [apply MEQ7; exact Hz'|]. intros Hin.
    unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
  clear HF8 HFr8.
  exact (sm_finish ly S W regs mem md EE z1 ms8 _ shape_z1 HS8 HEA Hra HpresW Hslo Htop HAR
    (with_vm_backing_same md mat8) EE2 MEQ8).
- (* the quick check fails: the walk reads the last granule byte and finds the range addressable *)
  pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG e1 13) (SLit 0) HS4
    (eq_trans Hbr (f_equal negb (proj2 (Z.eqb_neq _ _) Hz)))) as HS4'.
  eapply SRr_bind; [exact (sc_phase W EE _ n0 _ _ _ HS4' r_n0)|].
  cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
  assert (MEQ5 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
  { intros z Hz'. rewrite (HF5 z); [apply MEQ4; exact Hz'|]. intros Hin.
    unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
  clear HF5 HFr5.
  pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG n0 10) (SLit 0) HS5 (qc_zero EE b1 E32 Hok Hb8)) as HS5'.
  eapply SRr_bind; [exact (sc_phase W EE _ n1 _ _ _ HS5' r_n1)|].
  cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
  assert (MEQ6 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
  { intros z Hz'. rewrite (HF6 z); [apply MEQ5; exact Hz'|]. intros Hin.
    unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
  clear HF6 HFr6.
  eapply SRr_bind; [apply (sc_ld8 W EE n1 ms6 _ 12%bv 12%bv 0x00063603 A_SH 33 34 HS6 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
    ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms6 MEQ6))|].
  cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7). rewrite ?wvb_wvb in *.
  assert (MEQ7 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z) by (intros z Hz'; rewrite HM7; apply MEQ6; exact Hz').
  eapply SRr_bind; [apply (sc_ld8 W EE (set_regs_pc n1 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) ms7 _ 13%bv 13%bv 0x0006b683 A_SH 33 34 HS7 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) ltac:(vm_refl_bv)
    ltac:(vm_refl_bv) ltac:(unfold A_SH; lia) ltac:(unfold A_SH; lia) (HW ms7 MEQ7))|].
  cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8). rewrite ?wvb_wvb in *.
  assert (MEQ8 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z) by (intros z Hz'; rewrite HM8; apply MEQ7; exact Hz').
  change (set_regs_pc (set_regs_pc n1 [((12%bv : bv 5), SOff 33 0)] (symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z)) [((13%bv : bv 5), SOff 33 0)] ((symaddr (Symbols.AsanUbsan.s___interceptor_strcmp + 0x12c)%Z) + 4)) with n2s in HS8.
  eapply SRr_bind; [exact (sc_phase W EE n2s n2 _ _ _ HS8 r_n2)|].
  cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
  assert (MEQ9 : forall z : word, ~ (sp0 - SM_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
  { intros z Hz'. rewrite (HF9 z); [apply MEQ8; exact Hz'|]. intros Hin.
    unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SM_SCR) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. lia. }
  clear HF9 HFr9.
  exact (sm_finish ly S W regs mem md EE n2 ms9 _ shape_n2 HS9 HEA Hra HpresW Hslo Htop HAR
    (with_vm_backing_same md mat9) EE2 MEQ9).
Qed.
End d.
(* The contract of A/Rt/StrcmpDef.v, statement unchanged. *)
Theorem strcmp_lit_contract : forall B, AR_laws tfibsegs B -> PcapSyms B -> astrcmp_lit_realizes B.
Proof.
intros B LAWS TB x y res Hin ly S W regs mem md HPRE G10 G11 HIMG HRAx HHx HRAy HHy.
unfold SM_INST in Hin. cbn [In] in Hin. destruct Hin as [E|[]]. injection E as <- <- <-.
cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HRAx, HHx.
change (Z.of_nat (length FUZZ_PATH_BYTES) + 1) with 13 in HRAx, HHx.
exact (strcmp_walk B LAWS TB ly S W regs mem md HPRE G10 G11 HIMG HRAx HHx).
Qed.
End b.
