(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Rt/Strcmp.v (donor image sha256 c2c7559b29bd), with its module paths changed, names GrantSyms -> TfibSyms and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/Rt/Strcmp.v (donor image sha256 64b53ff86172), with its module paths changed, names AB1v -> YB1v, AE34 -> YE34, AF0l -> YF0l, AF0m -> YF0m, AF0x -> YF0x, AB1w -> YB1w, AE20 -> YE20, AE2y -> YE2y and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Read from: fuzz_state.asan-ubsan (omx-clap-core/fuzz_state asan-ubsan) sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204; unstripped twin sha256 b1566a1ca816049d20588a70b9b43f152a338319c8ebea649df5b62ff5c4cc00 *)
(* Modified by Theorem Labs, 2026-10: image B. The donor measured this walk on fuzz_grant.asan.debug; a Theorem Labs lane
   moved it to fuzz_state.asan (lib/A/Rt at 812b439a657) and port_core.py 718254b3f4dd moved it from there to
   fuzz_state.asan-ubsan: every address below is fuzz_state.asan-ubsan's, checked against this image's bytes, and
   the image modules are lib/B's twins of lib/A's (YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y). *)
(* Written by Theorem Labs, 2026-10, for libreac/fuzz_grant's ASan build (image A): the shared-core contract of the
   ASan strcmp interceptor, Reusable/AStrcmpDef.v's astrcmp_realizes, for ___interceptor_strcmp (0x42c80) and for the
   one-instruction trampoline __interceptor_trampoline_strcmp = __wrap_strcmp (0x426cc, `j 0x42c80`). The walk is the
   step order of A/AE2s.v (the bcmp interceptor) in the cgif_file core form, MEASURED on fuzz_grant.asan.debug with
   elfdis.py; the phases are:
   1. entry (symbolic run, this file): [0x426cc `j` ->] prologue 0x42c80 (frame 0x7f0 + 0xa0 = 2192 B, the saved ra and
      s0..s11 at sp - 8 .. sp - 104), __asan::TryAsanInitFromRtl 0x5a0e8 (asan_inited = 1, B/YE2y.icpt_rodata), then
      s2 = x, s1 = y, s4 = 0 at the loop head 0x42ce0; the stack window is [sp - 2208, sp);
   2. the byte loop 0x42ce0..0x42cf8 (StrcmpLoop.strcmp_loop, a plain machine walk): leaves at 0x42cfc with
      s4 = k + 1, s9 = x[k], s10 = y[k];
   3. the s1 range check 0x42cfc -> 0x42d68 (StrcmpChkX.scx_check_srr, A/AE6z.v form) on [x, x + k + 1);
   4. the s2 range check 0x42d68 -> 0x42db8 (StrcmpChkY.scy_check_srr) on [y, y + k + 1);
   5. the tail 0x42db8 (symbolic run, this file): s4 = (s10 <u s9) - (s9 <u s10), the call of the empty weak hook
      __sanitizer_weak_hook_strcmp 0x42c7c, a0 = s4, the epilogue and `ret`.
   The checks use the callee stack [sp - 2192 - 72, sp - 2192), so the walk writes only [sp - 2264, sp). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 AStrcmpDef.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Rt Require Import StrcmpTbl StrcmpLoop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Rt Require StrcmpChkX StrcmpChkY.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition STRCMP_TRAMP : Z := 0x426cc.   (* __wrap_strcmp = __interceptor_trampoline_strcmp, 4 bytes: j 0x42c80 *)
Definition STRCMP_ICPT : Z := 0x42c80.    (* ___interceptor_strcmp, 1328 bytes, 332 insns *)
Definition SC_WIN : Z := 2208.
Definition SC_FRAME : Z := 2192.
Definition SC_SCR : Z := 2264.
Definition SC_TAIL : Z := 0x42db8.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_sc FUEL s.
Definition RUNTOL (s : sstate) := sym_run_toN tfibsegs tbl_sc FUEL SL_HEAD s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
(* Phase 1: the entry, from either entry point to the loop head. *)
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- SC_WIN) 0 (- SC_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4)].
Definition ssA (pc0 : Z) : sstate := mkSS pc0 sr_atoms (stkA :: map ro_region icpt_rodata) None (mkFacts factsA [] []).
Definition eA : sstate := Eval vm_compute in fst (RUNTOL (ssA STRCMP_ICPT)).
Lemma r_A_icpt : RUNTOL (ssA STRCMP_ICPT) = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma r_A_tramp : RUNTOL (ssA STRCMP_TRAMP) = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition SAVEDA : list (sv * Z) :=
[(SOff 1 0, -8); (SOff 8 0, -16); (SOff 9 0, -24); (SOff 18 0, -32); (SOff 19 0, -40); (SOff 20 0, -48); (SOff 21 0, -56);
(SOff 22 0, -64); (SOff 23 0, -72); (SOff 24 0, -80); (SOff 25 0, -88); (SOff 26 0, -96); (SOff 27 0, -104)].
Definition KEPTA : list Z := [3; 4; 21; 22; 23; 24; 25; 26].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? SL_HEAD) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - SC_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 18 (SOff 10 0) && reg_is ss 9 (SOff 11 0) && reg_is ss 20 (SLit 0) && reg_is ss 2 (SOff 2 (- SC_FRAME)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (fst p)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
(* Phase 5: the tail, from 0x42db8 to the `ret` at 0x42e18, the saved registers read from the frame. *)
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2184 (CVal 8 (SOff 32 0)); YP09.mkChunk 2176 (CVal 8 (SOff 33 0)); YP09.mkChunk 2168 (CVal 8 (SOff 34 0));
YP09.mkChunk 2160 (CVal 8 (SOff 35 0)); YP09.mkChunk 2152 (CVal 8 (SOff 36 0)); YP09.mkChunk 2144 (CVal 8 (SOff 37 0));
YP09.mkChunk 2136 (CVal 8 (SOff 38 0)); YP09.mkChunk 2128 (CVal 8 (SOff 39 0)); YP09.mkChunk 2120 (CVal 8 (SOff 40 0));
YP09.mkChunk 2112 (CVal 8 (SOff 41 0)); YP09.mkChunk 2104 (CVal 8 (SOff 42 0)); YP09.mkChunk 2096 (CVal 8 (SOff 43 0));
YP09.mkChunk 2088 (CVal 8 (SOff 44 0))].
Definition ss_epi : sstate := mkSS SC_TAIL sr_atoms [YP09.mkRegion (Some 2%nat) 0 SC_FRAME 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
(* The result: `sltu a0,s9,s10; sltu a1,s10,s9; sub s4,a1,a0` (0x42db8..0x42dc0), then `mv a0,s4`. *)
Definition RES : sv := SAlu ALU_ADD (SAlu ALU_SUB (SAlu ALU_SLTU (SOff 26 0) (SOff 25 0)) (SAlu ALU_SLTU (SOff 25 0) (SOff 26 0))) (SLit 0).
Lemma res_reg : sr_get (ss_regs epi_e) 10%bv = RES. Proof. vm_compute. reflexivity. Qed.
Lemma res_ok : forall E c1 c2, ew E 25 = Z_to_bv 64 c1 -> ew E 26 = Z_to_bv 64 c2 -> 0 <= c1 < 256 -> 0 <= c2 < 256 ->
sv_denot E RES = w64 (strcmp_res c1 c2).
Proof.
intros E c1 c2 H1 H2 R1 R2. change (w64 (strcmp_res c1 c2)) with (sv_denot E (SLit (strcmp_res c1 c2))). apply U_inj.
unfold RES. rewrite U_SLit, !U_SAlu, (U_atom E 25 c1 H1), (U_atom E 26 c2 H2), U_SLit by lia. cbn [zalu_raw].
unfold strcmp_res, zcanon, M64.
destruct (Z.lt_trichotomy c1 c2) as [Hlt | [<- | Hgt]].
- rewrite (proj2 (Z.ltb_ge c2 c1)) by lia. rewrite (proj2 (Z.ltb_lt c1 c2) Hlt), (proj2 (Z.eqb_neq c1 c2)) by lia. reflexivity.
- rewrite Z.ltb_irrefl, Z.eqb_refl. reflexivity.
- rewrite (proj2 (Z.ltb_lt c2 c1) Hgt), (proj2 (Z.ltb_ge c1 c2)) by lia. rewrite (proj2 (Z.eqb_neq c1 c2)) by lia. reflexivity.
Qed.
Lemma aview_rdn1 : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfibsegs H m a = Some v -> rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof.
intros H m a v Hv. apply (proj2 (rdn_mbytes tfibsegs _ 1 a [Z_to_bv 8 v])). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. cbn [nth_error].
rewrite (YF0x.aview_byte H m a v Hv). reflexivity.
Qed.
Lemma sc_tail : forall B, AR_laws tfibsegs B ->
forall ly S (W : world tfibsegs) regs mem md (regsR : bvmap 5 word) (memR : word -> option byte) mdR c1 c2,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
0 <= c1 < 256 -> 0 <= c2 < 256 ->
AR tfibsegs B ly S W memR mdR -> same_but_materialized md mdR ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) memR a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memR a) ->
getr regsR 25 = w64 c1 -> getr regsR 26 = w64 c2 ->
getr regsR 2 = w64 (spZ regs - SC_FRAME) -> getr regsR 3 = getr regs 3 -> getr regsR 4 = getr regs 4 ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 80) 8 (bv_unsigned (getr regs 24)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 88) 8 (bv_unsigned (getr regs 25)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 96) 8 (bv_unsigned (getr regs 26)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 104) 8 (bv_unsigned (getr regs 27)) ->
SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 SC_TAIL) memR (seg_rom tfibsegs)) mdR)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (strcmp_res c1 c2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS ly S W regs mem md regsR memR mdR c1 c2 HPRE Hslo2 Hc1 Hc2 HARR HsbmR AVR PMR G25 G26 G2 G3 G4
V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF0x.Hwx_tfa as Hwx. unfold ESTACK, SC_SCR, SC_FRAME in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
set (E4 := Ereg regsR [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2192).
{ subst E4. rewrite (ew_Ereg_nat regsR _ 2 2%bv eq_refl), G2. unfold w64. apply unsigned_lit_small. lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regsR (Z_to_bv 64 SC_TAIL) memR (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regsR [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok, SC_FRAME. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2192) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (rq : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rq -> Z.of_nat j < 13 ->
val_mem tfibsegs (mrestrict H memR) (sp0 - 2192 + off) 8 (bv_unsigned (getr regs rq)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H memR) (sp0 - 2192) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j rq off Hnth Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2192) off 8 _ (bv_unsigned (getr regs rq))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regsR _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs rq)). zside.
- zside.
- exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv 2184); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2184) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv 2176); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2176) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv 2168); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2168) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv 2160); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2160) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv 2152); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2152) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv 2144); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2144) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv 2136); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2136) with (sp0 - 56) by lia; exact V6].
+ apply (CK 7%nat 22%bv 2128); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2128) with (sp0 - 64) by lia; exact V7].
+ apply (CK 8%nat 23%bv 2120); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2120) with (sp0 - 72) by lia; exact V8].
+ apply (CK 9%nat 24%bv 2112); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2112) with (sp0 - 80) by lia; exact V9].
+ apply (CK 10%nat 25%bv 2104); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2104) with (sp0 - 88) by lia; exact V10].
+ apply (CK 11%nat 26%bv 2096); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2096) with (sp0 - 96) by lia; exact V11].
+ apply (CK 12%nat 27%bv 2088); [reflexivity | cbn; lia | replace (sp0 - 2192 + 2088) with (sp0 - 104) by lia; exact V12].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2192) with (spZ regs + (-137) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply SRr_bind; [apply (sc_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 cf4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_sc tbl_sc_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = memR z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23.
rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (Q10 : getr (ms_regs ms4) 10 = sv_denot E4 RES) by (rewrite (st_ok_reg_denot H E4 epi_e ms4 10%bv HS4), res_reg; reflexivity).
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regsR _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regsR rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regsR _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regsR _ 0)). rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy mdR) mat' mdR).
pose proof (same_but_materialized_frame mdR _ (with_vm_backing_same mdR mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H memR a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split]]]].
+ apply (al_frame _ _ LAWS ly S W memR mdR (ms_mem ms4) _ HARR).
* intros a Hr Hown. apply AV4.
* intros a Hv. rewrite AV4. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (YE2y.hs_kept_eq _ _ _ MEQ4).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl). exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl). exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 7%nat 22%bv eq_refl).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 8%nat 23%bv eq_refl).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24. exact (X 9%nat 24%bv eq_refl).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25. exact (X 10%nat 25%bv eq_refl).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26. exact (X 11%nat 26%bv eq_refl).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27. exact (X 12%nat 27%bv eq_refl).
+ eapply same_but_materialized_trans; [exact HsbmR | apply with_vm_backing_same].
+ rewrite Q10. apply res_ok; [rewrite (Y 25%nat 25%bv eq_refl); exact G25 | rewrite (Y 26%nat 26%bv eq_refl); exact G26 | exact Hc1 | exact Hc2].
+ intros a Hr Hs. rewrite AV4. apply AVR; [exact Hr | unfold sp0 in *; lia].
+ intros a Hp. apply (apresent_same H memR (ms_mem ms4) a (MEQ4 _)). apply PMR. exact Hp.
Qed.
(* The walk: phases 1 to 5 composed, for an entry pc0 whose run reaches the loop head in the state eA. *)
Lemma strcmp_srr : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall pc0, RUNTOL (ssA pc0) = (eA, RS_running) -> astrcmp_realizes tfibsegs B pc0.
Proof.
intros B LAWS TB pc0 RA. unfold astrcmp_realizes.
intros ly S W regs mem md x y k c1 c2 HPRE Hslo2 Hpres2 G10 G11 Hx Hy Hk32 Hxk Hyk Hmeet Hsx Hsy Hbx Hby
Hamx Hamy Hrax Hhx Hray Hhy.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE, Hbx, Hby.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof YF0x.Hwx_tfa as Hwx.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (unfold ESTACK in Hslo2; lia).
assert (Hsl2 : ly_stk_lo ly + 8192 <= sp0) by (unfold ESTACK in Hslo2; exact Hslo2).
destruct Hmeet as (Hk0 & Hbef & Hc1v & Hc2v & Hstop).
assert (Hamr : x + (k + 1) <= 2 ^ 47 - 1 /\ y + (k + 1) <= 2 ^ 47 - 1)
by (pose proof Hamx as X1; pose proof Hamy as Y1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1, Y1; lia).
destruct (aview_byte_ex H mem (x + k) c1 Hc1v) as (bc1 & _ & _ & Rc1).
destruct (aview_byte_ex H mem (y + k) c2 Hc2v) as (bc2 & _ & _ & Rc2).
assert (VT : forall (m m' : word -> option byte) a v, val_mem tfibsegs (mrestrict H m) a 8 v ->
(forall b, a <= b < a + 8 -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a 8 v).
{ intros m m' a v Hv Hf. apply (YF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
(* phase 1: entry *)
unfold cfg_at. change (w64 pc0) with (Z_to_bv 64 pc0).
set (EE := YE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (HS0 : st_ok tfibsegs EE (ssA pc0) (restrict H (mkst regs (Z_to_bv 64 pc0) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB icpt_rodata ly S H mem EE (icpt_rodata_chk ly) (proj1 HAR))].
unfold stkA, SC_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2208)); [exact EE2 | lia | lia |].
intros a Ha. apply YF0x.apresent_writable; [unfold YF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply HpresE. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, icpt_rodata, ro_region, extent_of_region, SC_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; first [exact Hal16 | lia]. }
eapply SRr_bind; [apply (sc_phase_to W EE SL_HEAD _ _ _ _ _ HS0 RA)|].
cbv beta. intros W1 cf1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2208 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- SC_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold SC_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R2].
apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j v off, nth_error SAVEDA j = Some (v, off) -> forall z, sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros j v off Hj z Hz Hrg. rewrite forallb_forall in HSV. specialize (HSV (v, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 v _ Hck Hz); zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q18 : getr regs1 18 = w64 x) by (rewrite (RD 18%bv (SOff 10 0) R18); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q9 : getr regs1 9 = w64 y) by (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q20 : getr regs1 20 = w64 0) by (rewrite (RD 20%bv (SLit 0) R20); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2192)) by (rewrite (RD 2%bv (SOff 2 (- SC_FRAME)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 2192) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2208 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2208 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold SC_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (YE2y.apresent_mod _ (ms_mem ms1) a). rewrite (YE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2208)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (YE2y.aview_mod _ (ms_mem ms1) a). rewrite (YE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2208)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (YE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
(* phase 2: the byte loop *)
assert (AVS : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2 * 4096 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a)
by (intros a Hr Ha; apply AV1; [exact Hr | lia]).
assert (LB : forall j, 0 <= j < k -> exists b, 0 < b < 256 /\
rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (x + j)) 1 = Some [Z_to_bv 8 b] /\
rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (y + j)) 1 = Some [Z_to_bv 8 b]).
{ intros j Hj. destruct (Hbef j Hj) as (b & Bx & By & Bnz).
destruct (aview_byte_ex H mem (x + j) b Bx) as (bb & _ & _ & Rb).
exists b. split; [lia|]. split; apply aview_rdn1.
- rewrite AVS; [exact Bx | lia | apply Hbx; lia].
- rewrite AVS; [exact By | lia | apply Hby; lia]. }
assert (LX : rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (x + k)) 1 = Some [Z_to_bv 8 c1])
by (apply aview_rdn1; rewrite AVS; [exact Hc1v | lia | apply Hbx; lia]).
assert (LY : rdn tfibsegs (mrestrict H (ms_mem ms1)) (Z_to_bv 64 (y + k)) 1 = Some [Z_to_bv 8 c2])
by (apply aview_rdn1; rewrite AVS; [exact Hc2v | lia | apply Hby; lia]).
destruct (strcmp_loop (mrestrict H (ms_mem ms1)) (seg_rom tfibsegs) x y k c1 c2 ltac:(lia) ltac:(lia) Hxk Hyk LB Rc1 Rc2 LX LY Hstop Hk0
regs1 Q18 Q9 Q20) as (regs2 & Hms & L20 & L25 & L26 & LK).
assert (Hms' : msteps tfibsegs (restrict H ms1) (mkst regs2 (Z_to_bv 64 SL_EXIT) (mrestrict H (ms_mem ms1)) (seg_rom tfibsegs)))
by (rewrite Hshape at 1; rewrite restrict_mkst_fx; exact Hms).
eapply (SRr_msteps tfibsegs Hwx W ms1 _ md1 _ Hms').
intros model' Hsbm _. fold H. rewrite unrestrict_mkst_mrestrict.
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms1) model').
{ apply (al_frame _ _ LAWS ly S W (ms_mem ms1) md1 (ms_mem ms1) _ HAR1);
[intros a _ _; reflexivity | intros a Hv; exact Hv | | | | exact (YE2y.hs_kept_eq _ _ _ (fun z => eq_refl))];
apply (same_but_materialized_frame md1 _ Hsbm). }
assert (Hsp1 : spZ regs2 = sp0 - 2192) by (unfold spZ; rewrite (LK 2%bv) by discriminate; exact R1sp).
(* phase 3: the s1 range check *)
change (mkCfg (mkst regs2 (Z_to_bv 64 SL_EXIT) (ms_mem ms1) (seg_rom tfibsegs)) model')
with (cfg_at tfibsegs StrcmpChkX.RC_ENTRY regs2 (ms_mem ms1) model').
eapply SRr_bind.
{ apply (StrcmpChkX.scx_check_srr B LAWS TB ly S W regs2 (ms_mem ms1) model' x (k + 1) HAR2).
- rewrite Hsp1. replace (sp0 - 2192) with (sp0 + (-137) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite Hsp1. unfold StrcmpChkX.RC_SCR. lia.
- rewrite Hsp1. lia.
- intros a Ha. rewrite Hsp1 in Ha. unfold StrcmpChkX.RC_SCR in Ha. apply PM1. apply HpresE. lia.
- exact L20.
- rewrite (LK 18%bv) by discriminate. exact Q18.
- lia.
- lia.
- lia.
- exact Hamx.
- eapply range_addressable_agree; [|exact Hrax]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AV1; lia.
- intros s' Hs. rewrite AV1; [exact (Hhx s' Hs) | |];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (x + (k + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + (k + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + (k + 1) - 1)) 8 ltac:(lia)); lia. }
cbv beta. intros W2 cf2 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & (X20 & X21 & X22 & X24) & Hfr3 & Hpm3).
rewrite Hsp1 in Hfr3. unfold StrcmpChkX.RC_SCR in Hfr3.
assert (KK3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 20 -> z <> 21 -> z <> 22 -> z <> 24 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H4 H5. exact (K3 z H1 H2 H3 H4 H5). }
assert (Hsp3 : spZ regs3 = sp0 - 2192)
by (unfold spZ; rewrite (KK3 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Hsp1).
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2192 - 72 <= a < sp0 - 2192) -> aview tfibsegs H mem3 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Ha; exact (Hfr3 a Hr Ha)).
(* phase 4: the s2 range check *)
change (cfg_at tfibsegs StrcmpChkX.RC_END regs3 mem3 md3) with (cfg_at tfibsegs StrcmpChkY.RC_ENTRY regs3 mem3 md3).
eapply SRr_bind.
{ apply (StrcmpChkY.scy_check_srr B LAWS TB ly S W regs3 mem3 md3 y (k + 1) HAR3).
- rewrite Hsp3. replace (sp0 - 2192) with (sp0 + (-137) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite Hsp3. unfold StrcmpChkY.RC_SCR. lia.
- rewrite Hsp3. lia.
- intros a Ha. rewrite Hsp3 in Ha. unfold StrcmpChkY.RC_SCR in Ha. apply Hpm3. apply PM1. apply HpresE. lia.
- exact X20.
- rewrite (KK3 9 9%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (LK 9%bv) by discriminate. exact Q9.
- exact X21.
- exact X24.
- lia.
- lia.
- lia.
- exact Hamy.
- eapply range_addressable_agree; [|exact Hray]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
rewrite AV3 by lia. apply AV1; lia.
- intros s' Hs. rewrite AV3, AV1; [exact (Hhy s' Hs) | | | |];
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (y + (k + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (y + (k + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + (k + 1) - 1)) 8 ltac:(lia)); lia. }
cbv beta. intros W3 cf3 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & K4 & Hsbm4 & (Y20 & Y24) & Hfr4 & Hpm4).
rewrite Hsp3 in Hfr4. unfold StrcmpChkY.RC_SCR in Hfr4.
assert (KK4 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 20 -> z <> 21 -> z <> 24 -> getr regs4 rr = getr regs3 rr).
{ intros z rr -> H1 H2 H3 H4. exact (K4 z H1 H2 H3 H4). }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2192 - 72 <= a < sp0 - 2192) -> aview tfibsegs H mem4 a = aview tfibsegs H mem3 a)
by (intros a Hr Ha; exact (Hfr4 a Hr Ha)).
assert (AVT : forall b, sp0 - 104 <= b < sp0 -> aview tfibsegs H mem4 b = aview tfibsegs H (ms_mem ms1) b)
by (intros b Hb; rewrite AV4, AV3 by lia; reflexivity).
assert (KS : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 10 -> z <> 20 -> z <> 21 -> z <> 22 -> z <> 24 -> z <> 25 -> z <> 26 ->
getr regs4 rr = getr regs1 rr).
{ intros z rr Hrr Hcs H10 H20 H21 H22 H24 H25 H26. rewrite (KK4 z rr Hrr Hcs H20 H21 H24), (KK3 z rr Hrr Hcs H20 H21 H22 H24). subst rr.
unfold acallee_saved in Hcs.
assert (Hz : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 23 \/ z = 27) by lia.
destruct Hz as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
apply LK; intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E. }
(* phase 5: the tail *)
change (cfg_at tfibsegs StrcmpChkY.RC_END regs4 mem4 md4) with (mkCfg (mkst regs4 (Z_to_bv 64 SC_TAIL) mem4 (seg_rom tfibsegs)) md4).
apply (sc_tail B LAWS ly S W regs mem md regs4 mem4 md4 c1 c2 HPRE Hslo2 Rc1 Rc2 HAR4).
all: try change (spZ regs) with sp0.
- eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm|].
eapply same_but_materialized_trans; [exact Hsbm3 | exact Hsbm4].
- intros a Hr Ha. unfold SC_SCR in Ha. rewrite AV4, AV3; [apply AV1; [exact Hr | lia] | exact Hr | lia | exact Hr | lia].
- intros a Hp. apply Hpm4. apply Hpm3. apply PM1. exact Hp.
- rewrite (KK4 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia).
rewrite (KK3 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact L25.
- rewrite (KK4 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia).
rewrite (KK3 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact L26.
- rewrite (KS 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). unfold SC_FRAME. exact Q2.
- rewrite (KS 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q3.
- rewrite (KS 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q4.
- apply (VT (ms_mem ms1)); [exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 1))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 8))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 9))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 18))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 4%nat (SOff 19 0) (-40) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 19))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 5%nat (SOff 20 0) (-48) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 20))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 6%nat (SOff 21 0) (-56) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 21))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 7%nat (SOff 22 0) (-64) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 22))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 8%nat (SOff 23 0) (-72) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 23))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 9%nat (SOff 24 0) (-80) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 24))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 10%nat (SOff 25 0) (-88) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 25))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 11%nat (SOff 26 0) (-96) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 26))) | intros b Hb; apply AVT; lia].
- apply (VT (ms_mem ms1)); [exact (CK 12%nat (SOff 27 0) (-104) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 27))) | intros b Hb; apply AVT; lia].
Qed.
Theorem grant_strcmp_icpt : forall B, AR_laws tfibsegs B -> TfibSyms B -> astrcmp_realizes tfibsegs B STRCMP_ICPT.
Proof. intros B LAWS TB. exact (strcmp_srr B LAWS TB STRCMP_ICPT r_A_icpt). Qed.
Theorem grant_strcmp_tramp : forall B, AR_laws tfibsegs B -> TfibSyms B -> astrcmp_realizes tfibsegs B STRCMP_TRAMP.
Proof. intros B LAWS TB. exact (strcmp_srr B LAWS TB STRCMP_TRAMP r_A_tramp). Qed.
End d.
