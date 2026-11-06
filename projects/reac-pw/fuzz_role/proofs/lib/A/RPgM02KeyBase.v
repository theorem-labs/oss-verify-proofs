(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v, RPgM02KeyI.v and RPgM02KeyV.v
   at 595d8c5dd1b5 (the value language of the value entry's address and of a `lw`, the expect_value cases, the
   shadow entry over the value entry, the value dispatch, the Int arm and the value tail),
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyF.v at 7e8cf15c304a (the Float arm: the size test, the `flw` and
   pod_nearest) and proofs/reac-pw/fuzz_rate/lib/A/RtPgScanF.v at 22306b8175e6 (the pairs of the scan across a
   key) for reac-pw/fuzz_rate image A: role's pcs become rate's, the shadow base is rate's s2 (atom 18), role's Role
   answers become Rate.expect_value / Rate.rate_of_pairs, role's value tail (a bound test and check_role) becomes
   rate's check_rate on the hz cell, the out cell is R+0x158, the `flw` is stepped by YA0n.SRr_step, and the key
   compare (the spills, the strcmp wrapper, the mismatch exit to O) is new. *)
(* Modified by Theorem Labs, 2026-10: the shared parts of proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at
   48d3cf0d8e40 (the model facts, the value language of a `lw`, the value entry's facts, the interfaces of the
   pieces and their chain, the transport of a cut across the half's runs and calls) and of
   proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Chk.v at 5e00caea0758 (ch_L, ch_K, ch_far, ch_garr8_kept, ch_cut_A) for
   image B (fuzz_rate.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02KitB.v at f07713e8e823 and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v at 887bee7c56d for reac-pw/fuzz_role image B
   (fuzz_role.asan-ubsan): the cuts are lib/AU/RPgSeg.v's (rsb_ -> rs_); the model is role's (Role.expect_value,
   Role.role_of_pairs, Role.flag_rc, the role cell's rs_rcell) with lib/A/RPgM02KeyBase.v's role lemmas (m2k_sx_small,
   m2k_U_sextw, m2k_flag_small / _big, m2k_s32_small, m2k_nearest_range); rs_L_chk's registers are s0, s1, s2 (pod),
   s3, s4 (&role) and s11 (the shadow offset) and its cells R+0x20 (F) and R+0x40 (the flags byte); the join's cut is
   rs_cut_T (s9 = the answer's code, s6 = pp, s8 = the flags byte, s10 = F, the cells R+0x38 = F and R+0x140 = pp)
   where fuzz_rate's was its A cut, and the value tail's interface is role's (a2 = the value v, a role when v < 2,
   malformed otherwise); the zone the half writes is image B's five spill cells R+0x128 .. R+0x140, R+0x148 ..
   R+0x158 and the flag cell R+0x178, which is also pod_nearest's out cell; the shadow base is s11 (atom 27); the
   value entry's interfaces carry the registers image B's readers use (a7 = &ent[0] + 4, s7 = 104 v, s9 = the code)
   and the cells R+0x158 (the code) and R+0x120 (0x4018). The check walks of fuzz_rate's file are not here. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/AU/RPgM02KeyBase.v, with its addresses and numbers changed; 339 of its 564 lines of code are new or changed and 520 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes): THE SHARED LAYER of
   the KEY MATCH of segment M02's match half, which lib/A/RPgM02KeyC.v (the key compare), lib/A/RPgM02KeyI.v (the
   value dispatch and the Int arm), lib/A/RPgM02KeyF.v (the Float arm), lib/A/RPgM02KeyV.v (the value tail) and
   lib/A/RPgM02Key.v (the assembly, which proves lib/A/RPgSeg.v's rs_piece_W11b_key_stmt) all Require: the
   engine's facts, regions and shadow entry for this half, the float-state lemmas of its one `flw`, its
   value-language and Pod-model facts, and the transport of a cut's register and memory facts across a call or a
   run. No lemma of this half is stated twice: a piece that needs a new helper gets it here.
   Proves no function (kind: segment lemma).

   THE CODE (capstone over the pinned file; `SHADOW` marks an instrumented check's shadow byte):
     0x822a8 addi a1,s5,-1; 0x822ac blt a1,ra (ra = -1, s5 = m + 1 >= 1: never taken) -> ABS
     0x822b0 a1 := 0x20ee0 (.str.1 "reac.cfg.role"); 0x822b8..0x822cc spill t2 -> R+0xf8, s11 -> R+0xf0,
             mv s11,t3, t4 -> R+0xe8, t5 -> R+0xe0, t6 -> R+0xd8; 0x822d0 jal 0x41ad0 (the strcmp wrapper)
     0x822d4 li ra,-1; 0x822d8..0x822f0 the five reloads, a4 := 0x68, mv t3,s11; 0x822f4 mv a1,s9;
             0x822f8 bnez a0 -> O 0x821bc (the key is not "reac.cfg.role": the scan goes on at m + 2)
     0x822fc li a0,-1; 0x82300 sd a0,0x118(s1); 0x82304..0x82314 a0 := &ent[v] by `li 0xd; slli 0x23;
             slli s5,0x20; mulhu; add t3`; v = m + 1
     0x82318 SHADOW; 0x82328 lw a1 = ent[v].type; 0x82330 ld s9,0x28(s1); 0x82334 ld s11,0x80(s1);
             0x82338 beq a1,6 -> Float; 0x82340 bne a1,4 -> MAL
     Int   0x82344 .. 0x8237c: SHADOW, lw a1 = size, bltu a1,4 -> MAL, a0 += 8, SHADOW, lw a2 = the body word,
             j 0x823e0
     Float 0x82398 .. 0x823dc: SHADOW, lw a1 = size, bltu a1,4 -> MAL, a0 += 8, SHADOW, flw fa0,0(a0),
             a0 := R+0x118, jal pod_nearest 0x82ccc, beqz a0 -> MAL, ld a2,0x118(s1)
     0x823e0 li a0,2; 0x823e4 bgeu a2,a0 -> MAL; 0x823e8 lw a1,0(s6) (the role cell, no check: a constant
             offset in the frame for locals); 0x823ec sext.w a2,a2; 0x823f0 mv a0,s8;
             0x823f4 jal check_role 0x82bdc; 0x823f8 j T 0x82408.
   The five instrumented checks (0x82320, 0x82350, 0x82370, 0x823a4, 0x823c4) are 4-byte loads inside
   [&ent[v], &ent[v] + 16), which lies in the first block; one shadow entry mkSHE 10 0 16 over the entry's own
   atom covers all five, so the engine reads shadow 0 and the five `bnez` are decided not taken, and no slow
   block is entered.

   THE FLOAT STATE. `flw fa0,0(a0)` 0x823cc is the only float instruction of the half; the engine has no rule for
   it, so the walk stops there, steps it by YK0o.fp_step_flw and re-enters at 0x823d0 at the new float state. It
   writes fa0 (f10), which rs_chk_base's rl_fxk [10;13;14;15] already allows; pod_nearest adds fa5 (f15).

   WHAT IS A SECTION HYPOTHESIS. MTL, LAWS, the strcmp wrapper's contract (at every float state: the cut's float
   state is not the harness's) and the two symbol-record equations the pod_nearest lift asks for. Every other
   callee of this half is a theorem on the branch: RPgCheck.rl_check_role_A and
   RPgNear.rl_pod_nearest_A_of (RPgNearW.pod_nearest_A_holds NearSFClose.near_sf_facts_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YO0a YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgStrcmp RPgMem RPgCheck RPgCheckStr RPgScanF RPgM02Base.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgNear RPgNearW RPgNearC.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require NearSFClose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the pcs this file runs between ===================================== *)
Definition M2K_KV : Z := 0x82318.       (* the value entry's address is formed: the walk re-enters here *)
Definition M2K_TY : Z := 0x82338.       (* beq a1,6 *)
Definition M2K_TY4 : Z := 0x82340.      (* bne a1,4 *)
Definition M2K_ISZ : Z := 0x82360.      (* bltu size,4 (Int) *)
Definition M2K_FSZ : Z := 0x823b4.      (* bltu size,4 (Float) *)
Definition M2K_FLW : Z := 0x823cc.      (* flw fa0,0(a0) *)
Definition M2K_FOUT : Z := 0x823d0.     (* a0 := R + 0x118 *)
Definition M2K_FRET : Z := 0x823d8.     (* beqz a0 after pod_nearest *)
Definition M2K_VAL : Z := 0x823e0.      (* li a0,2 : the two arms meet *)
Definition M2K_VCMP : Z := 0x823e4.     (* bgeu a2,a0 *)
Definition M2K_RRET : Z := 0x823f8.     (* j T, after check_role *)
Definition M2K_SPILL : Z := 0x822b0.    (* the literal and the five spills *)
Definition M2K_BACK : Z := 0x822d4.     (* the wrapper returns here *)
Definition M2K_MATCH : Z := 0x822f8.    (* bnez a0 *)

(* ===================================== the engine's facts, regions and shadow ===================================== *)
(* atom 9 is s1 = R, atom 23 is s7 = the runtime's shadow offset, atom 10 is a0 = &ent[v] *)
Definition m2k_facts : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition m2k_facts10 : facts :=
mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
          (10%nat, mkAF 4096 0x7fffff800000 0) ] [] [].
(* the five checks of this half read shadow bytes of [&ent[v], &ent[v] + 16) *)
Definition m2k_SH : list shent := [ mkSHE 10 0 16 ].
(* the value entry: its type, its size and the first four bytes of its body *)
Definition m2k_ent (t s bw : sv) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 4 t); YP09.mkChunk 4 (CVal 4 s); YP09.mkChunk 8 (CVal 4 bw)].
(* the two regions the value dispatch reads: the real frame's two cells and the value entry *)
Definition m2k_rgs (t s bw : sv) : smem :=
[m2_frame 0 0x138 0 0 [YP09.mkChunk 0x28 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 33 0))];
 m2k_ent t s bw].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma m2k_facts_ok : forall E R,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 23) = SHADOW_OFF -> facts_ok E m2k_facts.
Proof.
intros E R H9 HR Hal H23. split; [|split; [exact I | exact I]].
cbn [m2k_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H23. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

Lemma m2k_facts10_ok : forall E R a,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 23) = SHADOW_OFF ->
bv_unsigned (ew E 10) = a -> 4096 <= a <= 0x7fffff800000 -> facts_ok E m2k_facts10.
Proof.
intros E R a H9 HR Hal H23 H10 Ha. split; [|split; [exact I | exact I]].
cbn [m2k_facts10 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H23, H10. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia.
all: try apply Z.mod_1_r.
Qed.

(* the shadow entry: every byte of [a, a + 16) is marked usable and the range is apart from the shadow band *)
Lemma m2k_sh_ok : forall (W : world rsegs) mem E a,
U E M2_Bx = SHADOW_OFF -> U E (SOff 10 0) = a ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a 16 ->
(a + 16 <= kLowShadowBeg \/ kHighMemBeg <= a) ->
sh_ok rsegs M2_Bx m2k_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E a HB H10 Hra Happ. apply Forall_cons; [|apply Forall_nil].
apply (YCbq.shent_ok_of_range rsegs (w_H W) mem E M2_Bx 10 a 16 a 0 16 Hra HB H10 ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ===================================== the float state ===================================== *)
Lemma m2k_fxk_trans : forall ks ks' f g h,
rl_fxk ks f g -> rl_fxk ks' g h -> (forall z, In z ks' -> In z ks) -> rl_fxk ks f h.
Proof.
intros ks ks' f g h (Hg & _) (Hh & Hcsr) Hin. split; [|exact Hcsr].
intros k Hk. rewrite (Hh k ltac:(intros Hc; exact (Hk (Hin _ Hc)))). exact (Hg k Hk).
Qed.

Lemma m2k_fxk_set : forall ks f g (r : Prelude.reg) (w : word),
In (bv_unsigned r) ks -> rl_fxk ks f g ->
rl_fxk ks f (YK11.mkFP (bvmap_set r w (@fp_regs g)) (@fp_csr g)).
Proof.
intros ks f g r w Hr (Hg & Hcsr). split; [|exact Hcsr].
intros k Hk. cbn [fp_regs].
destruct (base.decide (k = r)) as [->|Hne]; [exfalso; exact (Hk Hr)|].
change (bvmap_set r w (@fp_regs g)) with (regupd (@fp_regs g) r w).
rewrite (regupd_other (@fp_regs g) r w k Hne). exact (Hg k Hk).
Qed.

End b.

(* ===================================== the value language ===================================== *)
(* m2k_denot_a0 / m2k_U_a0: the address of ent[v] that 0x82304 .. 0x82314 forms, `li a0,13; slli a0,a0,35;
   slli s5,s5,32; mulhu a0,s5,a0; add a0,t3,a0`: mulhu((v * 2^32) mod 2^64, 13 * 2^35) = 104 v for 0 <= v <= 32,
   since (v * 2^32) * (13 * 2^35) = 104 v * 2^64. m2k_sx and its lemmas: the 64-bit word an `lw` leaves for a
   32-bit pattern, and its comparisons. m2k_U_sextw: the `sext.w` of the two value arms. *)
Lemma m2k_denot_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff p 0)
                (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = Z_to_bv 64 (b + 104 * i).
Proof.
intros E n p i b Hn Hi Hp Hb Hs.
rewrite (denot_lit_U E). apply (f_equal (Z_to_bv 64)).
rewrite ?U_SAlu, ?U_SMd, ?U_SAlu, ?U_SOff, ?U_SLit, Hn, Hp, !Z.add_0_r.
rewrite !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw Z.of_N].
change (zcanon 32) with 32. change (zcanon 446676598784) with 446676598784.
change (Z.land 32 63) with 32.
rewrite (zcanon_id i), (zcanon_id b) by (unfold M64; lia).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
rewrite (zcanon_id (i * 4294967296)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia.
replace (i * 4294967296 * 446676598784) with (104 * i * 2 ^ 64)
  by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite Z.div_mul by (change (2 ^ 64) with 18446744073709551616; lia).
rewrite (zcanon_id (104 * i)) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma m2k_U_a0 : forall E (n p : nat) (i b : Z),
  ew E n = Z_to_bv 64 i -> 0 <= i <= 32 ->
  ew E p = Z_to_bv 64 b -> 0 <= b -> b + 104 * i < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff p 0)
        (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 446676598784)))
  = b + 104 * i.
Proof.
intros E n p i b Hn Hi Hp Hb Hs. unfold U.
rewrite (m2k_denot_a0 E n p i b Hn Hi Hp Hb Hs).
apply unsigned_lit_small. lia.
Qed.

Definition m2k_sx (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).

Lemma m2k_U_sext32 : forall E (n : nat) (v : Z),
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = m2k_sx v.
Proof.
intros E n v H Hv.
rewrite U_SExt, (U_atom E n v H ltac:(lia)).
cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold m2k_sx, zcanon, M64, bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; cbv beta iota.
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
  rewrite Z.mod_small by lia. lia.
- replace ((v + 2 ^ 31) mod 2 ^ 32) with (v + 2 ^ 31 - 2 ^ 32)
    by (apply (Z.mod_unique _ _ 1); lia).
  symmetry. apply (Z.mod_unique _ _ (-1)); lia.
Qed.

Lemma m2k_sx_eq : forall v w, 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 -> (m2k_sx v = w <-> v = w).
Proof.
intros v w Hv Hw. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; split; intros; lia.
Qed.

Lemma m2k_sx_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= m2k_sx v < 2 ^ 64.
Proof.
intros v Hv. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2k_sx_small : forall v, 0 <= v < 2 ^ 32 -> (m2k_sx v < 2 <-> (v = 0 \/ v = 1)).
Proof.
intros v Hv. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; split; intros; lia.
Qed.

Lemma m2k_sx_id : forall v, 0 <= v < 2 ^ 31 -> m2k_sx v = v.
Proof.
intros v Hv. unfold m2k_sx.
destruct (Z.ltb_spec v (2 ^ 31)); cbv beta iota; lia.
Qed.

Lemma m2k_U_sextw : forall E (a : sv) (v : Z), U E a = v -> 0 <= v < 2 ^ 31 ->
  U E (SAluw ALU_ADD a (SLit 0)) = v.
Proof.
intros E a v H Hv.
rewrite U_of_S, S_SAluw, H, U_SLit.
change (zcanon 0 mod 2 ^ 32) with 0.
rewrite (Z.mod_small v (2 ^ 32)) by lia.
cbn [zalu_raw]. rewrite Z.add_0_r.
rewrite swrap32_id by lia.
apply wrap64_id. unfold M64. lia.
Qed.

Lemma m2k_denot_of_U : forall E (a : sv) (v : Z), U E a = v -> sv_denot E a = Z_to_bv 64 v.
Proof.
intros E a v H. rewrite (denot_lit_U E a), H. reflexivity.
Qed.

Lemma m2k_U_atom : forall E (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof. exact U_atom. Qed.

(* ===================================== the model facts ===================================== *)
(* What a key entry is, the text of a NUL-terminated body, the first pair of the scan, the moves of the scan
   invariant across the key compare, what the value entry's type and size decide, and the record's bounds.
   The scan invariant's own moves are lib/A/RPgScanF.v's (rk_inv_key) and are used, not restated. *)
Lemma m2k_key_of_some : forall (e : ent) (kb : list byte), key_of e = Some kb ->
  kb = Cursor.cstr (e_body e) /\ e_type e = POD_STRING /\ 1 <= e_size e /\
  bv_unsigned (nth (Z.to_nat (e_size e - 1)) (e_body e) NUL) = 0.
Proof.
intros e kb. unfold key_of, last_body_byte.
destruct (Z.eqb_spec (e_type e) POD_STRING) as [E1|E1]; cbn [andb]; cbv beta iota;
  [|intros H; discriminate H].
destruct (Z.leb_spec 1 (e_size e)) as [E2|E2]; cbn [andb]; cbv beta iota; [|intros H; discriminate H].
destruct (Z.eqb_spec (bv_unsigned (nth (Z.to_nat (e_size e - 1)) (e_body e) NUL)) 0) as [E3|E3];
  cbv beta iota; intros H; [|discriminate H].
injection H as <-. split; [reflexivity|]. split; [exact E1|]. split; [exact E2 | exact E3].
Qed.

Lemma m2k_cstr_bytes : forall (l : list byte) (k : nat), (k < length l)%nat ->
  bv_unsigned (nth k l NUL) = 0 ->
  (length (Cursor.cstr l) < length l)%nat /\
  (forall i, (i < length (Cursor.cstr l))%nat ->
     nth i l NUL = nth i (Cursor.cstr l) NUL /\ 0 < bv_unsigned (nth i (Cursor.cstr l) NUL) < 256) /\
  bv_unsigned (nth (length (Cursor.cstr l)) l NUL) = 0.
Proof.
intros l k Hk H0.
assert (Hle : forall (l : list byte) (k : nat), (k < length l)%nat -> bv_unsigned (nth k l NUL) = 0 ->
  (Cursor.nul_idx l <= k)%nat).
{ clear. induction l as [|x l IH]; intros k; cbn [Cursor.nul_idx length]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hk H0; [lia|].
  destruct k as [|k]; cbn [nth] in H0; [contradiction|].
  pose proof (IH k ltac:(lia) H0). lia. }
assert (Hnz : forall (l : list byte) (i : nat), (i < Cursor.nul_idx l)%nat -> bv_unsigned (nth i l NUL) <> 0).
{ clear. induction l as [|x l IH]; intros i; cbn [Cursor.nul_idx]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hi; [lia|].
  destruct i as [|i]; cbn [nth]; [exact Ex|]. apply IH. lia. }
assert (Hat : forall (l : list byte), (Cursor.nul_idx l < length l)%nat ->
  bv_unsigned (nth (Cursor.nul_idx l) l NUL) = 0).
{ clear. induction l as [|x l IH]; cbn [Cursor.nul_idx length]; [intros; lia|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [Ex|Ex]; cbv beta iota; intros Hl; cbn [nth]; [exact Ex|].
  apply IH. lia. }
assert (Hnth : forall (l : list byte) (n i : nat), (i < n)%nat -> nth i (firstn n l) NUL = nth i l NUL).
{ clear. induction l as [|x l IH]; intros n i Hi; [destruct n; reflexivity|].
  destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia. }
pose proof (Hle l k Hk H0) as Hn.
assert (Hlen : length (Cursor.cstr l) = Cursor.nul_idx l).
{ unfold Cursor.cstr. rewrite length_firstn. pose proof (Cursor.nul_idx_le l). lia. }
rewrite Hlen. split; [lia|]. split.
- intros i Hi. unfold Cursor.cstr. rewrite (Hnth l (Cursor.nul_idx l) i Hi). split; [reflexivity|].
  pose proof (Hnz l i Hi). pose proof (Cursor.byte_range (nth i l NUL)). lia.
- apply Hat. lia.
Qed.

Lemma m2k_bytes_eqb_true : forall a b, Cursor.bytes_eqb a b = true -> a = b.
Proof. intros a b H. apply Cursor.bytes_eqb_eq. exact H. Qed.

Lemma m2k_bytes_eqb_false : forall a b, a <> b -> Cursor.bytes_eqb a b = false.
Proof.
intros a b H. destruct (Cursor.bytes_eqb a b) eqn:E; [|reflexivity].
apply Cursor.bytes_eqb_eq in E. contradiction.
Qed.

Lemma m2k_map_bv_inj : forall (a b : list byte),
  map (fun x : byte => bv_unsigned x) a = map (fun x : byte => bv_unsigned x) b -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hxy Hab. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hab].
Qed.

Lemma m2k_rop_cons : forall vf k e ps,
  Role.role_of_pairs vf ((k, e) :: ps) =
  (if Cursor.bytes_eqb k Role.ROLE_KEY then vf e else Role.role_of_pairs vf ps).
Proof.
intros vf k e ps. unfold Role.role_of_pairs. cbn [find fst].
destruct (Cursor.bytes_eqb k Role.ROLE_KEY); reflexivity.
Qed.

Lemma m2k_inv_mismatch : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rs_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) rk_d) = None) ->
  key_of (nth m (ents rec) rk_d) = Some kb -> kb <> Role.ROLE_KEY ->
  rs_scan_inv rec (S (S m)).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Hne.
pose proof (RPgScanF.rk_inv_key rec at0 m kb Hinv Ham Hm Hq Hk) as E.
split; [lia|].
rewrite E, m2k_rop_cons, (m2k_bytes_eqb_false kb Role.ROLE_KEY Hne). reflexivity.
Qed.

Lemma m2k_inv_match : forall (rec : pod_rec) (at0 m : nat) (kb : list byte),
  rs_scan_inv rec at0 -> (at0 <= m)%nat -> (S m < length (ents rec))%nat ->
  (forall q, (at0 <= q < m)%nat -> key_of (nth q (ents rec) rk_d) = None) ->
  key_of (nth m (ents rec) rk_d) = Some kb -> kb = Role.ROLE_KEY ->
  rs_E0 rec = Role.expect_value (nth (S m) (ents rec) rk_d).
Proof.
intros rec at0 m kb Hinv Ham Hm Hq Hk Heq. subst kb.
rewrite (RPgScanF.rk_inv_key rec at0 m Role.ROLE_KEY Hinv Ham Hm Hq Hk), m2k_rop_cons.
assert (Cursor.bytes_eqb Role.ROLE_KEY Role.ROLE_KEY = true) as -> by (apply Cursor.bytes_eqb_eq; reflexivity).
reflexivity.
Qed.

Lemma m2k_expect_int : forall e, ent_wf e -> e_type e = POD_INT -> 4 <= e_size e ->
  Role.expect_value e = Role.flag_rc (Accessors.s32 (Cursor.rd32 (e_body e))).
Proof.
intros e _ Ht Hs. unfold Role.expect_value, Accessors.int_of. rewrite Ht.
rewrite (proj2 (Z.leb_le 4 (e_size e)) Hs).
assert (E : (POD_INT =? POD_INT) = true) by reflexivity. rewrite E. cbn [andb]. reflexivity.
Qed.

Lemma m2k_expect_float : forall e, ent_wf e -> e_type e = POD_FLOAT -> 4 <= e_size e ->
  Role.expect_value e =
  match Nearest.nearest (Cursor.rd32 (e_body e)) Nearest.INT32_MIN Nearest.INT32_MAX with
  | Some n => Role.flag_rc n | None => (None, -1) end.
Proof.
intros e _ Ht Hs. unfold Role.expect_value, Accessors.int_of, Accessors.float_of. rewrite Ht.
rewrite (proj2 (Z.leb_le 4 (e_size e)) Hs).
assert (E1 : (POD_FLOAT =? POD_INT) = false) by reflexivity.
assert (E2 : (POD_FLOAT =? POD_FLOAT) = true) by reflexivity.
rewrite E1, E2. cbn [andb]. reflexivity.
Qed.

Lemma m2k_expect_none : forall e, ent_wf e ->
  (e_type e <> POD_INT /\ e_type e <> POD_FLOAT) \/ e_size e < 4 ->
  Role.expect_value e = (None, -1).
Proof.
intros e _ [[H1 H2]|H3]; unfold Role.expect_value, Accessors.int_of, Accessors.float_of.
- rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
- rewrite (proj2 (Z.leb_gt 4 (e_size e)) H3).
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma m2k_flag_small : forall v, 0 <= v < 2 ->
  snd (Role.flag_rc v) = 1 /\ exists w, fst (Role.flag_rc v) = Some w /\ Role.role_z w = v.
Proof.
intros v Hv. assert (v = 0 \/ v = 1) as [->| ->] by lia.
- split; [reflexivity|]. exists Role.MASTER. split; reflexivity.
- split; [reflexivity|]. exists Role.SLAVE. split; reflexivity.
Qed.

Lemma m2k_flag_big : forall v, v < 0 \/ 2 <= v -> Role.flag_rc v = (None, -1).
Proof.
intros v Hv. unfold Role.flag_rc.
destruct (Z.eqb_spec v 0) as [E|E]; [exfalso; lia|].
destruct (Z.eqb_spec v 1) as [E'|E']; [exfalso; lia|].
reflexivity.
Qed.

Lemma m2k_rd32_range : forall l, 0 <= Cursor.rd32 l < 2 ^ 32.
Proof. exact Cursor.rd32_range. Qed.

Lemma m2k_s32_small : forall z, 0 <= z < 2 ^ 32 ->
  (Accessors.s32 z = 0 <-> z = 0) /\ (Accessors.s32 z = 1 <-> z = 1).
Proof.
intros z Hz. unfold Accessors.s32.
destruct (Z.ltb_spec z (2 ^ 31)); cbv beta iota; split; split; intros; lia.
Qed.

Lemma m2k_nearest_range : forall b r,
  Nearest.nearest b Nearest.INT32_MIN Nearest.INT32_MAX = Some r ->
  - 2 ^ 31 <= r <= 2 ^ 31 - 1.
Proof.
intros b r H. unfold Nearest.nearest in H.
destruct (Nearest.near_f32 b) as [r'|]; cbv beta iota in H; [|discriminate H].
destruct ((Nearest.INT32_MIN <=? r') && (r' <=? Nearest.INT32_MAX)) eqn:E; cbv beta iota in H;
  [|discriminate H].
injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
unfold Nearest.INT32_MIN, Nearest.INT32_MAX in *. lia.
Qed.

Lemma m2k_ent_mem_len : forall e, ent_wf e -> (length (Layout.ent_mem e) = 104)%nat.
Proof. intros e (_ & Hb & Hs). apply Layout.length_ent_mem. lia. Qed.

Lemma m2k_ent_type_slice : forall e, ent_wf e ->
  RPgMem.rm_slice (Layout.ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof.
intros e _. unfold RPgMem.rm_slice, Layout.ent_mem. cbn [skipn].
change (Z_to_le_bytes 4 (e_type e)) with (Cursor.le32 (e_type e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2k_ent_size_slice : forall e, ent_wf e ->
  RPgMem.rm_slice (Layout.ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e _. unfold RPgMem.rm_slice, Layout.ent_mem.
rewrite (Layout.skipn_app_eq (Cursor.le32 (e_type e))) by reflexivity.
change (Z_to_le_bytes 4 (e_size e)) with (Cursor.le32 (e_size e)).
apply Layout.firstn_app_eq. reflexivity.
Qed.

Lemma m2k_ent_body_slice : forall e, ent_wf e -> 4 <= e_size e ->
  RPgMem.rm_slice (Layout.ent_mem e) 8 4 = firstn 4 (e_body e).
Proof.
intros e (_ & Hb & Hs) H4. unfold RPgMem.rm_slice, Layout.ent_mem.
assert (E : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
  by (intros; reflexivity).
rewrite E, firstn_app.
replace (4 - length (e_body e))%nat with 0%nat by lia.
cbn [firstn]. apply app_nil_r.
Qed.

(* the body's first four bytes as a field of the entry's 104, for EVERY size: ent_mem pads the body with zeros,
   and trailing zeros do not change a little-endian value *)
Lemma m2k_ent_word_slice : forall e, ent_wf e ->
RPgMem.rm_slice (Layout.ent_mem e) 8 4 = Z_to_le_bytes 4 (Cursor.rd32 (Model.e_body e)).
Proof.
assert (Hzero : forall k, bytes_le_to_Z (repeat Cursor.NUL k) = 0).
{ induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite RPgMem.rm_lez_cons, IH. reflexivity. }
assert (Hpad : forall (l : list byte) (k : nat), bytes_le_to_Z (l ++ repeat Cursor.NUL k) = bytes_le_to_Z l).
{ induction l as [|b l IH]; intros k; [cbn [app]; apply Hzero|].
  cbn [app]. rewrite !RPgMem.rm_lez_cons, IH. reflexivity. }
intros e (_ & Hb & Hs). unfold RPgMem.rm_slice, Layout.ent_mem.
assert (E8 : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
by (intros; reflexivity).
rewrite E8.
assert (Hlen : length (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e))) = 96%nat).
{ unfold Cursor.zeros. rewrite length_app, repeat_length. lia. }
assert (Hfr : forall (a : byte) (n k : nat), firstn n (repeat a k) = repeat a (Nat.min n k)).
{ induction n as [|n IH]; intros [|k]; cbn [firstn repeat Nat.min]; try reflexivity. rewrite IH. reflexivity. }
set (X := firstn 4 (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e)))).
assert (HX4 : length X = 4%nat) by (subst X; rewrite length_firstn, Hlen; reflexivity).
assert (Hval : bytes_le_to_Z X = Cursor.rd32 (Model.e_body e)).
{ subst X. unfold Cursor.rd32, Cursor.zeros. rewrite firstn_app, Hfr. apply Hpad. }
rewrite <- Hval, <- HX4. symmetry. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

Lemma m2k_ent_key_slice : forall e k, ent_wf e -> (k < length (e_body e))%nat ->
  RPgMem.rm_slice (Layout.ent_mem e) (8 + k) 1 = [nth k (e_body e) NUL].
Proof.
intros e k (_ & Hb & Hs) Hk. unfold RPgMem.rm_slice, Layout.ent_mem.
assert (E : forall (a b : Z) (X : list byte) (j : nat),
  skipn (8 + j) (Cursor.le32 a ++ Cursor.le32 b ++ X) = skipn j X) by (intros; reflexivity).
rewrite E.
rewrite (RPgScanF.rk_skipn_cons _ k NUL) by (rewrite length_app; lia).
cbn [firstn]. rewrite app_nth1 by exact Hk. reflexivity.
Qed.

Lemma m2k_buf_max : forall rec, pod_rec_wf rec -> Z.of_nat (length (Model.buf rec)) <= Layout.POD_BUF_MAX.
Proof.
intros rec (Hs & Hk & He & Hl & HL & Hc). unfold Model.buf, Layout.POD_BUF_MAX.
destruct (p_corr rec) as [[off bs]|].
- destruct Hc as (Ho & Hb & _). unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn. lia.
- lia.
Qed.

Lemma m2k_bodies_96 : forall rec, pod_rec_wf rec ->
  Forall (fun e => (length (Model.e_body e) <= 96)%nat) (ents rec).
Proof.
intros rec Hw. pose proof (Model.ents_wf rec Hw) as [_ HF].
eapply Forall_impl; [|exact HF]. intros e (_ & Hb & Hs). cbv beta. lia.
Qed.

(* the first block holds exactly PP_SIZE bytes *)
Lemma m2k_pp_len : forall rec, pod_rec_wf rec ->
Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE.
Proof.
intros rec Hw. unfold Layout.pp_bytes.
apply (RPgMem.rm_pp_len_img (Model.buf rec) (Model.is_props rec) (Model.has_params rec)
  (Model.params_struct rec) (Model.ents rec) (Model.corrupt rec)
  (m2k_buf_max rec Hw) (RPgScanF.rk_nent_le rec Hw) (m2k_bodies_96 rec Hw)).
Qed.

(* ---- registers across a call or a run ---- *)
Lemma m2k_sp_of_cs : forall (regs regs' : bvmap 5 word), cs_eq [2; 3; 4]%bv regs regs' -> spZ regs' = spZ regs.
Proof.
intros regs regs' H. unfold spZ. f_equal. exact (H (2%bv : bv 5) ltac:(left; reflexivity)).
Qed.

Lemma m2k_r234 : forall (regs regs' : bvmap 5 word), cs_eq [2; 3; 4]%bv regs regs' ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs' H r Hr. destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
[left; apply bv_eq; reflexivity | right; left; apply bv_eq; reflexivity
| right; right; left; apply bv_eq; reflexivity].
Qed.

Lemma m2k_sp_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' -> spZ regs' = spZ regs.
Proof.
intros regs regs' H. unfold spZ. f_equal. exact (H 2 ltac:(unfold acallee_saved; lia)).
Qed.

(* every write window of a read-only region is empty *)
Ltac m2k_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]);
destruct Hr.

(* ===================================== the walk ===================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract, at every float state: the cut's float state is not the harness's *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, @astrcmp_realizes fy rc rsegs B M2_STRCMP.
(* the two symbol-record cells the pod_nearest lift reads *)
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

(* ---- the addresses this half never writes ---- *)
Lemma m2k_apart : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(e_pp (x_e rsegs cx) + Layout.PP_SIZE <= kLowShadowBeg \/ kHighMemBeg <= e_pp (x_e rsegs cx)) /\
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 512 <= alloc_ceiling /\
shadow_addr (e_F (x_e rsegs cx)) + 52 < 2 ^ 46 /\
alloc_ceiling <= e_R (x_e rsegs cx) - T_SEG_STK /\ 2 ^ 46 <= e_R (x_e rsegs cx) <= 2 ^ 47.
Proof.
intros cx Hpre.
pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2_frameF B LAWS cx Hpre) as (_ & HF0 & HFc & _ & _).
pose proof Hpre as Hpre'. unfold rs_pre, rl_seg_pre in Hpre'.
destruct Hpre' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hppin & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (_ & Hp0 & Hpc & Happ & _).
pose proof asan_consts as (C1 & _).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
rewrite Hreq in Hpc, Happ.
assert (HFsh : shadow_addr (e_F (x_e rsegs cx)) + 52 < 2 ^ 46).
{ unfold shadow_addr, SHADOW_OFF.
  assert (Hd2 : e_F (x_e rsegs cx) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (Hd3 : 0x7fffff800000 / 8 = 17592184995840) by (vm_compute; reflexivity).
  rewrite Hd3 in Hd2. lia. }
unfold in_app in Happ. destruct Happ as (_ & Happ').
split; [lia|]. split; [lia|].
split; [destruct Happ' as [H|[H _]]; [left; exact H | right; exact H]|].
split; [lia|]. split; [lia|]. split; [exact HFsh|]. split; [lia | exact H46].
Qed.

(* ---- the value facts of a cut, carried across a call or a run ---- *)
Lemma m2k_at_kept : forall (cx : rs_scx rsegs) (W2 W3 : world rsegs) mem2 mem3 regs2 regs3 (Wr : Z -> Prop) L,
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
aregs_preserved regs2 regs3 ->
Forall (fun f : rl_loc * Z => match fst f with
        | LReg r => acallee_saved r
        | LCell b o => forall i, 0 <= i < 8 ->
            0 <= rl_xv (x_e rsegs cx) b + o + i < 2 ^ 64 /\ ~ Wr (rl_xv (x_e rsegs cx) b + o + i)
        end) L ->
rs_at_cx rsegs cx W2 mem2 regs2 L -> rs_at_cx rsegs cx W3 mem3 regs3 L.
Proof.
intros cx W2 W3 mem2 mem3 regs2 regs3 Wr L HK Hpres HL HAT.
unfold rs_at_cx, rs_at in HAT |- *.
apply (rm_atl_kept rsegs (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) L HAT).
intros f Hf.
apply (rm_keeps_call rsegs Wr 0 0 (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 (x_e rsegs cx) (fst f));
[intros a Ha _ Hw; exact (HK a Ha Hw) | exact Hpres |].
pose proof (proj1 (Forall_forall _ _) HL f Hf) as Hm. cbv beta in Hm.
destruct (fst f) as [r|b o]; [exact Hm|].
intros i Hi. destruct (Hm i Hi) as (H1 & H2). split; [exact H1|]. split; [lia | exact H2].
Qed.

(* the only bytes a callee of this half, or a run of it, may change: the callees' stack below R and the
   real-frame cells the code writes (the five spills and pod_nearest's out cell) *)
Definition m2k_wz (cx : rs_scx rsegs) (a : Z) : Prop :=
(e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) \/
(e_R (x_e rsegs cx) + 0xd8 <= a < e_R (x_e rsegs cx) + 0x120) \/
a < 0 \/ 2 ^ 64 <= a.

(* ---- the memory facts of a cut, carried across anything that writes only inside m2k_wz ---- *)
Lemma m2k_chk_kept : forall (cx : rs_scx rsegs) rec (fx2 fx3 : YK11.FPState)
ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 ->
Z.of_nat (length (Layout.pp_bytes rec)) = Layout.PP_SIZE ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
rl_fxk [10; 13; 14; 15] fx fx3 ->
(forall a, ~ m2k_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@rs_chk_base fx rc SK rsegs B MT cx fx3 rec ly3 S3 W3 regs3 mem3 md3 /\ rs_role_at rsegs cx rec W3 mem3.
Proof.
intros cx rec fx2 fx3 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
Hpre HCB HRA Hppl Hcore3 Hfxk3 HK.
pose proof (m2k_apart cx Hpre) as (Hp0 & Hpc & Happ & HF0 & HFc & HFsh & Hceil & H46).
pose proof HCB as (_ & _ & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpodin & Hpodout).
pose proof asan_consts as (C1 & _).
assert (HNW : forall a, 0 <= a < alloc_ceiling -> ~ m2k_wz cx a).
{ intros a Ha [H|[H|[H|H]]]; unfold T_SEG_STK, ASTACK in *; lia. }
assert (HK46 : forall a, 0 <= a < alloc_ceiling ->
aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a)
by (intros a Ha; apply HK; exact (HNW a Ha)).
assert (HlenPB : Z.of_nat (length rs_PB) = 52) by (vm_compute; reflexivity).
assert (Hfsh3 : rs_fsh_at rsegs cx W3 mem3 rs_PB).
{ unfold rs_fsh_at in Hfsh |- *.
  apply (rm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh).
  intros i Hi. apply HK46. unfold shadow_addr, SHADOW_OFF in HFsh |- *.
  assert (0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (Hpp3 : rs_pp_at rsegs cx W3 mem3 (Layout.pp_bytes rec)).
{ unfold rs_pp_at, rs_u8s in Hpp |- *.
  change (garr8 rsegs (mrestrict (w_H W2) mem2) (e_pp (x_e rsegs cx))
            (map (fun x : byte => bv_unsigned x) (Layout.pp_bytes rec)))
  with (rm_bytes rsegs (w_H W2) mem2 (e_pp (x_e rsegs cx)) (Layout.pp_bytes rec)) in Hpp.
  change (garr8 rsegs (mrestrict (w_H W3) mem3) (e_pp (x_e rsegs cx))
            (map (fun x : byte => bv_unsigned x) (Layout.pp_bytes rec)))
  with (rm_bytes rsegs (w_H W3) mem3 (e_pp (x_e rsegs cx)) (Layout.pp_bytes rec)).
  apply (rm_bytes_kept_wr rsegs (m2k_wz cx) (w_H W2) mem2 (w_H W3) mem3 _ _ Hpp HK).
  intros x Hx. rewrite Hppl in Hx. apply HNW. unfold Layout.PP_SIZE in Hx, Hpc. lia. }
assert (HRA3 : rs_role_at rsegs cx rec W3 mem3).
{ unfold rs_role_at in HRA |- *.
  apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ 4 _); [|exact HRA].
  intros k Hk. apply HK46. cbn in Hk. lia. }
assert (Hrom3 : rom_view rsegs W3 mem3).
{ apply (rm_rom_kept_wr rsegs (m2k_wz cx) W2 W3 mem2 mem3 Hrom HK).
  intros a (sg & Hin & _ & Hr). apply HNW.
  pose proof (m2_segs_low a (ex_intro _ sg (conj Hin Hr))) as Hlow.
  unfold kLowMemEnd in Hlow. lia. }
split; [|exact HRA3].
split; [exact Hcore3|]. split; [exact Hfxk3|]. split; [exact Hfsh3|]. split; [exact Hrom3|].
split; [exact Hpp3|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hpod0|].
split; [exact Hpodin | exact Hpodout].
Qed.

(* ---- the malformed exit, from the state at MAL 0x823fc ---- *)
Lemma m2k_mal : forall (cx : rs_scx rsegs) POST rec (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
@rs_from_MAL fx rc SK rsegs B MT cx POST ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rs_role_at rsegs cx rec W2 mem2 ->
rs_at_cx rsegs cx W2 mem2 regs2
  (rs_L_chk rsegs cx ++ [(LReg 24, -1); (LReg 25, e_F (x_e rsegs cx)); (LReg 27, e_pp (x_e rsegs cx))]) ->
fst (rs_PA rsegs cx rec) = None -> snd (rs_PA rsegs cx rec) = -1 ->
SRr rsegs W2 (@cfg_at fx2 rsegs RS_MAL regs2 mem2 md2) POST.
Proof.
intros cx POST rec fx2 ly2 S2 W2 regs2 mem2 md2 HMAL HCB HRA HAT Hf Hs.
apply (HMAL fx2 ly2 S2 W2 regs2 mem2 md2 rec).
split; [exact HCB|]. split; [exact HAT|]. split; [exact HRA|]. split; [exact Hf | exact Hs].
Qed.


End c.
