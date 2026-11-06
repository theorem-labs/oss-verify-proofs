(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1 (the engine plumbing
   of a segment of a parse walk and its arithmetic lemmas U_subba, U_sext32, U_sext32_eqb, U_next, U_and3, U_off_of,
   U_s8), for reac_headamp_prop_parse_result's pair loop on reac-pw/fuzz_headamp's ASan + UBSan image B, its two
   segments WALK and ADV of lib/AU/HPgParseCut.v; the entry states, exits, the strncmp call inside the frame hole and
   the walks below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/AU/HPgParseW.v at f7ae59d74add (pbW_tcs_ok,
   pbW_loop_stop, pbW_exit_exit, pbW_exit_adv, pbW_exit_key, pbW_exit_wlb, pbW_ret_at, pbW_call, pbW_lb_ok,
   pbW_ret_ok) for image A's segments of lib/A/HPgParseCut.v: image A's pcs, registers, frame cells and literal (the
   inner cuts LAST 0x84994 and RET 0x849cc; a5, s9 = rf and [spa + 40] = keys in place of image B's registers and
   cells; the last body byte by a branch in place of a mask); the call's stop (pw_exit_call), the run of WALK from
   0x84910 (hp_segWALK_A) and the segment ADV (hp_segADV_A) are new. *)
(* reac_headamp_prop_parse_result 0x845b4 of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the two segments of the
   pair loop, WALK 0x84910 and ADV 0x84b00, against lib/A/HPgParseCut.v's segWALK_stmt and segADV_stmt.
   Proves no function (kind: segment lemma).

   WALK 0x84910 .. 0x849e0 (its slow paths 0x84d0c, 0x84d18, 0x84d38, 0x84d48, 0x84d58 are never entered):
     0x84910 lb a0,0(s5); 0x84914 bnez a0,0x84d0c: the instrumented check of the Struct pod at s6 = P + r + 8
       (s5 holds its shadow byte); the shadow entry mkSHE 22 0 8 of the pod's header decides it;
     0x84918 bltu s7,a4 (never taken: r + 16 <= cc), 0x8491c lwu a0,0(s6) (the Struct's value size vs),
       0x84920 bltu a0,a5 (vs < 8), 0x84924 .. 0x8492c bltu a2,a1 (vs - 8 < cc - (r + 16)),
       0x84930 .. 0x8493c the check of the child at s7 = P + cc (a6 holds its shadow byte, shadow entry mkSHE 23 0 8),
       0x84940 lwu a1,0(s7) (the child's size), 0x84944 .. 0x8494c bltu a0,a1
       (r + 8 + vs - cc < the child's size): each test that is taken is spa_pod_is_inside false, and the walk goes to
       EXIT 0x84890 with the fold's state unchanged (hp_walk_pairs at S n is []). When the child's header does not lie
       in the Struct body the walk starts from a state without the child's region (pw_sso) and leaves at the second
       or third test;
     0x84950 bnez s8: the key slot;
     s8 = 0: 0x84954 .. 0x849a8 spa_pod_get_string of the child (size < 2^20, size <> 0, type 8 = String, last body
       byte 0), then ADV with the key slot Some cc or None. The engine cannot run the check of the last body byte
       (its address is s7 + 8 + size - 1, which is no atom), so that byte is the inner cut LAST 0x84994 with the
       address as the atom a0, its own one-byte region and the shadow entry mkSHE 10 0 1;
     s8 <> 0: 0x849b4 sd a6,48(sp) (the child's shadow byte, reloaded after the call), 0x849b8 .. 0x849c4 the
       arguments (a0 = the key text P + ck + 8, a1 = 0x21460 = hi_akey, a2 = 13), 0x849c8 jal 0x41ba4 (the strncmp
       wrapper in the hole form of lib/A/HPgHole.v: hj_strncmp_at with hd_astrncmp_hole at A_TRAMP_STRNCMP); its
       return is the inner cut RET 0x849cc: beqz a0: 0 is KEY 0x849e4, else 0x849d0 .. 0x849e0 (s8 = 0, a4 / a5 / a6
       reloaded) and ADV with the key slot empty (the pair's key has no prefix).
   ADV 0x84b00 .. 0x84b24 with its slow path 0x84d28: the check of the child at s7 (a6 holds its shadow byte),
     0x84b08 lwu a0,0(s7), 0x84b0c .. 0x84b18 s7 += ((size + 7) | 7) + 1 = round_up8 (8 + size), the next child,
     0x84b1c andi a0,s7,3; 0x84b20 beqz a0,0x84910 (always taken: the next child's offset is 0 mod 8).
   Every write of the two segments is the one `sd a6,48(sp)` of WALK and the strncmp wrapper's own 2 ESTACK bytes
   below sp; both lie inside the parse's stack window, away from the thirteen saved words, from out, from res, from
   the errno cell and from the hole's eight shadow bytes, so hp_core's memory part is carried unchanged
   (lib/A/HPgParseGRun.v hgr_stop, lib/A/HPgParseGKit.v hk_core_of_call, lib/A/HPgParseGKey.v hgk_core_keep). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YG0b.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseCut HPgParseGWalk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGKit HPgParseGKey HPgParseGRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation pctx := (@hp_ctx rsegs).

(* ======================================= the entry states ======================================= *)
(* s5 and a6 hold the shadow byte of s6 and of s7: the engine's form of `srli x,r,3; add x,x,s11`. *)
Definition pw_sh (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 27 0).
(* the kit's env (lib/A/HPgParseGKit.v hk_env) gives slot 32 the shadow offset, 33 .. 45 the saved words, 46 fs0;
   WALK and ADV put at 47 the Struct's value size, at 48 the child's size and at 49 the child's type word. *)
Definition pw_r6 : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 47 0))].
Definition pw_r7 : YP09.region :=
YP09.mkRegion (Some 23%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 48 0)); YP09.mkChunk 4 (CVal 4 (SOff 49 0))].
Definition pw_atoms : list (nat * afact) :=
[(22%nat, mkAF 0 (2 ^ 47 - 16) 2); (23%nat, mkAF 0 (2 ^ 47 - 16) 2);
 (47%nat, mkAF 0 (2 ^ 32 - 1) 0); (48%nat, mkAF 0 (2 ^ 32 - 1) 0); (49%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition pw_facts : facts := mkFacts (hk_atoms ++ pw_atoms) [] [].

(* WALK's frame cells at the atoms a, a + 1, a + 2: [spa + 16] (the slow arm's bound), [spa + 32] = P + r + 16 and
   [spa + 40] = keys *)
Definition pw_tcs (a : nat) : list YP09.chunk :=
[YP09.mkChunk 0x10 (CVal 8 (SOff a 0)); YP09.mkChunk 0x20 (CVal 8 (SOff (S a) 0));
 YP09.mkChunk 0x28 (CVal 8 (SOff (S (S a)) 0))].
(* WALK's entry: s5 = the shadow address of s6, a5 = 8; the env's 50 .. 52 are the frame cells. pw_ss when the
   child's header lies in the Struct body, pw_sso (no child region) when it does not. *)
Definition pw_regs_key : list sv := sr_set (sr_set sr_atoms 21%bv (pw_sh 22)) 15%bv (SLit 8).
Definition pw_ss : sstate := mkSS PC_WALK pw_regs_key [hk_temps (pw_tcs 50); pw_r6; pw_r7] None pw_facts.
Definition pw_atoms_o : list (nat * afact) := [(22%nat, mkAF 0 (2 ^ 47 - 16) 2); (47%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition pw_sso : sstate :=
mkSS PC_WALK pw_regs_key [hk_temps (pw_tcs 50); pw_r6] None (mkFacts (hk_atoms ++ pw_atoms_o) [] []).
Definition pw_SH : list shent := [mkSHE 22 0 8; mkSHE 23 0 8].
Definition pw_SH6 : list shent := [mkSHE 22 0 8].

(* ADV's entry state *)
Definition pw_regs_adv : list sv := sr_set sr_atoms 16%bv (pw_sh 23).
Definition pw_SH7 : list shent := [mkSHE 23 0 8].
Definition ss_adv : sstate := mkSS PC_ADV pw_regs_adv [pw_r7] None pw_facts.

(* the inner cut LAST of WALK: the child's last body byte, its address the atom a0; the env's 47 is the byte,
   48 .. 50 the frame cells *)
Definition PC_LAST : Z := 0x84994.
Definition pw_rb : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 47 0))].
Definition pw_atoms_b : list (nat * afact) := [(10%nat, mkAF 0 (2 ^ 47 - 1) 0); (47%nat, mkAF 0 255 0)].
Definition pw_ssb : sstate :=
mkSS PC_LAST sr_atoms [hk_temps (pw_tcs 48); pw_rb] None (mkFacts (hk_atoms ++ pw_atoms_b) [] []).
Definition pw_SHb : list shent := [mkSHE 10 0 1].

(* the inner cut RET of WALK: the return of the strncmp wrapper; the env's 47 .. 49 are the frame cells, 50 the
   child's shadow address at [spa + 48] *)
Definition PC_RET : Z := 0x849cc.
Definition pw_csr : list YP09.chunk := pw_tcs 47 ++ [YP09.mkChunk 0x30 (CVal 8 (SOff 50 0))].
Definition pw_ssr : sstate := mkSS PC_RET sr_atoms [hk_temps pw_csr] None (mkFacts (hk_atoms ++ []) [] []).

(* ======================================= the arithmetic this walk adds ======================================= *)
(* `srliw a0,a1,20` of the sign-extended child size *)
Lemma pw_U_srliw20 : forall E n v, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 ->
U E (SAluw ALU_SRL (SExt true 32 (SOff n 0)) (SLit 20)) = v / 2 ^ 20.
Proof.
intros E n v Hv Hr. rewrite U_of_S, S_SAluw, (hgw_U_sext32 E n v Hv Hr), U_SLit.
assert (Hm : (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)) mod 2 ^ 32 = v).
{ destruct (Z.ltb_spec v (2 ^ 31)); [apply Z.mod_small; lia|].
  replace (v + (2 ^ 64 - 2 ^ 32)) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  apply Z.mod_small. lia. }
rewrite Hm. change (zcanon 20 mod 2 ^ 32) with 20. cbn [zalu_raw]. change (Z.land 20 31) with 20.
rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= v / 2 ^ 20 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* `addi s8,s7,8; add a0,s8,a1; addi a0,a0,-1`: the child's last body byte *)
Lemma pw_U_last : forall E n m v cs, U E (SOff n 0) = v -> U E (SOff m 0) = cs ->
0 <= v -> 1 <= cs < 2 ^ 31 -> v + 8 + cs < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff n 8) (SExt true 32 (SOff m 0))) (SLit (-1))) = v + 8 + cs - 1.
Proof.
intros E n m v cs Hv Hcs H0 Hr Hlt.
rewrite !U_SAlu, (hgw_U_off E n v 8 Hv ltac:(lia)), (hgw_U_sext32 E m cs Hcs ltac:(lia)), U_SLit.
rewrite (proj2 (Z.ltb_lt cs (2 ^ 31))) by lia. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (v + 8 + cs)) by lia. change ((-1) mod 2 ^ 64) with 18446744073709551615.
replace (v + 8 + cs + 18446744073709551615) with ((v + 8 + cs - 1) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* the shadow address in sv_denot form, for the two registers the cut states fix by value *)
Lemma pw_sv_sh : forall E n v, ew E n = w64 v -> ew E 27 = w64 SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
sv_denot E (pw_sh n) = w64 (shadow_addr v).
Proof.
intros E n v Hn H27 Hr. rewrite denot_lit_U. unfold pw_sh.
rewrite (hgw_U_shadow E n v (U_atom E n v Hn ltac:(lia))
  (U_atom E 27 SHADOW_OFF H27 ltac:(unfold SHADOW_OFF; lia)) Hr).
reflexivity.
Qed.

(* ======================================= the engine's plumbing ======================================= *)
Ltac pw_ureg HAE :=
lazymatch goal with |- U ?E (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity) end;
lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
first [constr_eq E0 E1 | rewrite (U_agree k E0 E1 _ HAE) by (vm_compute; reflexivity)] end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis STRNCMP : forall F fc, hd_astrncmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRNCMP.
Hypothesis HBerrno : as_errno B = 0x5d7cac.

(* the registers a chunk keeps, and the value a register holds at a stop *)
Lemma pw_reg_kept : forall (fy : YK11.FPState) (W : world rsegs) (E0 E : env) (ss : sstate) (ms : machine_state)
  (k n : nat) (r : bv 5) (regs2 : bvmap 5 word),
st_ok (fx := fy) rsegs E ss (restrict (w_H W) ms) -> env_agree k E0 E -> (n < k)%nat ->
ew E0 n = getr regs2 r -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = getr regs2 r.
Proof.
intros fy W E0 E ss ms k n r regs2 HS HAE Hn Hew Hsr.
rewrite (st_ok_restrict_reg rsegs (w_H W) E ss ms r HS), Hsr, hk_sv_SOff0, (proj1 HAE n Hn). exact Hew.
Qed.
Lemma pw_reg_U : forall (fy : YK11.FPState) (x : pctx) E ss ms (r : bv 5) v,
st_ok (fx := fy) rsegs E ss (restrict (w_H (hx_W x)) ms) -> U E (sr_get (ss_regs ss) r) = v ->
getr (ms_regs ms) r = w64 v.
Proof.
intros fy x E ss ms r v HS Hv. rewrite (st_ok_restrict_reg rsegs (w_H (hx_W x)) E ss ms r HS), denot_lit_U, Hv.
reflexivity.
Qed.
(* a register the chunk did not touch, at the run's stop *)
Ltac pw_kepta xx rg LL HAEf nn rr :=
lazymatch goal with
| HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  apply (pw_reg_kept _ _ (hk_env xx rg LL) _ ssf msf 50 nn (rr : bv 5) rg HSf HAEf ltac:(lia)
    (hk_env_reg xx rg LL nn (rr : bv 5) eq_refl) ltac:(vm_compute; reflexivity))
end.
Ltac pw_keptr xx rg LL HAEf nn rr :=
lazymatch goal with
| HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  rewrite (pw_reg_kept _ _ (hk_env xx rg LL) _ ssf msf 50 nn (rr : bv 5) rg HSf HAEf ltac:(lia)
    (hk_env_reg xx rg LL nn (rr : bv 5) eq_refl) ltac:(vm_compute; reflexivity))
end.

(* the memory a chunk without a write window leaves *)
Lemma pw_mem_ro : forall (E : env) (rs : smem) (m m' : word -> option byte),
frame_of E rs m m' -> (forall r, In r rs -> r_whi r <= r_wlo r) -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros z. apply HF.
intros (rr & Hr & Hb). pose proof (Hro rr Hr). lia.
Qed.

(* ======================================= ADV 0x84b00 ======================================= *)
Theorem hp_segADV_A : segADV_stmt B MT.
Proof.
unfold segADV_stmt. intros x r cc n ko cl keys rf HCALL HWALK HEXIT F fc regs2 mem2 md2 HADV.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
pose proof HADV as (HC & HFX & HM & HLOOP & HA45 & R23 & R24 & R25 & R16).
pose proof HM as (Hnull & HSTOK & Hcc1 & Hcc8 & Hin & Hfuel & Hko & HST & HRES).
pose proof HLOOP as (L20 & L21 & L22 & L16c & L32c & L40c).
pose proof HA45 as (A14 & A15).
pose proof HSTOK as (Hr16 & Hr8 & Hvs20 & Hrvs).
pose proof (hk_pod B x HCALL Hnull) as
  (HP0 & HP16 & Hl8 & Hl64 & HSZ & HP63 & HGc & HInb & HOdj & HRdj & HEdj & HRAc & HHVc & HAM & HOS).
pose proof (hk_stack B x HCALL) as
  (Sceil & Slo & Sw1 & Ssp & Ssp0 & Shi & Sal & Sal0 & Spa32 & Spa1 & Sfr & Sfrlo & Sfrhi).
pose proof (hgk_pod_at B pa_segs_low errno_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2
  HCALL Hnull ltac:(exact (proj1 HST)) HC) as (HG & HRA & HHV).
pose proof (hk_core_cregs B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 HC) as HCR.
pose proof (hk_core_journal B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 HC) as (HJ & HOK & HPAT).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RTY.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
pose proof (hgw_inside_bounds (hx_bs x) (r + 16) (hp_vs x r) cc Hin) as (Ib1 & Ib2 & Ib3).
pose proof asan_consts as (AC & C2 & C3 & C4 & C5).
assert (Hccl : cc + 8 + Spa.u32_at (hx_bs x) cc <= hx_len x) by (unfold hp_vs in *; lia).
assert (HPcc : 0 <= hx_P x + cc <= 2 ^ 47 - 16)
  by (destruct HAM as [HA|[HA1 HA2]]; unfold kLowMemEnd, kHighMemEnd, hx_len in *; lia).
assert (HPr : 0 <= hx_P x + r + 8 <= 2 ^ 47 - 16)
  by (destruct HAM as [HA|[HA1 HA2]]; unfold kLowMemEnd, kHighMemEnd, hx_len in *; lia).
pose proof HCR as (C2r & C8r & C3r & C4r & C9r & C18r & C19r & C26r & C27r).
set (L := [w64 (hp_vs x r); w64 (Spa.u32_at (hx_bs x) cc); w64 (Spa.u32_at (hx_bs x) (cc + 4))]) in *.
set (E0 := hk_env x regs2 L) in *.
assert (W27 : ew E0 27 = w64 SHADOW_OFF) by (subst E0; rewrite (hk_env_reg x regs2 L 27 27%bv eq_refl); exact C27r).
assert (W23 : ew E0 23 = w64 (hx_P x + cc)) by (subst E0; rewrite (hk_env_reg x regs2 L 23 23%bv eq_refl); exact R23).
assert (W22 : ew E0 22 = w64 (hx_P x + r + 8))
  by (subst E0; rewrite (hk_env_reg x regs2 L 22 22%bv eq_refl); exact L22).
assert (W47 : ew E0 47 = w64 (hp_vs x r)) by (subst E0; exact (hk_env_seg x regs2 L 0)).
assert (W48 : ew E0 48 = w64 (Spa.u32_at (hx_bs x) cc)) by (subst E0; exact (hk_env_seg x regs2 L 1)).
assert (W49 : ew E0 49 = w64 (Spa.u32_at (hx_bs x) (cc + 4))) by (subst E0; exact (hk_env_seg x regs2 L 2)).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply U_atom; [exact W23 | lia]).
assert (U27 : U E0 (SOff 27 0) = SHADOW_OFF) by (apply U_atom; [exact W27 | unfold SHADOW_OFF; lia]).
assert (U48 : U E0 (SOff 48 0) = Spa.u32_at (hx_bs x) cc) by (apply U_atom; [exact W48 | lia]).
(* the entry state *)
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 ss_adv
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs2 (Z_to_bv 64 PC_ADV) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_adv. apply (entry_st_ok_full rsegs).
  - apply regs_ok_pin; [apply regs_ok_Ereg | vm_compute; discriminate |].
    rewrite R16. symmetry. apply (pw_sv_sh E0 23 (hx_P x + cc) W23 W27 ltac:(lia)).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pw_r7.
    apply (hm_ro_region rsegs E0 (w_H (hx_W x)) mem2 23 (hx_P x + cc) 0 8);
    [rewrite W23; unfold w64; apply unsigned_lit_small; lia | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs E0 _ (hx_P x + cc) 0 4 (SOff 48 0) (Spa.u32_at (hx_bs x) cc));
      [rewrite hk_sv_SOff0, W48; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) cc HG); unfold hx_len in *; lia.
    + apply (chunk_ok_val rsegs E0 _ (hx_P x + cc) 4 4 (SOff 49 0) (Spa.u32_at (hx_bs x) (cc + 4)));
      [rewrite hk_sv_SOff0, W49; reflexivity | cbn; lia | cbn; lia |].
      replace (hx_P x + cc + 4) with (hx_P x + (cc + 4)) by lia.
      apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (cc + 4) HG); unfold hx_len in *; lia.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms]. unfold pw_facts.
    apply (hk_atoms_ok B x regs2 L pw_atoms HCALL HCR).
    fold E0. unfold pw_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite W22, W23, W47, W48, W49. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    assert ((hx_P x + cc) mod 4 = 0) by (Z.div_mod_to_equations; lia).
    assert ((hx_P x + r + 8) mod 4 = 0) by (Z.div_mod_to_equations; lia).
    repeat split; try lia. }
assert (SHOK : sh_ok rsegs hk_Bx pw_SH7 E0 (hx_rd x mem2)).
{ unfold pw_SH7, hk_Bx. apply Forall_cons; [|apply Forall_nil].
  apply (hk_shent_pod B x (w_H (hx_W x)) mem2 E0 23 cc 0 8 HCALL Hnull W27 W23 HRA);
  unfold hp_vs in *; lia. }
unfold cfg_at. change (w64 PC_ADV) with (Z_to_bv 64 PC_ADV).
assert (HAE : env_agree 50 (hk_env x regs2 L) E0) by (unfold E0; apply env_agree_refl).
aj_run_tokH pa_tbl_ok HS HJ SHOK hk_Bspan.
{ unfold ss_adv. cbn [ss_mem]. apply awr_okH_cons_ro; [unfold pw_r7; cbn [YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_okH_nil. }
assert (Hmem : ms_mem ms = mem2).
{ apply (pw_mem_ro E0 (ss_mem ss_adv) mem2); [exact HF|].
  intros rr Hr. unfold ss_adv in Hr. cbn [ss_mem] in Hr. destruct Hr as [<-|[]].
  unfold pw_r7. cbn [YP09.r_wlo YP09.r_whi]. lia. }
(* the alignment test at 0x84b20 *)
pose proof (hgw_next_bounds x r cc HSTOK Hcc1 Hcc8 Hin) as (Nb1 & Nb2 & Neq).
assert (Unext : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 23 0) (SAlu ALU_OR (SOff 48 7) (SLit 7))) (SLit 1)) =
  hx_P x + hp_next x cc).
{ rewrite (hgw_U_next E0 23 48 (hx_P x + cc) (Spa.u32_at (hx_bs x) cc) U23 U48 ltac:(lia) ltac:(lia));
  unfold hp_next in *; lia. }
assert (Un4 : (hx_P x + hp_next x cc) mod 4 = 0) by (Z.div_mod_to_equations; lia).
srr_branch_tok pa_tbl_ok HS SHOK hk_Bspan.
2:{ (* the next child is 8-aligned, so the test is never false *)
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hbr end.
  exfalso. rewrite branch_eq_U in Hbr.
  rewrite (hgw_U_and3 E0 _ _ Unext Un4), U_lit in Hbr by lia. discriminate Hbr. }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hbr end.
aj_run_to_tokH pa_tbl_ok HS HJ SHOK hk_Bspan PC_WALK.
{ cbn [ss_mem add_cond]. unfold ss_adv. cbn [ss_mem].
  apply awr_okH_cons_ro; [unfold pw_r7; cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_okH_nil. }
lazymatch goal with
| HSf : st_ok _ _ ?ssf (restrict _ ?msf), HFf : frame_of _ ?rsf (ms_mem ms) (ms_mem ?msf) |- _ =>
  assert (Hmem2 : ms_mem msf = mem2) by
   (rewrite <- Hmem; apply (pw_mem_ro E0 rsf (ms_mem ms));
    [exact HFf
    | intros rr Hr; cbn [ss_mem add_cond] in Hr; unfold ss_adv in Hr; cbn [ss_mem] in Hr;
      destruct Hr as [<-|[]]; unfold pw_r7; cbn [YP09.r_wlo YP09.r_whi]; lia]);
  assert (Hpc : ss_pc ssf = PC_WALK) by (vm_compute; reflexivity);
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E0 ssf msf HSf ltac:(vm_compute; reflexivity)), Hpc;
  rewrite Hmem2 in *
end.
lazymatch goal with
| HSf : st_ok _ _ ?ssf (restrict _ ?msf) |- _ =>
  apply (HWALK (hp_next x cc) F fc (ms_regs msf) mem2);
  split;
  [ apply (hgk_core_keep B pa_segs_low errno_low x PAT_KEY PAT_KEY cl (ha_res_bytes 0 0 0)
      regs2 mem2 md2 (ms_regs msf) mem2 _ (fun _ : Z => False) HCALL ltac:(exact (proj1 HST)) ltac:(cbn; lia) HC)
  | ]
end.
- lazymatch goal with HJf : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    split; [exact HJf|]; split; [exact HOK | exact HPAT] end.
- apply same_io_with_vm_backing.
- intros a Ha _. reflexivity.
- intros a [].
- pose proof (hk_core_cells B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 HC) as (_ & _ & HE). exact HE.
- pw_kepta x regs2 L HAE 2%nat (2%bv : bv 5).
- pw_kepta x regs2 L HAE 8%nat (8%bv : bv 5).
- pw_kepta x regs2 L HAE 3%nat (3%bv : bv 5).
- pw_kepta x regs2 L HAE 4%nat (4%bv : bv 5).
- pw_kepta x regs2 L HAE 9%nat (9%bv : bv 5).
- pw_kepta x regs2 L HAE 18%nat (18%bv : bv 5).
- pw_kepta x regs2 L HAE 19%nat (19%bv : bv 5).
- pw_kepta x regs2 L HAE 26%nat (26%bv : bv 5).
- pw_kepta x regs2 L HAE 27%nat (27%bv : bv 5).
- split; [exact HFX|].
  split; [exact (hgw_adv_walk x r cc n ko cl keys rf HM)|].
  split.
  { unfold pa_loop.
    pw_keptr x regs2 L HAE 20%nat (20%bv : bv 5). pw_keptr x regs2 L HAE 21%nat (21%bv : bv 5). pw_keptr x regs2 L HAE 22%nat (22%bv : bv 5).
    split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
    split; [exact L16c|]. split; [exact L32c | exact L40c]. }
  split.
  { unfold pa_a45. pw_keptr x regs2 L HAE 14%nat (14%bv : bv 5). pw_keptr x regs2 L HAE 15%nat (15%bv : bv 5).
    split; [exact A14 | exact A15]. }
  split.
  { lazymatch goal with HSf : st_ok _ ?EE ?ssf (restrict _ ?msf) |- _ =>
      apply (pw_reg_U (mkFP F fc) x EE ssf msf (23%bv : bv 5)); [exact HSf | pw_ureg HAE; exact Unext] end. }
  split.
  { pw_keptr x regs2 L HAE 24%nat (24%bv : bv 5). exact R24. }
  pw_keptr x regs2 L HAE 25%nat (25%bv : bv 5). exact R25.
Qed.

(* ======================================= WALK 0x84910 ======================================= *)
(* ---------------------------------- the two inner cuts ---------------------------------- *)
(* LAST 0x84994: a String-sized child (size in [1, 2^20), type 8) with the key slot empty; s8 = s7 + 8, a0 = the
   address s7 + 8 + size - 1 of its last body byte, a6 = the shadow address of s7.
   RET 0x849cc: strncmp's return for the pending key ck; a0 = 0 exactly when the key has the prefix. *)
Definition LAST_at (x : pctx) (r cc : Z) (n : nat) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_walk x r cc (S n) None cl keys rf /\
hp_child_in x r cc /\ 1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 /\ Spa.u32_at (hx_bs x) (cc + 4) = 8 /\
pa_loop x r cl keys regs mem /\ pa_a45 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hx_P x + cc + 8) /\ getr regs 25 = w64 rf /\
getr regs 16 = w64 (shadow_addr (hx_P x + cc)) /\
getr regs 10 = w64 (hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc - 1).

Definition LAST_ok (x : pctx) (r cc : Z) (n : nat) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, LAST_at x r cc n cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_LAST regs mem md) (PPOST B MT x).

Definition RET_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\
hp_m_walk x r cc (S n) (Some ck) cl keys rf /\ hp_child_in x r cc /\ pa_loop x r cl keys regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hx_P x + ck + 8) /\ getr regs 25 = w64 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) /\
(getr regs 10 = w64 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true).

Definition RET_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, RET_at x r cc n ck cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_RET regs mem md) (PPOST B MT x).

(* ---------------------------------- the frame cells and the pair loop's state at a stop ---------------------------------- *)
Lemma pw_tcs_ok : forall (x : pctx) regs mem L r cl keys (a : nat), pa_loop x r cl keys regs mem ->
ew (hk_env x regs L) a = w64 ((hx_P x + r + 8) mod 8 + 3) -> ew (hk_env x regs L) (S a) = w64 (hx_P x + r + 16) ->
ew (hk_env x regs L) (S (S a)) = w64 keys ->
0 <= (hx_P x + r + 8) mod 8 + 3 < 2 ^ 64 -> 0 <= hx_P x + r + 16 < 2 ^ 64 -> 0 <= keys < 2 ^ 64 ->
Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) (pw_tcs a).
Proof.
intros x regs mem L r cl keys a (_ & _ & _ & L16 & L32 & L40) E1 E2 E3 R1 R2 R3. unfold pw_tcs.
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val rsegs _ _ _ 0x10 8 (SOff a 0) ((hx_P x + r + 8) mod 8 + 3));
  [rewrite hk_sv_SOff0, E1; reflexivity | cbn; lia | lia | exact L16].
- apply (chunk_ok_val rsegs _ _ _ 0x20 8 (SOff (S a) 0) (hx_P x + r + 16));
  [rewrite hk_sv_SOff0, E2; reflexivity | cbn; lia | lia | exact L32].
- apply (chunk_ok_val rsegs _ _ _ 0x28 8 (SOff (S (S a)) 0) keys);
  [rewrite hk_sv_SOff0, E3; reflexivity | cbn; lia | lia | exact L40].
Qed.

Lemma pw_loop_stop : forall F fc (x : pctx) r cl keys E ss ms cs v1 v2 v3,
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
pa_loop x r cl keys (ms_regs ms) (ms_mem ms).
Proof.
intros F fc x r cl keys E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3.
split; [exact (hgr_reg_U F fc E ss ms _ 20%bv _ HS U20)|].
split; [exact (hgr_reg_U F fc E ss ms _ 21%bv _ HS U21)|].
split; [exact (hgr_reg_U F fc E ss ms _ 22%bv _ HS U22)|].
split; [exact (hgr_temps_val F fc x E ss ms cs 0x10 v1 _ HS Hin U2 C1 V1)|].
split; [exact (hgr_temps_val F fc x E ss ms cs 0x20 v2 _ HS Hin U2 C2 V2)|].
exact (hgr_temps_val F fc x E ss ms cs 0x28 v3 _ HS Hin U2 C3 V3).
Qed.

(* ---------------------------------- the stops of WALK at a cut ---------------------------------- *)
(* EXIT 0x84890: the child at cc is not inside the Struct body *)
Lemma pw_exit_exit : forall F fc (x : pctx) r cc n ko cl keys rf regs mem md L E ss ms md2 k cs v3,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_walk x r cc (S n) ko cl keys rf ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_EXIT ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> hgr_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) -> U E (sr_get (ss_regs ss) 25%bv) = rf ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
EXIT_ok B MT x -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ko cl keys rf regs mem md L E ss ms md2 k cs v3 Hc HC Hfx HM HS Hrv Hpc HAE Hk Hfix U20 U25
  Hin U2 C3 V3 Hout HJ Hio KM HEXIT.
pose proof HM as (_ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (hgr_cfg_stop F fc E ss ms _ PC_EXIT md2 HS Hrv Hpc).
apply (HEXIT cl keys rf F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (hgr_stop B pa_segs_low F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k errno_low Hc HC ltac:(lia)
  eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact (proj1 Hfx)|]. split; [exact (hgw_walk_exit x r cc n ko cl keys rf HM Hout)|].
split; [exact (hgr_reg_U F fc E ss ms _ 20%bv _ HS U20)|].
split; [exact (hgr_reg_U F fc E ss ms _ 25%bv _ HS U25)|].
exact (hgr_temps_val F fc x E ss ms cs 0x28 v3 _ HS Hin U2 C3 V3).
Qed.

(* ADV 0x84b00 with the key slot ko' *)
Lemma pw_exit_adv : forall F fc (x : pctx) r cc n ko' cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_adv x r cc n ko' cl keys rf ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_ADV ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> hgr_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 15%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hp_keyv x ko' ->
U E (sr_get (ss_regs ss) 25%bv) = rf -> U E (sr_get (ss_regs ss) 16%bv) = shadow_addr (hx_P x + cc) ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
ADV_ok B MT x r cc n ko' cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ko' cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 Hc HC Hfx HM HS Hrv Hpc HAE Hk Hfix
  U20 U21 U22 U14 U15 U23 U24 U25 U16 Hin U2 C1 V1 C2 V2 C3 V3 HJ Hio KM HADV.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (hgr_cfg_stop F fc E ss ms _ PC_ADV md2 HS Hrv Hpc).
apply (HADV F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (hgr_stop B pa_segs_low F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k errno_low Hc HC ltac:(lia)
  eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|].
split; [exact (pw_loop_stop F fc x r cl keys E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (hgr_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (hgr_reg_U F fc E ss ms _ 15%bv _ HS U15)]|].
split; [exact (hgr_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (hgr_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact (hgr_reg_U F fc E ss ms _ 25%bv _ HS U25)|].
exact (hgr_reg_U F fc E ss ms _ 16%bv _ HS U16).
Qed.

(* KEY 0x849e4: strncmp returned 0 *)
Lemma pw_exit_key : forall F fc (x : pctx) r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_key x r cc n ck cl keys rf ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_KEY ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> hgr_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hx_P x + ck + 8 ->
U E (sr_get (ss_regs ss) 25%bv) = rf ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
In (YP09.mkChunk 0x30 (CVal 8 v4)) cs -> U E v4 = shadow_addr (hx_P x + cc) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
KEY_ok B MT x r cc n ck cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4 Hc HC Hfx HM HS Hrv Hpc HAE Hk Hfix
  U20 U21 U22 U23 U24 U25 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 HJ Hio KM HKEY.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (hgr_cfg_stop F fc E ss ms _ PC_KEY md2 HS Hrv Hpc).
apply (HKEY F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (hgr_stop B pa_segs_low F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k errno_low Hc HC ltac:(lia)
  eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|].
split; [exact (pw_loop_stop F fc x r cl keys E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [exact (hgr_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (hgr_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact (hgr_reg_U F fc E ss ms _ 25%bv _ HS U25)|].
exact (hgr_temps_val F fc x E ss ms cs 0x30 v4 _ HS Hin U2 C4 V4).
Qed.

(* LAST 0x84994 *)
Lemma pw_exit_last : forall F fc (x : pctx) r cc n cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_walk x r cc (S n) None cl keys rf -> hp_child_in x r cc ->
1 <= Spa.u32_at (hx_bs x) cc < 2 ^ 20 -> Spa.u32_at (hx_bs x) (cc + 4) = 8 ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_LAST ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> hgr_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 14%bv) = hx_P x + r + 16 -> U E (sr_get (ss_regs ss) 15%bv) = 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hx_P x + cc + 8 ->
U E (sr_get (ss_regs ss) 25%bv) = rf -> U E (sr_get (ss_regs ss) 16%bv) = shadow_addr (hx_P x + cc) ->
U E (sr_get (ss_regs ss) 10%bv) = hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc - 1 ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
LAST_ok x r cc n cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 Hc HC Hfx HM Hci Hcs Hty HS Hrv Hpc HAE Hk
  Hfix U20 U21 U22 U14 U15 U23 U24 U25 U16 U10 Hin U2 C1 V1 C2 V2 C3 V3 HJ Hio KM HLB.
pose proof HM as (_ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (hgr_cfg_stop F fc E ss ms _ PC_LAST md2 HS Hrv Hpc).
apply (HLB F fc (ms_regs ms) (ms_mem ms) md2).
split; [exact (hgr_stop B pa_segs_low F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k errno_low Hc HC ltac:(lia)
  eq_refl HS HAE Hk Hfix HJ Hio KM)|].
split; [exact Hfx|]. split; [exact HM|]. split; [exact Hci|]. split; [exact Hcs|]. split; [exact Hty|].
split; [exact (pw_loop_stop F fc x r cl keys E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)|].
split; [split; [exact (hgr_reg_U F fc E ss ms _ 14%bv _ HS U14) | exact (hgr_reg_U F fc E ss ms _ 15%bv _ HS U15)]|].
split; [exact (hgr_reg_U F fc E ss ms _ 23%bv _ HS U23)|].
split; [exact (hgr_reg_U F fc E ss ms _ 24%bv _ HS U24)|].
split; [exact (hgr_reg_U F fc E ss ms _ 25%bv _ HS U25)|].
split; [exact (hgr_reg_U F fc E ss ms _ 16%bv _ HS U16)|].
exact (hgr_reg_U F fc E ss ms _ 10%bv _ HS U10).
Qed.

(* ---------------------------------- the strncmp call (0x849c8 jal 0x41ba4) ---------------------------------- *)
Ltac pw_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

(* the cut RET from strncmp's post *)
Lemma pw_ret_at : forall (x : pctx) r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 -> hp_fxw F fc ->
hp_m_walk x r cc (S n) (Some ck) cl keys rf -> hp_child_in x r cc -> pa_loop x r cl keys regsT memT ->
getr regsT 23 = w64 (hx_P x + cc) -> getr regsT 24 = w64 (hx_P x + ck + 8) -> getr regsT 25 = w64 rf ->
val_mem rsegs (hx_rd x memT) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
aregs_preserved regsT regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) ->
 aview rsegs (w_H (hx_W x)) mem2 a = aview rsegs (w_H (hx_W x)) memT a) ->
(getr regs2 10 = w64 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true) ->
RET_at x r cc n ck cl keys rf F fc regs2 mem2 md2.
Proof.
intros x r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2 Hc HC Hfx HW Hin (L20 & L21 & L22 & L16 & L32 & L40)
  R23 R24 R25 H48 HP HK H10.
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
assert (KV : forall o (k : nat) v, 0 <= o <= 0x40 -> (k <= 8)%nat ->
  val_mem rsegs (hx_rd x memT) (hx_spa x + o) k v -> val_mem rsegs (hx_rd x mem2) (hx_spa x + o) k v).
{ intros o k v Ho Hk Hv. apply (val_mem_kept rsegs (w_H (hx_W x)) (w_H (hx_W x)) memT mem2); [|exact Hv].
  intros j Hj. apply HK; lia. }
split; [exact HC|]. split; [exact Hfx|]. split; [exact HW|]. split; [exact Hin|]. split.
{ unfold pa_loop. rewrite (hgr_pres regsT regs2 20%bv HP ltac:(pw_acs)), (hgr_pres regsT regs2 21%bv HP ltac:(pw_acs)),
    (hgr_pres regsT regs2 22%bv HP ltac:(pw_acs)).
  split; [exact L20|]. split; [exact L21|]. split; [exact L22|].
  split; [exact (KV 16 8%nat _ ltac:(lia) ltac:(lia) L16)|]. split; [exact (KV 32 8%nat _ ltac:(lia) ltac:(lia) L32)|].
  exact (KV 40 8%nat _ ltac:(lia) ltac:(lia) L40). }
rewrite (hgr_pres regsT regs2 23%bv HP ltac:(pw_acs)), (hgr_pres regsT regs2 24%bv HP ltac:(pw_acs)),
  (hgr_pres regsT regs2 25%bv HP ltac:(pw_acs)).
split; [exact R23|]. split; [exact R24|]. split; [exact R25|].
split; [exact (KV 48 8%nat _ ltac:(lia) ltac:(lia) H48) | exact H10].
Qed.

Lemma pw_call : forall (x : pctx) r cc n ck cl keys rf F fc regsT memT mdT,
call_ok B x ->
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regsT memT mdT -> hp_fxw F fc ->
hp_m_walk x r cc (S n) (Some ck) cl keys rf -> hp_child_in x r cc -> pa_loop x r cl keys regsT memT ->
getr regsT 23 = w64 (hx_P x + cc) -> getr regsT 24 = w64 (hx_P x + ck + 8) -> getr regsT 25 = w64 rf ->
getr regsT 10 = w64 (hx_P x + ck + 8) -> getr regsT 11 = w64 0x21460 -> getr regsT 12 = w64 13 ->
getr regsT 1 = w64 PC_RET ->
val_mem rsegs (hx_rd x memT) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
RET_ok x r cc n ck cl keys rf ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRNCMP regsT memT mdT) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf F fc regsT memT mdT Hc HC Hfx HW Hin HL R23 R24 R25 R10 R11 R12 R1 H48 HRET.
pose proof HW as (Hnull & Hst & Hcc & Hc8 & Hn & HK & Hs & _).
pose proof (HK ck eq_refl) as HKo. pose proof HKo as (Hck0 & Hckl & _).
pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof Hs as (Hcl & _ & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hk_call_regs B x Hc) as (_ & _ & _ & _ & _ & _ & _ & Hgp & Htp).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_KEY cl _ regsT memT mdT errno_low Hc Hnull HC ltac:(lia))
  as (HG & HRA & HHV).
destruct (hgw_key_bytes x ck HKo) as (Hnz & Hkl1 & Hkl2 & _ & _).
pose proof (hgw_key_garr8 (hx_rd x memT) x ck HG HKo) as HKG.
destruct (hgw_strncmp_prefix (hp_kstr x ck) Hnz) as (d & Hd & Hdr & Hdp).
assert (Hsp : spZ regsT = hx_spa x) by (unfold spZ; rewrite C2; unfold w64; apply unsigned_lit_small; lia).
(* the key, a C string in the pod *)
assert (Hoffk : hd_off_stack regsT (2 * ESTACK) (hx_P x) (hx_len x)).
{ apply (hk_off_stack_sub (hx_regs x) regsT T_parse_STK (2 * ESTACK) (hx_P x) (hx_len x) _ _ HOFF);
  [rewrite Hsp; unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia | rewrite Hsp; unfold hx_sp in *; lia
  | lia | lia]. }
assert (Htlk : hd_str_tail (aview rsegs (w_H (hx_W x)) memT) (hx_P x + ck + 8 + Z.of_nat (length (hp_kstr x ck)))).
{ apply (hgw_str_tail (w_H (hx_W x)) memT (hx_P x) (hd_zbytes (hx_bs x)) _ HG);
  unfold hd_zbytes; rewrite ?length_map; unfold hx_len in *; [Z.div_mod_to_equations; lia | exact Hl8m | lia]. }
destruct (hk_awrap_sub (hx_W x) regsT memT (hx_P x) (hx_len x) (hx_P x + ck + 8) (hp_kstr x ck) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) HAM HRA HHV Hoffk HKG Hnz Htlk) as [Hx Hmx].
(* the literal "reac.headamp." at 0x21460 *)
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & Hkey0 & _).
assert (Eakey : hi_akey headamp_himg_A = 0x21460) by reflexivity.
rewrite Eakey in Hkey0.
assert (Hkey : hd_cstr rsegs (w_H (hx_W x)) memT 0x21460 (hd_zbytes Headamp.HA_PREFIX)).
{ apply (hk_cstr_at_cut B pa_segs_low x PAT_KEY cl _ regsT memT mdT _ _ errno_low Hc HC ltac:(lia)
    ltac:(reflexivity) Hkey0).
  intros i Hi. unfold hd_zbytes in Hi. rewrite length_map, hgw_prefix_len in Hi. rewrite HBerrno. lia. }
assert (Hoffy : hd_off_stack regsT (2 * ESTACK) 0x21460 (Z.of_nat (length Headamp.HA_PREFIX) + 1)).
{ intros b Hb Hw. rewrite hgw_prefix_len in Hb. rewrite Hsp in Hw.
  pose proof (hk_window_band B x b Hc ltac:(unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)) as Hwb.
  pose proof alloc_ceiling_value as [[AC1 AC2] _]. lia. }
destruct (hk_awrap_cstr pa_segs_low (hx_W x) regsT memT 0x21460 Headamp.HA_PREFIX Hkey Hoffy) as [Hy Hmy].
(* the read-only image bytes the wrapper reads *)
assert (Hro : forall a, in_rom rsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview rsegs (w_H (hx_W x)) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a))).
{ exact (hk_aro_at_cut B pa_segs_low x PAT_KEY cl _ regsT memT mdT Hc HC ltac:(lia)). }
pose proof HS as (_ & _ & S3 & S4 & _ & _ & S7 & S8 & S9 & S10 & _).
assert (Ho16 : (hx_spa x - hx_sp0 x) mod 16 = 0) by (clear - S8 S9; Z.div_mod_to_equations; lia).
assert (Hbud : 2 * ESTACK - (hx_spa x - hx_sp0 x) <= hx_STK x)
by (clear - S3 S10; unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia).
assert (Hsp' : spZ regsT = hx_sp0 x + (hx_spa x - hx_sp0 x)) by (rewrite Hsp; lia).
assert (Hneg : hx_spa x - hx_sp0 x <= 0) by (unfold hx_sp in *; lia).
assert (Hgp' : getr regsT 3 = w64 (as_gp B)) by (rewrite C3; exact Hgp).
assert (Htp' : getr regsT 4 = w64 (as_tp B)) by (rewrite C4; exact Htp).
assert (Hraw : YK0s.ret_ok (w64 PC_RET)) by (apply ret_ok_even; vm_compute; reflexivity).
eapply SRr_bind.
{ exact (hj_strncmp_at (fx := mkFP F fc) rsegs B pa_segs_low A_TRAMP_STRNCMP (STRNCMP F fc) (hx_W x) regsT memT
    (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x)
    (hx_Sc x) mdT (hx_k x) (hx_P x + ck + 8) 0x21460 13 (hp_kstr x ck) Headamp.HA_PREFIX d (hx_spa x - hx_sp0 x)
    (w64 PC_RET) (hx_fr x) PAT_KEY (proj1 HC) R10 R11 R12 ltac:(lia) Hsp' Ho16 Hneg Hbud Hgp' Htp' R1 Hraw
    Hx Hy Hmx Hmy Hd Hro). }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hio2 & (v & Hv & Hvd) & HK2 & Hpres2).
assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) ->
  aview rsegs (w_H (hx_W x)) mem2 a = aview rsegs (w_H (hx_W x)) memT a).
{ intros a Ha Hw. apply HK2; [exact Ha|]. replace (hx_sp0 x + (hx_spa x - hx_sp0 x)) with (hx_spa x) by lia. exact Hw. }
pose proof alloc_ceiling_value as [[AC1 AC2] _].
assert (Herr2 : exists ev', rd32 (hx_view x mem2) (as_errno B) ev').
{ destruct (hk_core_cells B x _ _ _ _ _ _ HC) as (_ & _ & (ev' & Hev)). exists ev'.
  apply (hk_rd32_kept (hx_view x memT)); [|exact Hev].
  intros j Hj. unfold hx_view. apply HK2'; rewrite HBerrno; [lia|].
  pose proof (hk_window_band B x (hx_spa x - 2 * ESTACK) Hc
    ltac:(unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia)).
  lia. }
assert (HC2 : hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2).
{ apply (hk_core_of_call B pa_segs_low x PAT_KEY cl _ regsT memT mdT regs2 mem2 md2 errno_low Hc HC ltac:(lia)
    ltac:(reflexivity) HJ2 HP2 Hio2); [|exact Herr2].
  intros a Ha Hw _ _. unfold hx_view. apply HK2'; [exact Ha|]. intros Hw'. apply Hw. unfold ESTACK in *. lia. }
apply (HRET F fc regs2 mem2 md2).
apply (pw_ret_at x r cc n ck cl keys rf F fc regsT memT regs2 mem2 md2 Hc HC2 Hfx HW Hin HL R23 R24 R25 H48 HP2 HK2').
rewrite Hv. split; intros H0; [apply Hdp, Hvd, H0 | apply Hvd, Hdp, H0].
Qed.

(* the call at its stop: the run from WALK ends at the trampoline 0x41ba4 *)
Lemma pw_exit_call : forall F fc (x : pctx) r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4,
call_ok B x -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F fc ->
hp_m_walk x r cc (S n) (Some ck) cl keys rf -> hp_child_in x r cc ->
st_ok (fx := mkFP F fc) rsegs E ss (restrict (w_H (hx_W x)) ms) -> ss_resv ss = None ->
ss_pc ss = A_TRAMP_STRNCMP ->
env_agree k (hk_env x regs L) E -> (28 <= k)%nat -> hgr_fixed (ss_regs ss) ->
U E (sr_get (ss_regs ss) 20%bv) = Z.of_nat (length cl) ->
U E (sr_get (ss_regs ss) 21%bv) = shadow_addr (hx_P x + r + 8) ->
U E (sr_get (ss_regs ss) 22%bv) = hx_P x + r + 8 ->
U E (sr_get (ss_regs ss) 23%bv) = hx_P x + cc -> U E (sr_get (ss_regs ss) 24%bv) = hx_P x + ck + 8 ->
U E (sr_get (ss_regs ss) 25%bv) = rf ->
U E (sr_get (ss_regs ss) 10%bv) = hx_P x + ck + 8 -> U E (sr_get (ss_regs ss) 11%bv) = 0x21460 ->
U E (sr_get (ss_regs ss) 12%bv) = 13 -> U E (sr_get (ss_regs ss) 1%bv) = PC_RET ->
In (hk_temps cs) (ss_mem ss) -> bv_unsigned (ew E 2) = hx_spa x ->
In (YP09.mkChunk 0x10 (CVal 8 v1)) cs -> U E v1 = (hx_P x + r + 8) mod 8 + 3 ->
In (YP09.mkChunk 0x20 (CVal 8 v2)) cs -> U E v2 = hx_P x + r + 16 ->
In (YP09.mkChunk 0x28 (CVal 8 v3)) cs -> U E v3 = keys ->
In (YP09.mkChunk 0x30 (CVal 8 v4)) cs -> U E v4 = shadow_addr (hx_P x + cc) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) (ms_mem ms)) md2 (hx_k x) ->
same_io md md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
 hx_rd x (ms_mem ms) (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
RET_ok x r cc n ck cl keys rf -> SRr rsegs (hx_W x) (mkCfg ms md2) (PPOST B MT x).
Proof.
intros F fc x r cc n ck cl keys rf regs mem md L E ss ms md2 k cs v1 v2 v3 v4 Hc HC Hfx HM Hci HS Hrv Hpc HAE Hk
  Hfix U20 U21 U22 U23 U24 U25 U10 U11 U12 U1 Hin U2 C1 V1 C2 V2 C3 V3 C4 V4 HJ Hio KM HRET.
pose proof HM as (_ & _ & _ & _ & _ & _ & (Hcl & _ & _) & _).
rewrite (hgr_cfg_stop F fc E ss ms _ A_TRAMP_STRNCMP md2 HS Hrv Hpc).
apply (pw_call x r cc n ck cl keys rf F fc (ms_regs ms) (ms_mem ms) md2 Hc
  (hgr_stop B pa_segs_low F fc x PAT_KEY cl _ regs mem md L E ss ms md2 k errno_low Hc HC ltac:(lia) eq_refl HS HAE Hk
    Hfix HJ Hio KM)
  Hfx HM Hci (pw_loop_stop F fc x r cl keys E ss ms cs v1 v2 v3 HS U20 U21 U22 Hin U2 C1 V1 C2 V2 C3 V3)
  (hgr_reg_U F fc E ss ms _ 23%bv _ HS U23) (hgr_reg_U F fc E ss ms _ 24%bv _ HS U24)
  (hgr_reg_U F fc E ss ms _ 25%bv _ HS U25) (hgr_reg_U F fc E ss ms _ 10%bv _ HS U10)
  (hgr_reg_U F fc E ss ms _ 11%bv _ HS U11) (hgr_reg_U F fc E ss ms _ 12%bv _ HS U12)
  (hgr_reg_U F fc E ss ms _ 1%bv _ HS U1)
  (hgr_temps_val F fc x E ss ms cs 0x30 v4 _ HS Hin U2 C4 V4) HRET).
Qed.

(* the temporaries region of a stop, its chunks found by computation *)
Ltac pw_find_temps :=
  lazymatch goal with |- In (hk_temps _) (ss_mem ?ss) =>
  let m := eval vm_compute in (ss_mem ss) in
  replace (ss_mem ss) with m by (vm_compute; reflexivity); unfold hk_temps;
  repeat first [apply in_eq | apply in_cons] end.

(* ---------------------------------- LAST 0x84994 -> ADV ---------------------------------- *)
(* 0x84994 .. 0x849a0: the 1-byte check of a0 = s7 + 8 + size - 1 (shadow entry mkSHE 10 0 1), 0x849a4 lbu b;
   0x849a8 beqz b: ADV with s8 = s7 + 8 (the key slot cc), else 0x849ac s8 = 0 and ADV. *)
Lemma pw_last_ok : forall (x : pctx) r cc n cl keys rf, call_ok B x ->
(forall ko', ADV_ok B MT x r cc n ko' cl keys rf) -> LAST_ok x r cc n cl keys rf.
Proof.
intros x r cc n cl keys rf Hc HADV F fc regs mem md HLB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsl.
pose proof HLB as (HC & Hfx & HM & Hci & Hcs & Hty & HL & (R14 & R15) & R23 & R24 & R25 & R16 & R10).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hgr_walk_keys x r cc (S n) None cl keys rf HM) as Hkeys.
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_KEY cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_inside_bounds _ _ _ _ Hci) as (B1 & B2 & B3).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
set (o := cc + 8 + Spa.u32_at (hx_bs x) cc - 1) in *.
set (b := bv_unsigned (nth (Z.to_nat o) (hx_bs x) Cursor.NUL)).
destruct (hgw_pod_u8 (hx_rd x mem) (hx_P x) (hx_bs x) o HG ltac:(lia) ltac:(unfold hx_len in *; lia)) as [Vb Rb].
fold b in Vb, Rb.
set (L := [w64 b; w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 keys]).
set (E0 := hk_env x regs L).
assert (EG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 m = w64 v).
{ intros m rg v Hm Hv. subst E0. rewrite (hk_env_reg x regs L m rg Hm). exact Hv. }
assert (UG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff m 0) = v) by (intros m rg v Hm Hv Hr; apply U_atom; [exact (EG m rg v Hm Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
assert (E10 : ew E0 10 = w64 (hx_P x + o)) by (rewrite (EG 10%nat 10%bv _ eq_refl R10); unfold o; f_equal; lia).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by exact (EG 27%nat 27%bv _ eq_refl C27).
assert (E47 : ew E0 47 = w64 b) by exact (hk_env_seg x regs L 0).
assert (U47 : U E0 (SOff 47 0) = b) by (apply (UL 0%nat); [reflexivity | lia]).
assert (U48 : U E0 (SOff 48 0) = (hx_P x + r + 8) mod 8 + 3) by (apply (UL 1%nat); [reflexivity | lia]).
assert (U49 : U E0 (SOff 49 0) = hx_P x + r + 16) by (apply (UL 2%nat); [reflexivity | lia]).
assert (U50 : U E0 (SOff 50 0) = keys) by (apply (UL 3%nat); [reflexivity | lia]).
assert (U14 : U E0 (SOff 14 0) = hx_P x + r + 16) by (apply (UG 14%nat 14%bv); [reflexivity | exact R14 | lia]).
assert (U15 : U E0 (SOff 15 0) = 8) by (apply (UG 15%nat 15%bv); [reflexivity | exact R15 | lia]).
assert (U16 : U E0 (SOff 16 0) = shadow_addr (hx_P x + cc))
by (apply (UG 16%nat 16%bv); [reflexivity | exact R16 | apply Hsh; lia]).
assert (U20 : U E0 (SOff 20 0) = Z.of_nat (length cl)) by (apply (UG 20%nat 20%bv); [reflexivity | exact L20 | lia]).
assert (U21 : U E0 (SOff 21 0) = shadow_addr (hx_P x + r + 8))
by (apply (UG 21%nat 21%bv); [reflexivity | exact L21 | apply Hsh; lia]).
assert (U22 : U E0 (SOff 22 0) = hx_P x + r + 8) by (apply (UG 22%nat 22%bv); [reflexivity | exact L22 | lia]).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply (UG 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (U24 : U E0 (SOff 24 0) = hx_P x + cc + 8) by (apply (UG 24%nat 24%bv); [reflexivity | exact R24 | lia]).
assert (U25 : U E0 (SOff 25 0) = rf) by (apply (UG 25%nat 25%bv); [reflexivity | exact R25 | lia]).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pw_ssb
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_LAST) mem (seg_rom rsegs)))).
{ unfold pw_ssb. apply (hgr_entry B F fc x PAT_KEY cl _ regs mem md L PC_LAST _ _ _ _ Hc HC).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply (pw_tcs_ok x regs mem L r cl keys 48 HL);
    [exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | exact (hk_env_seg x regs L 3) | lia | lia | lia].
  - apply Forall_cons; [|apply Forall_nil]. unfold pw_rb.
    apply (hm_ro_region rsegs (hk_env x regs L) (w_H (hx_W x)) mem 10 (hx_P x + o) 0 1);
    [fold E0; rewrite E10; unfold w64; apply unsigned_lit_small; lia | lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 47 0) b); [rewrite hk_sv_SOff0; exact E47 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
  - apply pairwise_disjoint_of_extents. unfold hk_temps, pw_rb.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl C2), E10. unfold w64. rewrite !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia.
  - unfold pw_atoms_b. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
    rewrite E10, E47. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold o. repeat split; lia. }
assert (SHOK : sh_ok rsegs hk_Bx pw_SHb E0 (hx_rd x mem)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (hk_shent_pod B x (w_H (hx_W x)) mem E0 10 o 0 1 Hc Hnull E27 E10 HRA ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold hx_len in *; lia)). }
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 51 E0 E0) by apply env_agree_refl.
unfold cfg_at. change (w64 PC_LAST) with (Z_to_bv 64 PC_LAST).
(* 0x84994 .. 0x849a4: the check of the byte (decided), lbu; stop at 0x849a8 beqz *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB.
- (* taken: the byte is NUL: ADV with s8 = s7 + 8, the key slot cc *)
  rewrite U47, U_lit in HB by lia. apply Z.eqb_eq in HB.
  assert (UK : U E0 (SOff 24 0) = hp_keyv x (hgw_ko x cc)).
  { rewrite (hgr_keyv_lb x cc ltac:(lia) Hcs Hty). fold o b. rewrite HB, Z.eqb_refl. exact U24. }
  hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
  eapply (pw_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 51 (pw_tcs 48) (SOff 48 0)
    (SOff 49 0) (SOff 50 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14 | hgr_ukept HAE U15
  | hgr_ukept HAE U23 | hgr_ukept HAE UK | hgr_ukept HAE U25 | hgr_ukept HAE U16
  | hgr_in | exact U2 | hgr_in | hgr_uat HAE U48 | hgr_in | hgr_uat HAE U49 | hgr_in | hgr_uat HAE U50
  | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
- (* not taken: 0x849ac s8 = 0; ADV with the key slot empty *)
  rewrite U47, U_lit in HB by lia. apply Z.eqb_neq in HB.
  hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
  eapply (pw_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 51 (pw_tcs 48) (SOff 48 0)
    (SOff 49 0) (SOff 50 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hci) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14 | hgr_ukept HAE U15
  | hgr_ukept HAE U23
  | hgr_ureg HAE; rewrite U_lit by lia; rewrite (hgr_keyv_lb x cc ltac:(lia) Hcs Hty); fold o b;
    rewrite (proj2 (Z.eqb_neq b 0) HB); reflexivity
  | hgr_ukept HAE U25 | hgr_ukept HAE U16
  | hgr_in | exact U2 | hgr_in | hgr_uat HAE U48 | hgr_in | hgr_uat HAE U49 | hgr_in | hgr_uat HAE U50
  | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
Qed.

(* ---------------------------------- RET 0x849cc -> KEY | ADV ---------------------------------- *)
(* 0x849cc beqz a0: taken (strncmp = 0, the key has the prefix) -> KEY 0x849e4; else s8 = 0, a4 = [spa + 32],
   a5 = 8, a6 = [spa + 48]; j ADV (the pair is skipped). *)
Lemma pw_ret_ok : forall (x : pctx) r cc n ck cl keys rf, call_ok B x ->
(forall ko', ADV_ok B MT x r cc n ko' cl keys rf) -> KEY_ok B MT x r cc n ck cl keys rf ->
RET_ok x r cc n ck cl keys rf.
Proof.
intros x r cc n ck cl keys rf Hc HADV HKEY F fc regs mem md HR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsl.
pose proof HR as (HC & Hfx & HM & Hci & HL & R23 & R24 & R25 & H48 & H10).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hn & HK & Hs & HW).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hgr_walk_keys x r cc (S n) (Some ck) cl keys rf HM) as Hkeys.
pose proof (HK ck eq_refl) as HKo. pose proof HKo as (Hck0 & Hckl & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_inside_bounds _ _ _ _ Hci) as (B1 & B2 & B3).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
pose proof (hgw_u32_range (hx_bs x) ck) as RCK.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
set (L := [w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 keys; w64 (shadow_addr (hx_P x + cc))]).
set (E0 := hk_env x regs L).
assert (EG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 m = w64 v).
{ intros m rg v Hm Hv. subst E0. rewrite (hk_env_reg x regs L m rg Hm). exact Hv. }
assert (UG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff m 0) = v) by (intros m rg v Hm Hv Hr; apply U_atom; [exact (EG m rg v Hm Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
pose proof (Hsh (hx_P x + cc) ltac:(lia)) as Rsh.
assert (U47 : U E0 (SOff 47 0) = (hx_P x + r + 8) mod 8 + 3) by (apply (UL 0%nat); [reflexivity | lia]).
assert (U48 : U E0 (SOff 48 0) = hx_P x + r + 16) by (apply (UL 1%nat); [reflexivity | lia]).
assert (U49 : U E0 (SOff 49 0) = keys) by (apply (UL 2%nat); [reflexivity | lia]).
assert (U50 : U E0 (SOff 50 0) = shadow_addr (hx_P x + cc)) by (apply (UL 3%nat); [reflexivity | exact Rsh]).
assert (U20 : U E0 (SOff 20 0) = Z.of_nat (length cl)) by (apply (UG 20%nat 20%bv); [reflexivity | exact L20 | lia]).
assert (U21 : U E0 (SOff 21 0) = shadow_addr (hx_P x + r + 8))
by (apply (UG 21%nat 21%bv); [reflexivity | exact L21 | apply Hsh; lia]).
assert (U22 : U E0 (SOff 22 0) = hx_P x + r + 8) by (apply (UG 22%nat 22%bv); [reflexivity | exact L22 | lia]).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply (UG 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (U24 : U E0 (SOff 24 0) = hx_P x + ck + 8) by (apply (UG 24%nat 24%bv); [reflexivity | exact R24 | lia]).
assert (U25 : U E0 (SOff 25 0) = rf) by (apply (UG 25%nat 25%bv); [reflexivity | exact R25 | lia]).
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pw_ssr
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_RET) mem (seg_rom rsegs)))).
{ unfold pw_ssr. apply (hgr_entry B F fc x PAT_KEY cl _ regs mem md L PC_RET _ _ _ _ Hc HC).
  - unfold hk_env. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold pw_csr. apply Forall_app. split.
    + apply (pw_tcs_ok x regs mem L r cl keys 47 HL);
      [exact (hk_env_seg x regs L 0) | exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | lia | lia | lia].
    + apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ _ 0x30 8 (SOff 50 0) (shadow_addr (hx_P x + cc)));
      [rewrite hk_sv_SOff0; exact (hk_env_seg x regs L 3) | cbn; lia | lia | exact H48].
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - exact I. }
assert (SHOK : sh_ok rsegs hk_Bx [] E0 (hx_rd x mem)) by apply Forall_nil.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 51 E0 E0) by apply env_agree_refl.
assert (U10 : U E0 (SOff 10 0) = 0 <-> Headamp.ha_prefix (hp_kstr x ck) = true)
by exact (iff_trans (hgr_U_reg0 x regs L 10 10%bv eq_refl) H10).
unfold cfg_at. change (w64 PC_RET) with (Z_to_bv 64 PC_RET).
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB.
- (* taken: strncmp = 0, KEY 0x849e4 *)
  rewrite ?U_lit in HB by lia. apply Z.eqb_eq in HB. pose proof (proj1 U10 HB) as HP.
  hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_KEY.
  eapply (pw_exit_key F fc x r cc n ck cl keys rf regs mem md L _ _ _ _ 51 pw_csr (SOff 47 0) (SOff 48 0) (SOff 49 0)
    (SOff 50 0) Hc HC Hfx (hgw_walk_key x r cc n ck cl keys rf HM Hci HP) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U23 | hgr_ukept HAE U24
  | hgr_ukept HAE U25
  | hgr_in | exact U2
  | hgr_in | hgr_uat HAE U47 | hgr_in | hgr_uat HAE U48 | hgr_in | hgr_uat HAE U49 | hgr_in | hgr_uat HAE U50
  | exact HJ | exact Hio | exact KM | exact HKEY ].
- (* not taken: strncmp <> 0, the pair is skipped; ADV with the key slot empty *)
  rewrite ?U_lit in HB by lia. apply Z.eqb_neq in HB.
  assert (HP : Headamp.ha_prefix (hp_kstr x ck) = false)
  by (destruct (Headamp.ha_prefix (hp_kstr x ck)) eqn:EP; [exfalso; exact (HB (proj2 U10 eq_refl)) | reflexivity]).
  hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
  eapply (pw_exit_adv F fc x r cc n None cl keys rf regs mem md L _ _ _ _ 51 pw_csr (SOff 47 0) (SOff 48 0)
    (SOff 49 0) Hc HC Hfx (hgw_walk_skip x r cc n ck cl keys rf HM Hci HP) HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22
  | hgr_ukept HAE U48
  | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
  | hgr_ukept HAE U23
  | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
  | hgr_ukept HAE U25
  | hgr_ukept HAE U50
  | hgr_in | exact U2
  | hgr_in | hgr_uat HAE U47 | hgr_in | hgr_uat HAE U48 | hgr_in | hgr_uat HAE U49
  | exact HJ | exact Hio | exact KM | exact (HADV None) ].
Qed.

(* ---------------------------------- WALK 0x84910 ---------------------------------- *)
Theorem hp_segWALK_A : segWALK_stmt B MT.
Proof.
unfold segWALK_stmt. intros x r cc n ko cl keys rf Hc HADV HKEY HEXIT F fc regs mem md HW.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsl.
pose proof HW as (HC & Hfx & HM & HL & (R14 & R15) & R23 & R24 & R25).
pose proof HM as (Hnull & Hst & Hcc & Hc8 & Hn & HK & Hs & HWm).
pose proof Hs as (Hcl & Hk0 & Hrf). pose proof Hst as (Hr16 & Hr8 & Hvs & Hrl).
pose proof HL as (L20 & L21 & L22 & L16 & L32 & L40).
pose proof (hgr_walk_keys x r cc (S n) ko cl keys rf HM) as Hkeys.
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & HOFF).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_KEY cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_stack B x Hc) as HS0. pose proof (hk_frame_win B x Hc) as HFW.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (C2 & C8 & C3 & C4 & C9 & C18 & C19 & C26 & C27).
pose proof (hgw_u32_range (hx_bs x) cc) as RCS. pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RTY.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RVS.
unfold hp_vs in *.
assert (Hhi : hx_P x + hx_len x + 8 <= 2 ^ 47)
by (destruct HAM as [HAl|[HAh1 HAh2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
pose proof alloc_ceiling_value as [[AC1 AC2] _]. pose proof (hk_out B x Hc) as (Hcap & _).
pose proof (Z.mod_pos_bound (hx_P x + r + 8) 8 ltac:(lia)) as RM.
assert (Hsh : forall a, 0 <= a <= 2 ^ 47 -> 0 <= shadow_addr a < 2 ^ 64).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (Hccl : cc <= hx_len x) by (clear - Hcc Hc8 Hrl Hl8m; Z.div_mod_to_equations; lia).
set (L := [w64 (Spa.u32_at (hx_bs x) (r + 8)); w64 (Spa.u32_at (hx_bs x) cc); w64 (Spa.u32_at (hx_bs x) (cc + 4));
  w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 keys]).
set (E0 := hk_env x regs L).
assert (EG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> ew E0 m = w64 v).
{ intros m rg v Hm Hv. subst E0. rewrite (hk_env_reg x regs L m rg Hm). exact Hv. }
assert (UG : forall (m : nat) (rg : bv 5) v, Z.of_nat m = bv_unsigned rg -> getr regs rg = w64 v -> 0 <= v < 2 ^ 64 ->
  U E0 (SOff m 0) = v) by (intros m rg v Hm Hv Hr; apply U_atom; [exact (EG m rg v Hm Hv) | exact Hr]).
assert (UL : forall j v, nth j L (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 -> U E0 (SOff (47 + j) 0) = v)
by (intros j v Hv Hr; apply U_atom; [subst E0; rewrite hk_env_seg; exact Hv | exact Hr]).
assert (U2 : bv_unsigned (ew E0 2) = hx_spa x) by (rewrite (EG 2%nat 2%bv _ eq_refl C2); apply unsigned_lit_small; lia).
assert (E22 : ew E0 22 = w64 (hx_P x + r + 8)) by exact (EG 22%nat 22%bv _ eq_refl L22).
assert (E23 : ew E0 23 = w64 (hx_P x + cc)) by exact (EG 23%nat 23%bv _ eq_refl R23).
assert (E27 : ew E0 27 = w64 SHADOW_OFF) by exact (EG 27%nat 27%bv _ eq_refl C27).
assert (E47 : ew E0 47 = w64 (Spa.u32_at (hx_bs x) (r + 8))) by exact (hk_env_seg x regs L 0).
assert (E48 : ew E0 48 = w64 (Spa.u32_at (hx_bs x) cc)) by exact (hk_env_seg x regs L 1).
assert (E49 : ew E0 49 = w64 (Spa.u32_at (hx_bs x) (cc + 4))) by exact (hk_env_seg x regs L 2).
assert (U14 : U E0 (SOff 14 0) = hx_P x + r + 16) by (apply (UG 14%nat 14%bv); [reflexivity | exact R14 | lia]).
assert (U20 : U E0 (SOff 20 0) = Z.of_nat (length cl)) by (apply (UG 20%nat 20%bv); [reflexivity | exact L20 | lia]).
assert (U22 : U E0 (SOff 22 0) = hx_P x + r + 8) by (apply (UG 22%nat 22%bv); [reflexivity | exact L22 | lia]).
assert (U23 : U E0 (SOff 23 0) = hx_P x + cc) by (apply (UG 23%nat 23%bv); [reflexivity | exact R23 | lia]).
assert (U25 : U E0 (SOff 25 0) = rf) by (apply (UG 25%nat 25%bv); [reflexivity | exact R25 | lia]).
assert (U27 : U E0 (SOff 27 0) = SHADOW_OFF)
by (apply (UG 27%nat 27%bv); [reflexivity | exact C27 | unfold SHADOW_OFF; lia]).
assert (U47 : U E0 (SOff 47 0) = Spa.u32_at (hx_bs x) (r + 8)) by (apply (UL 0%nat); [reflexivity | lia]).
assert (U48 : U E0 (SOff 48 0) = Spa.u32_at (hx_bs x) cc) by (apply (UL 1%nat); [reflexivity | lia]).
assert (U49 : U E0 (SOff 49 0) = Spa.u32_at (hx_bs x) (cc + 4)) by (apply (UL 2%nat); [reflexivity | lia]).
assert (U50 : U E0 (SOff 50 0) = (hx_P x + r + 8) mod 8 + 3) by (apply (UL 3%nat); [reflexivity | lia]).
assert (U51 : U E0 (SOff 51 0) = hx_P x + r + 16) by (apply (UL 4%nat); [reflexivity | lia]).
assert (U52 : U E0 (SOff 52 0) = keys) by (apply (UL 5%nat); [reflexivity | lia]).
assert (U21 : U E0 (pw_sh 22) = shadow_addr (hx_P x + r + 8))
by (unfold pw_sh; apply hgw_U_shadow; [exact U22 | exact U27 | lia]).
assert (U16s : U E0 (pw_sh 23) = shadow_addr (hx_P x + cc))
by (unfold pw_sh; apply hgw_U_shadow; [exact U23 | exact U27 | lia]).
assert (U24 : U E0 (SOff 24 0) = hp_keyv x ko).
{ apply (UG 24%nat 24%bv); [reflexivity | exact R24 |]. unfold hp_keyv. destruct ko as [ck|]; [|lia].
  pose proof (HK ck eq_refl) as (Hck0 & Hckl & _). pose proof (hgw_u32_range (hx_bs x) ck). lia. }
(* the Struct pod's header: its size word and its shadow entry *)
assert (HR6 : region_ok rsegs E0 (hx_rd x mem) pw_r6).
{ unfold pw_r6. apply (hm_ro_region rsegs E0 (w_H (hx_W x)) mem 22 (hx_P x + r + 8) 0 4);
  [rewrite E22; unfold w64; apply unsigned_lit_small; lia | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs E0 _ (hx_P x + r + 8) 0 4 (SOff 47 0) (Spa.u32_at (hx_bs x) (r + 8)));
  [rewrite hk_sv_SOff0, E47; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. replace (hx_P x + r + 8) with (hx_P x + (r + 8)) by lia.
  apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (r + 8) HG); unfold hx_len in *; lia. }
assert (SH22 : shent_ok rsegs hk_Bx E0 (hx_rd x mem) (mkSHE 22 0 8)).
{ apply (hk_shent_pod B x (w_H (hx_W x)) mem E0 22 (r + 8) 0 8 Hc Hnull E27);
  [replace (hx_P x + (r + 8)) with (hx_P x + r + 8) by lia; exact E22 | exact HRA | lia | lia | lia | lia]. }
assert (Hregs : regs_ok (hk_env x regs L) pw_regs_key regs).
{ unfold pw_regs_key. apply regs_ok_pin; [apply regs_ok_pin; [unfold hk_env; apply regs_ok_Ereg | vm_compute; discriminate |]
    | vm_compute; discriminate |].
  + rewrite L21. symmetry. apply (pw_sv_sh E0 22 (hx_P x + r + 8) E22 E27 ltac:(lia)).
  + rewrite R15. reflexivity. }
assert (HT : Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) (pw_tcs 50)).
{ apply (pw_tcs_ok x regs mem L r cl keys 50 HL);
  [exact (hk_env_seg x regs L 3) | exact (hk_env_seg x regs L 4) | exact (hk_env_seg x regs L 5) | lia | lia | lia]. }
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & _ & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x <= a < hx_spa x + 0x80) ->
  hx_rd x mem (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) by reflexivity.
pose proof (same_io_refl md) as Hio.
assert (HAE : env_agree 53 E0 E0) by apply env_agree_refl.
unfold cfg_at. change (w64 PC_WALK) with (Z_to_bv 64 PC_WALK).
destruct (Z_le_gt_dec (cc + 8) (r + 16 + Spa.u32_at (hx_bs x) (r + 8))) as [HIN | HOUT].
2:{ (* ---------------- the child's header does not lie in the Struct body: EXIT ---------------- *)
  assert (Hpif : Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false)
    by (apply hgr_out_B; unfold hp_vs; lia).
  assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pw_sso
    (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WALK) mem (seg_rom rsegs)))).
  { unfold pw_sso. apply (hgr_entry B F fc x PAT_KEY cl _ regs mem md L PC_WALK _ _ _ _ Hc HC Hregs).
    - vm_compute. reflexivity.
    - exact HT.
    - apply Forall_cons; [exact HR6 | apply Forall_nil].
    - apply pairwise_disjoint_of_extents. unfold hk_temps, pw_r6.
      cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
      rewrite (EG 2%nat 2%bv _ eq_refl C2), E22. unfold w64. rewrite !unsigned_lit_small by (unfold hx_sp in *; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia.
    - unfold pw_atoms_o. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
      rewrite E22, E47. unfold w64. rewrite !unsigned_lit_small by lia.
      change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      assert ((hx_P x + r + 8) mod 4 = 0) by (clear - HP16 Hr8; Z.div_mod_to_equations; lia).
      repeat split; lia. }
  assert (SHOK : sh_ok rsegs hk_Bx pw_SH6 E0 (hx_rd x mem)) by (apply Forall_cons; [exact SH22 | apply Forall_nil]).
  (* 0x84910 .. 0x84914: the check of s6 (decided); stop at 0x84918 bltu s7,a4 *)
  hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
  hgr_branch pa_tbl_ok HAE HB1.
  { exfalso. rewrite U23, U14 in HB1. apply Z.ltb_lt in HB1. lia. }
  (* stop at 0x84920 bltu vs,8 *)
  hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
  hgr_branch pa_tbl_ok HAE HB2.
  - (* vs < 8: EXIT *)
    hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_EXIT.
    eapply (pw_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 52 0) Hc HC Hfx HM HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
    | hgr_ukept HAE U20 | hgr_ukept HAE U25 | hgr_in | exact U2 | hgr_in | hgr_uat HAE U52 | exact Hpif
    | exact HJ | exact Hio | exact KM | exact HEXIT ].
  - rewrite U47, U_lit in HB2 by lia. apply Z.ltb_ge in HB2.
    (* stop at 0x8492c bltu vs - 8, cc - (r + 16) *)
    hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
    hgr_branch pa_tbl_ok HAE HB3.
    + (* EXIT *)
      hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_EXIT.
      eapply (pw_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 52 0) Hc HC Hfx HM HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
      | hgr_ukept HAE U20 | hgr_ukept HAE U25 | hgr_in | exact U2 | hgr_in | hgr_uat HAE U52 | exact Hpif
      | exact HJ | exact Hio | exact KM | exact HEXIT ].
    + exfalso.
      rewrite (hgw_U_off E0 47 _ (-8) U47 ltac:(lia)), (hgw_U_subba E0 14 23 _ _ U14 U23 ltac:(lia)) in HB3.
      apply Z.ltb_ge in HB3. lia. }
(* ---------------- the child's header lies in the Struct body ---------------- *)
assert (HR7 : region_ok rsegs E0 (hx_rd x mem) pw_r7).
{ unfold pw_r7. apply (hm_ro_region rsegs E0 (w_H (hx_W x)) mem 23 (hx_P x + cc) 0 8);
  [rewrite E23; unfold w64; apply unsigned_lit_small; lia | lia | lia |].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val rsegs E0 _ (hx_P x + cc) 0 4 (SOff 48 0) (Spa.u32_at (hx_bs x) cc));
    [rewrite hk_sv_SOff0, E48; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) cc HG); unfold hx_len in *; lia.
  + apply (chunk_ok_val rsegs E0 _ (hx_P x + cc) 4 4 (SOff 49 0) (Spa.u32_at (hx_bs x) (cc + 4)));
    [rewrite hk_sv_SOff0, E49; reflexivity | cbn; lia | cbn; lia |].
    replace (hx_P x + cc + 4) with (hx_P x + (cc + 4)) by lia.
    apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (cc + 4) HG); unfold hx_len in *; lia. }
assert (HS : st_ok (fx := mkFP F fc) rsegs E0 pw_ss
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PC_WALK) mem (seg_rom rsegs)))).
{ unfold pw_ss, pw_facts. apply (hgr_entry B F fc x PAT_KEY cl _ regs mem md L PC_WALK _ _ _ _ Hc HC Hregs).
  - vm_compute. reflexivity.
  - exact HT.
  - apply Forall_cons; [exact HR6 | apply Forall_cons; [exact HR7 | apply Forall_nil]].
  - apply pairwise_disjoint_of_extents. unfold hk_temps, pw_r6, pw_r7.
    cbn [map]. unfold extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E0.
    rewrite (EG 2%nat 2%bv _ eq_refl C2), E22, E23. unfold w64.
    rewrite !unsigned_lit_small by (unfold hx_sp in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *. destruct Hside; repeat split; lia.
  - unfold pw_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
    rewrite E22, E23, E47, E48, E49. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    assert ((hx_P x + r + 8) mod 4 = 0) by (clear - HP16 Hr8; Z.div_mod_to_equations; lia).
    assert ((hx_P x + cc) mod 4 = 0) by (clear - HP16 Hc8; Z.div_mod_to_equations; lia).
    repeat split; lia. }
assert (SHOK : sh_ok rsegs hk_Bx pw_SH E0 (hx_rd x mem)).
{ unfold pw_SH. apply Forall_cons; [exact SH22 | apply Forall_cons; [|apply Forall_nil]].
  apply (hk_shent_pod B x (w_H (hx_W x)) mem E0 23 cc 0 8 Hc Hnull E27 E23 HRA); lia. }
(* 0x84910 .. 0x84914: the check of s6 (decided); stop at 0x84918 bltu s7,a4 *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB1.
{ exfalso. rewrite U23, U14 in HB1. apply Z.ltb_lt in HB1. lia. }
(* stop at 0x84920 bltu vs,8 *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB2.
{ exfalso. rewrite U47, U_lit in HB2 by lia. apply Z.ltb_lt in HB2. lia. }
(* stop at 0x8492c bltu vs - 8, cc - (r + 16) *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB3.
{ exfalso.
  rewrite (hgw_U_off E0 47 _ (-8) U47 ltac:(lia)), (hgw_U_subba E0 14 23 _ _ U14 U23 ltac:(lia)) in HB3.
  apply Z.ltb_lt in HB3. lia. }
(* 0x84930 .. 0x84948: the check of s7 (decided), lwu the child's size; stop at 0x8494c *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
assert (Urest : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 22 0) (SMd M_MUL (SOff 23 0) (SLit 18446744073709551615)))
  (SOff 47 0)) = r + 8 + Spa.u32_at (hx_bs x) (r + 8) - cc)
by (rewrite (hgw_U_rest E0 22 23 47 _ _ _ U22 U23 U47); lia).
hgr_branch pa_tbl_ok HAE HB4.
{ (* the child's body runs past the Struct body: EXIT *)
  rewrite Urest, U48 in HB4. apply Z.ltb_lt in HB4.
  assert (Hpif : Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = false)
    by (rewrite (hgr_inside_A x r cc ltac:(lia) Hc8 ltac:(unfold hp_vs; lia)); apply Z.leb_gt; unfold hp_vs; lia).
  hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_EXIT.
  eapply (pw_exit_exit F fc x r cc n ko cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 52 0) Hc HC Hfx HM HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U25 | hgr_in | exact U2 | hgr_in | hgr_uat HAE U52 | exact Hpif
  | exact HJ | exact Hio | exact KM | exact HEXIT ]. }
rewrite Urest, U48 in HB4. apply Z.ltb_ge in HB4.
assert (Hpit : Spa.pod_is_inside (hx_bs x) (r + 16) (hp_vs x r) cc = true)
  by (rewrite (hgr_inside_A x r cc ltac:(lia) Hc8 ltac:(unfold hp_vs; lia)); apply Z.leb_le; unfold hp_vs; lia).
(* stop at 0x84950 bnez s8 *)
hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
hgr_branch pa_tbl_ok HAE HB5.
- (* the key slot holds the key ck: 0x849b4 sd a6,48(sp), the arguments, jal 0x41ba4 *)
  rewrite U24, U_lit in HB5 by lia.
  destruct ko as [ck|]; [| exfalso; cbn in HB5; discriminate HB5].
  hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
  eapply (pw_exit_call F fc x r cc n ck cl keys rf regs mem md L _ _ _ _ 53 _ (SOff 50 0) (SOff 51 0) (SOff 52 0)
    (pw_sh 23) Hc HC Hfx HM Hpit HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
  | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U23 | hgr_ukept HAE U24
  | hgr_ukept HAE U25 | hgr_ukept HAE U24
  | hgr_ureg HAE; rewrite ?U_lit by lia; first [reflexivity | vm_compute; reflexivity]
  | hgr_ureg HAE; rewrite ?U_lit by lia; first [reflexivity | vm_compute; reflexivity]
  | hgr_ureg HAE; rewrite ?U_lit by lia; first [reflexivity | vm_compute; reflexivity]
  | pw_find_temps | exact U2
  | hgr_in | hgr_uat HAE U50 | hgr_in | hgr_uat HAE U51 | hgr_in | hgr_uat HAE U52 | hgr_in | hgr_uat HAE U16s
  | exact HJ | exact Hio | exact KM | exact (pw_ret_ok x r cc n ck cl keys rf Hc HADV (HKEY ck eq_refl)) ].
- (* the key slot is empty: spa_pod_get_string of the child *)
  rewrite U24, U_lit in HB5 by lia.
  destruct ko as [ck|].
  { exfalso. cbn [hp_keyv] in HB5. apply negb_false_iff, Z.eqb_eq in HB5.
    pose proof (HK ck eq_refl) as (Hck0 & _). lia. }
  (* 0x84954 .. 0x84960: the check of s7 (decided), lw the size, srliw; stop at 0x84964 bnez (size >> 20) *)
  hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
  hgr_branch pa_tbl_ok HAE HB6.
  + (* the size is at least 2^20: 0x849ac s8 = 0; ADV *)
    rewrite (pw_U_srliw20 E0 48 _ U48 RCS), U_lit in HB6 by lia. apply negb_true_iff, Z.eqb_neq in HB6.
    assert (Hbig : 2 ^ 20 <= Spa.u32_at (hx_bs x) cc).
    { destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) cc) (2 ^ 20)) as [Hl|Hl]; [|exact Hl].
      exfalso. apply HB6. apply Z.div_small. lia. }
    hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
    eapply (pw_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 50 0)
      (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hpit) HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
    | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14
    | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
    | hgr_ukept HAE U23
    | hgr_ureg HAE; rewrite U_lit by lia; rewrite (hgr_ko_none x cc ltac:(lia) (or_introl Hbig)); reflexivity
    | hgr_ukept HAE U25 | hgr_ukept HAE U16s
    | hgr_in | exact U2 | hgr_in | hgr_uat HAE U50 | hgr_in | hgr_uat HAE U51 | hgr_in | hgr_uat HAE U52
    | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
  + rewrite (pw_U_srliw20 E0 48 _ U48 RCS), U_lit in HB6 by lia. apply negb_false_iff, Z.eqb_eq in HB6.
    assert (Hsmall : Spa.u32_at (hx_bs x) cc < 2 ^ 20).
    { destruct (Z_lt_le_dec (Spa.u32_at (hx_bs x) cc) (2 ^ 20)) as [Hl|Hl]; [exact Hl|].
      exfalso. pose proof (Z.div_le_lower_bound (Spa.u32_at (hx_bs x) cc) (2 ^ 20) 1 ltac:(lia) ltac:(lia)). lia. }
    (* 0x84968 .. 0x84978: the check of s7 + 4 (decided); stop at 0x8497c beqz size *)
    hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
    hgr_branch pa_tbl_ok HAE HB7.
    * (* the size is 0: ADV *)
      rewrite (hgw_U_sext32 E0 48 _ U48 RCS), U_lit in HB7 by lia.
      rewrite (proj2 (Z.ltb_lt (Spa.u32_at (hx_bs x) cc) (2 ^ 31))) in HB7 by lia. apply Z.eqb_eq in HB7.
      hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
      eapply (pw_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 50 0)
        (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hpit) HS);
      [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
      | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14
      | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
      | hgr_ukept HAE U23
      | hgr_ureg HAE; rewrite U_lit by lia; rewrite (hgr_ko_none x cc ltac:(lia) (or_intror (or_introl HB7)));
        reflexivity
      | hgr_ukept HAE U25 | hgr_ukept HAE U16s
      | hgr_in | exact U2 | hgr_in | hgr_uat HAE U50 | hgr_in | hgr_uat HAE U51 | hgr_in | hgr_uat HAE U52
      | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
    * rewrite (hgw_U_sext32 E0 48 _ U48 RCS), U_lit in HB7 by lia.
      rewrite (proj2 (Z.ltb_lt (Spa.u32_at (hx_bs x) cc) (2 ^ 31))) in HB7 by lia. apply Z.eqb_neq in HB7.
      (* 0x84980 lw the type; stop at 0x84984 bne type,8 *)
      hgr_run pa_tbl_ok x Hc HAE KM Hio U2.
      hgr_branch pa_tbl_ok HAE HB8.
      -- (* not a String: ADV *)
         rewrite U_lit in HB8 by lia. rewrite (hgw_U_sext32_eqb E0 49 _ 8 U49 RTY ltac:(lia)) in HB8.
         apply negb_true_iff, Z.eqb_neq in HB8.
         hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_ADV.
         eapply (pw_exit_adv F fc x r cc n (hgw_ko x cc) cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 50 0)
           (SOff 51 0) (SOff 52 0) Hc HC Hfx (hgw_walk_adv0 x r cc n cl keys rf HM Hpit) HS);
         [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
         | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14
         | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
         | hgr_ukept HAE U23
         | hgr_ureg HAE; rewrite U_lit by lia;
           rewrite (hgr_ko_none x cc ltac:(lia) (or_intror (or_intror HB8))); reflexivity
         | hgr_ukept HAE U25 | hgr_ukept HAE U16s
         | hgr_in | exact U2 | hgr_in | hgr_uat HAE U50 | hgr_in | hgr_uat HAE U51 | hgr_in | hgr_uat HAE U52
         | exact HJ | exact Hio | exact KM | exact (HADV (hgw_ko x cc)) ].
      -- rewrite U_lit in HB8 by lia. rewrite (hgw_U_sext32_eqb E0 49 _ 8 U49 RTY ltac:(lia)) in HB8.
         apply negb_false_iff, Z.eqb_eq in HB8.
         (* 0x84988 .. 0x84990: s8 = s7 + 8, a0 = s8 + size - 1; the inner cut LAST 0x84994 *)
         hgr_run_to pa_tbl_ok x Hc HAE KM Hio U2 PC_LAST.
         eapply (pw_exit_last F fc x r cc n cl keys rf regs mem md L _ _ _ _ 53 (pw_tcs 50) (SOff 50 0) (SOff 51 0)
           (SOff 52 0) Hc HC Hfx HM Hpit ltac:(lia) HB8 HS);
         [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | hgr_fixed_tac
         | hgr_ukept HAE U20 | hgr_ukept HAE U21 | hgr_ukept HAE U22 | hgr_ukept HAE U14
         | hgr_ureg HAE; rewrite U_lit by lia; reflexivity
         | hgr_ukept HAE U23
         | hgr_ureg HAE; apply (hgw_U_off E0 23 _ 8 U23); lia
         | hgr_ukept HAE U25 | hgr_ukept HAE U16s
         | hgr_ureg HAE; apply (pw_U_last E0 23 48 _ _ U23 U48); lia
         | hgr_in | exact U2 | hgr_in | hgr_uat HAE U50 | hgr_in | hgr_uat HAE U51 | hgr_in | hgr_uat HAE U52
         | exact HJ | exact Hio | exact KM | exact (pw_last_ok x r cc n cl keys rf Hc HADV) ].
Qed.

End b.

Print Assumptions hp_segADV_A.
Print Assumptions hp_segWALK_A.
