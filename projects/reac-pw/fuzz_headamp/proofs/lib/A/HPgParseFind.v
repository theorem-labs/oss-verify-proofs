(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v; 492 of its 562 lines of code are new or changed and 844 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v, with its module paths, module names and numbers changed; 502 of its 580 lines of code are new or changed and 484 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1 (f_kept, f_reg_of,
   f_same_io_wvb and the f_run / f_br / f_hc / f_rg / f_rkeep tactics, here hfa_* over the hole runners of
   lib/A/HPgHole.v and image A's cut FIND); the engine arithmetic is lib/A/HPgParseGFind.v's (the hpf_U_ lemmas), the pod's
   words lib/A/HPgParseGWalk.v's (hgw_u32_range, hgw_pod_u32); the entry states, the exits and the segment theorem
   are new. *)
(* reac_headamp_prop_parse_result 0x845b4 of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47), segment FIND: one pass of the find loop from the
   cut FIND 0x847c4 at the property offset r with fuel S n, hp_segFIND_A : segFIND_stmt B MT (lib/A/HPgParseCut.v).
   Proves no function by itself (kind: segment lemma of reac_headamp_prop_parse_result; lib/A/HPgParse.v composes it).

   The code (pcs read from the code, capstone over the pinned file):
     0x847c4 bltu a1,a0           P + r < P + 8: never (r >= 16);
     0x847cc bltu a2,a5           SZ - 16 < r - 8: the header does not fit -> EPI 0x84738 (s4 = 0);
     0x847d0 .. 0x847e4           the instrumented lwu of the value size VS at s6 = P + r + 8;
     0x847ec bltu a6,a5           SZ - 8 - r < VS -> 0x84734 li s4,0 -> EPI;
     0x847f0 .. 0x84800           the instrumented lw of the key at P + r; 0x84804 beq a6,a4 (key = 0x80001);
     0x84808 .. 0x8481c           r' = r + ((VS + 15) | 7) + 1 = r + round_up8 (16 + VS); bnez (r' & 3): never;
     0x84820 j 0x847c4            FIND at r' with fuel n;
     0x84848 .. 0x84858           VS again, bnez (VS >> 20) -> EPI (s4 = 0);
     0x8485c .. 0x84878           the instrumented lw of the value type at P + r + 12, bne 14 -> EPI (s4 = 0);
     0x8487c andi a0,s6,3         decided by the engine (atom 11 = P + r is 8-aligned): 0x848e0;
     0x848e0 .. 0x8490c           the walk setup: s8 = s4 = s9 = 0, [spa + 40] = 0, a4 = s7 = [spa + 32] = P + r + 16,
                                  a5 = 8, [spa + 16] = (s6 & 7) + 3 = 3, and `fmv.d.x fs0,zero` 0x848fc (one concrete
                                  step, lib/A/HPgParseGFstep.v) -> WALK 0x84910 at the Struct's first child.
   The engine runs from an entry state of two regions: the frame temporaries [spa, spa + 0x40) at sp (atom 2,
   writable) and, when r + 16 <= len, the property header [P + r, P + r + 16) at a1 (atom 11, read-only; atoms 33 .. 35
   its key, value size and value type) with its shadow entry; every instrumented check reads the pod's shadow.
   Every exit gives the cut's hp_core by lib/A/HPgParseGKit.v hk_core_frame (writes only in [spa, spa + 0x40)); the
   model steps are lib/A/HPgParseGFind.v's. Section hypothesis: errno_low : api_env rsegs B. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseCut HPgParseFP HPgParseGFstep HPgParseGFind HPgParseGKit HPgParseGWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation pctx := (@hp_ctx rsegs).

(* ======================================= the engine's frame ======================================= *)
(* the env of the segment: slots 0 .. 31 the registers at FIND, 32 the shadow base (s11 = atom 27 holds it at every
   cut; the shadow checks use lib/A/HPgParseGKit.v hk_Bx, hk_Bspan), 33 .. 35 the property's key, value size and value
   type (the u32 at P + r, P + r + 8, P + r + 12) *)
Definition hfa_env (regs : bvmap 5 word) (L : list word) : env := Ereg regs (w64 SHADOW_OFF :: L).
Definition hfa_L (x : pctx) (r : Z) : list word :=
[w64 (Spa.u32_at (hx_bs x) r); w64 (Spa.u32_at (hx_bs x) (r + 8)); w64 (Spa.u32_at (hx_bs x) (r + 12))].
(* the frame temporaries [spa, spa + 0x40) below the frame object (the walk setup's stores at spa + 16, 32, 40) *)
Definition hfa_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 0x40 0 0x40 [].
(* the property header [P + r, P + r + 16) at atom 11 (a1), read-only *)
Definition hfa_pod : YP09.region :=
YP09.mkRegion (Some 11%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 8 (CVal 4 (SOff 34 0)); YP09.mkChunk 12 (CVal 4 (SOff 35 0))].
Definition hfa_factsA : facts :=
mkFacts [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5); (11%nat, mkAF 0 (2 ^ 47 - 17) 3); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
  [] [].
Definition hfa_factsB : facts := mkFacts [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition hfa_ssA : sstate := mkSS PC_FIND sr_atoms [hfa_frame; hfa_pod] None hfa_factsA.
Definition hfa_ssB : sstate := mkSS PC_FIND sr_atoms [hfa_frame] None hfa_factsB.
Definition hfa_shA : list shent := [mkSHE 11 0 16].

Lemma hfa_env_reg : forall regs L (n : nat) (q : bv 5), Z.of_nat n = bv_unsigned q -> ew (hfa_env regs L) n = getr regs q.
Proof. intros regs L n q H. unfold hfa_env. apply ew_Ereg_nat. exact H. Qed.
Lemma hfa_env_seg : forall regs L j, ew (hfa_env regs L) (33 + j) = nth j L (Z_to_bv 64 0).
Proof.
intros regs L j. unfold hfa_env. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ---- a run keeps every byte outside the frame temporaries ---- *)
Lemma hfa_kept : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mrestrict H m1 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a)) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a).
Proof.
intros E rs H m0 m1 m2 lo hi HK HF HW a Ha Hn.
rewrite <- (HK a Ha Hn). apply HF. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.

Lemma hfa_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. repeat split; reflexivity. Qed.
Ltac hfa_kio := let rec go := first [ apply same_io_refl | (eapply same_io_trans; [| apply hfa_same_io_wvb]); go ] in go.

Section fs. Context {fs : YK11.FPState}.
(* a register the walk did not touch: still the one it entered with *)
Lemma hfa_reg_of : forall regs L E ss ms (H : word -> bool) (q : bv 5) (n : nat),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 ->
env_agree 36 (hfa_env regs L) E -> (n < 32)%nat -> Z.of_nat n = bv_unsigned q ->
getr (ms_regs ms) q = getr regs q.
Proof.
intros regs L E ss ms H q n HS Hsr HAE Hn Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms q HS), Hsr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (proj1 HAE n ltac:(lia)).
apply hfa_env_reg. exact Hq.
Qed.

(* a cell the walk stored in its frame region (the first region, at sp) *)
Lemma hfa_frame_val : forall E ss ms (H : word -> bool) rest cs off (n : N) e v,
st_ok rsegs E ss (restrict H ms) -> ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x40 0 0x40 cs :: rest ->
In (YP09.mkChunk off (CVal n e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) (N.to_nat n) v.
Proof.
intros E ss ms H rest cs off n e v HS Hm Hin He Hv Hn.
pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. inversion HF as [|r0 l0 HR _]; subst.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply (val_of_chunk_ok rsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
rewrite Forall_forall in HC. exact (HC _ Hin).
Qed.
End fs.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.


Lemma hfa_cap : forall x : pctx, call_ok B x -> 0 <= hx_cap x <= 9.
Proof. intros x (_ & _ & _ & _ & _ & _ & (_ & Hcap & _)). exact Hcap. Qed.

(* the call's facts the segment uses *)
Lemma hfa_call : forall x : pctx, call_ok B x -> hx_null x = 0 ->
0x7fff7f800000 + 12288 <= hx_spa x /\ hx_spa x + 0x100 <= hx_sp x /\ hx_sp x - 0x120 < hx_spa x /\
hx_spa x mod 32 = 0 /\ hx_sp0 x - hx_STK x + 12288 <= hx_spa x /\ hx_sp x <= hx_sp0 x /\ hx_sp0 x <= 2 ^ 47 /\
ly_stk_lo (hx_lyc x) <= hx_spa x /\
0 < hx_P x /\ hx_P x mod 16 = 0 /\ 8 <= hx_len x <= 16384 /\ hx_len x mod 8 = 0 /\ hx_SZ x = hx_len x - 8 /\
amem_range (hx_P x) (hx_len x + 8) /\ hd_off_stack (hx_regs x) T_parse_STK (hx_P x) (hx_len x) /\
0 <= hx_cap x <= 9.
Proof.
intros x (HPRE & _ & _ & _ & _ & _ & HA) Hn.
pose proof (hd_parse_frame rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x)
  (hx_md0 x) (hx_own x) (hx_k x) (hx_regs x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x) HPRE)
  as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
pose proof HPRE as (HJ & _ & _ & _ & _ & _ & Hw1 & Hw2 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct HA as (Hpod & Hcap & _).
destruct (Hpod Hn) as (HP0 & HP16 & HL & HL8 & HSZ & _ & _ & _ & _ & _ & _ & _ & _ & HAM & HOS).
unfold hx_spa, hx_sp, hx_len, hx_SZ, hd_fr, T_parse_STK, T_PARSE_FRAME, ESTACK in *.
repeat split; first [assumption | lia].
Qed.

(* the cut core after runs that wrote only the frame temporaries [spa, spa + 0x40) (lib/A/HPgParseGKit.v
   hk_core_frame at the FIND cut's cells and res bytes) *)
Lemma hfa_core_frame : forall x regs mem md regs2 mem2 md2, call_ok B x ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
 mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 -> hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs2 mem2 md2.
Proof.
intros x regs mem md regs2 mem2 md2 Hc Hcore KW HJ2 Hio HCR2.
pose proof (hfa_cap x Hc) as Hcap.
exact (hk_core_frame B pa_segs_low x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md regs2 mem2 md2 0 0x40 errno_low Hc Hcore
  ltac:(cbn [length Z.of_nat]; lia) eq_refl ltac:(lia) ltac:(lia) KW HJ2 Hio HCR2).
Qed.

(* ======================================= the entry states ======================================= *)
(* (A) the property header [P + r, P + r + 16) lies in the pod: the frame temporaries and the header (atoms 33 .. 35
   its key, value size and value type), and the header's shadow entry; (B) it does not: the frame alone. *)
Lemma hfa_entryA : forall x r F fc regs mem md, call_ok B x -> hx_null x = 0 ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md ->
getr regs 11 = w64 (hx_P x + r) -> 16 <= r -> r mod 8 = 0 -> r + 16 <= hx_len x ->
st_ok (fx := mkFP F fc) rsegs (hfa_env regs (hfa_L x r)) hfa_ssA
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_FIND) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx hfa_shA (hfa_env regs (hfa_L x r)) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r F fc regs mem md Hc Hn Hcore H11 Hr16 Hr8 Hin.
pose proof (hfa_call x Hc Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md errno_low Hc Hn Hcore
  ltac:(cbn [length Z.of_nat]; lia)) as (HG & HRA & _).
pose proof Hcore as ((HJ0 & HOK & _) & _ & _ & _ & _ & _ & _ & H2 & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 (proj1 HJ0))) as LO.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (P7 (hx_P x + r) ltac:(lia)) as O1. pose proof (P7 (hx_P x + r + 15) ltac:(lia)) as O2.
change (spZ (hx_regs x)) with (hx_sp x) in O1, O2. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in O1, O2.
pose proof (hgw_u32_range (hx_bs x) r) as R0.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as R8.
pose proof (hgw_u32_range (hx_bs x) (r + 12)) as R12.
assert (E2 : bv_unsigned (ew (hfa_env regs (hfa_L x r)) 2) = hx_spa x).
{ rewrite (hfa_env_reg regs _ 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E11 : ew (hfa_env regs (hfa_L x r)) 11 = Z_to_bv 64 (hx_P x + r)).
{ rewrite (hfa_env_reg regs _ 11 11%bv eq_refl), H11. reflexivity. }
assert (B11 : bv_unsigned (ew (hfa_env regs (hfa_L x r)) 11) = hx_P x + r).
{ rewrite E11. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in P6. lia. }
assert (E27 : ew (hfa_env regs (hfa_L x r)) 27 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (hfa_env_reg regs _ 27 27%bv eq_refl), H27. reflexivity. }
assert (B27 : bv_unsigned (ew (hfa_env regs (hfa_L x r)) 27) = SHADOW_OFF).
{ rewrite E27. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (E33 : ew (hfa_env regs (hfa_L x r)) 33 = Z_to_bv 64 (Spa.u32_at (hx_bs x) r))
  by exact (hfa_env_seg regs (hfa_L x r) 0).
assert (E34 : ew (hfa_env regs (hfa_L x r)) 34 = Z_to_bv 64 (Spa.u32_at (hx_bs x) (r + 8)))
  by exact (hfa_env_seg regs (hfa_L x r) 1).
assert (E35 : ew (hfa_env regs (hfa_L x r)) 35 = Z_to_bv 64 (Spa.u32_at (hx_bs x) (r + 12)))
  by exact (hfa_env_seg regs (hfa_L x r) 2).
rewrite restrict_mkst_fx. split.
- unfold hfa_ssA, hfa_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs); fold (hfa_env regs (hfa_L x r)).
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold region_ok, hfa_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. split; [lia|]. split; [unfold amem_range, kHighMemEnd in *; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs).
      assert (Hu : in_ush (hU (hx_fr x) PAT_KEY) (bv_unsigned (Z_to_bv 64 (hx_spa x + o))) = false)
        by (eapply hole_free_stack; [exact LO | exact HOK | lia]).
      apply (proj1 (hp_apresent_unp _ _ _ _ Hu)). apply Hpres. lia.
    * unfold region_ok, hfa_pod. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite B11. split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in P6; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 33 0) (Spa.u32_at (hx_bs x) r));
           [rewrite hk_sv_SOff0; exact E33 | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) r HG); unfold hx_len in Hin; lia.
      -- apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 34 0) (Spa.u32_at (hx_bs x) (r + 8)));
           [rewrite hk_sv_SOff0; exact E34 | cbn; lia | cbn; lia |].
         replace (hx_P x + r + 8) with (hx_P x + (r + 8)) by lia. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (r + 8) HG); unfold hx_len in Hin; lia.
      -- apply (chunk_ok_val rsegs _ _ _ 12 4 (SOff 35 0) (Spa.u32_at (hx_bs x) (r + 12)));
           [rewrite hk_sv_SOff0; exact E35 | cbn; lia | cbn; lia |].
         replace (hx_P x + r + 12) with (hx_P x + (r + 12)) by lia. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (r + 12) HG); unfold hx_len in Hin; lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, hfa_frame, hfa_pod.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, B11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]]. cbn [hfa_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, B11, B27. unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    repeat split; lia.
- unfold sh_ok, hfa_shA. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H (hx_W x)) mem _ hk_Bx 11 (hx_P x) (hx_len x) (hx_P x + r) 0 16 HRA).
  + unfold hk_Bx. apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
  + apply (U_atom _ 11 (hx_P x + r) E11). unfold amem_range, kLowMemEnd, kHighMemEnd in P6. lia.
  + lia.
  + lia.
  + intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma hfa_entryB : forall x F fc regs mem md, call_ok B x -> hx_null x = 0 ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md ->
st_ok (fx := mkFP F fc) rsegs (hfa_env regs []) hfa_ssB
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_FIND) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx [] (hfa_env regs []) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x F fc regs mem md Hc Hn Hcore.
pose proof (hfa_call x Hc Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
pose proof Hcore as ((HJ0 & HOK & _) & _ & _ & _ & _ & _ & _ & H2 & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 (proj1 HJ0))) as LO.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (E2 : bv_unsigned (ew (hfa_env regs []) 2) = hx_spa x).
{ rewrite (hfa_env_reg regs _ 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E27 : ew (hfa_env regs []) 27 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (hfa_env_reg regs _ 27 27%bv eq_refl), H27. reflexivity. }
assert (B27 : bv_unsigned (ew (hfa_env regs []) 27) = SHADOW_OFF).
{ rewrite E27. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx. split; [|constructor].
unfold hfa_ssB, hfa_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs); fold (hfa_env regs []).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, hfa_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable rsegs).
  assert (Hu : in_ush (hU (hx_fr x) PAT_KEY) (bv_unsigned (Z_to_bv 64 (hx_spa x + o))) = false)
    by (eapply hole_free_stack; [exact LO | exact HOK | lia]).
  apply (proj1 (hp_apresent_unp _ _ _ _ Hu)). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region, hfa_frame.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [hfa_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, B27. unfold SHADOW_OFF in *. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
  repeat split; lia.
Qed.

(* ======================================= the walk's plumbing ======================================= *)
Ltac hfa_B2 HAE B20 E B2 :=
lazymatch type of B20 with bv_unsigned (ew _ 2) = ?F =>
assert (B2 : bv_unsigned (ew E 2) = F) by (first [exact B20 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20]) end.
(* the write set of a run: the frame temporaries lie in the caller's stack window; the header is read-only *)
Ltac hfa_awr x HAE B20 :=
lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
let B2 := fresh "B2" in hfa_B2 HAE B20 E B2;
apply awr_okH_of_ok;
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (hx_spa x - sp0)); [reflexivity | rewrite B2; lia | cbn; lia | cbn; lia |] ]
end.
(* after a run: every byte outside the frame temporaries as at FIND *)
Ltac hfa_keep HAE B20 :=
lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _),
  KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ =>
let B2 := fresh "B2" in hfa_B2 HAE B20 E B2;
let KS := fresh "KS" in
pose proof (hfa_kept _ _ _ _ _ _ _ _ KW HFr) as KS;
lazymatch type of KS with ?P -> _ => let KX := fresh "KX" in assert (KX : P) by (
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb);
  lazymatch type of Hrg with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hrg end;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; first [rewrite B2 in Hb; lia | lia] | ]);
  destruct Hrg);
  specialize (KS KX); clear KX KW HFr B2; rename KS into KW end
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hfa_upd HAE :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
let H := fresh in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE end end.
Ltac hfa_run x HAE B20 :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokH pa_tbl_ok HS HJ SHOK hk_Bspan; [ idtac .. | hfa_awr x HAE B20 | hfa_keep HAE B20; hfa_upd HAE] end.
Ltac hfa_run_to x HAE B20 stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokH pa_tbl_ok HS HJ SHOK hk_Bspan stop; [ idtac .. | hfa_awr x HAE B20 | hfa_keep HAE B20; hfa_upd HAE] end.
Ltac hfa_br Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pa_tbl_ok HS SH hk_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac hfa_hc HAE H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
tryif constr_eq E0 E then idtac else (repeat (rewrite (U_agree k E0 E _ HAE) in H by (vm_compute; reflexivity))) end.

(* ======================================= the cuts the segment reaches ======================================= *)
Lemma hfa_to_EPI : forall x F fc regs mem md regs2 mem2 md2, call_ok B x ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md -> hp_fx F fc ->
hx_ans x = (0, [], (0, 0, 0)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
 mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 -> getr regs2 20 = w64 0 ->
EPI_at B x F fc regs2 mem2 md2.
Proof.
intros x F fc regs mem md regs2 mem2 md2 Hc Hcore Hfx Hans HK HJ Hio HCR H20.
unfold EPI_at. rewrite Hans. cbn [ans_cells ans_res_bytes ans_rc ans_n ans_keys ans_rf fst snd].
split; [|split; [exact Hfx | exact H20]].
exact (hfa_core_frame x regs mem md regs2 mem2 md2 Hc Hcore HK HJ Hio HCR).
Qed.

Lemma hfa_to_FIND : forall x r' n F fc regs mem md regs2 mem2 md2, call_ok B x ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md -> hp_fx F fc -> hp_m_find x r' n ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
 mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 ->
getr regs2 10 = w64 (hx_P x + 8) -> getr regs2 11 = w64 (hx_P x + r') -> getr regs2 12 = w64 (hx_SZ x - 16) ->
getr regs2 13 = w64 (hx_P x + hx_SZ x - 8) -> getr regs2 14 = w64 Model.POD_PROP_PARAMS -> getr regs2 20 = w64 0 ->
FIND_at B x r' n F fc regs2 mem2 md2.
Proof.
intros x r' n F fc regs mem md regs2 mem2 md2 Hc Hcore Hfx Hm HK HJ Hio HCR H10 H11 H12 H13 H14 H20.
unfold FIND_at.
split; [exact (hfa_core_frame x regs mem md regs2 mem2 md2 Hc Hcore HK HJ Hio HCR)|].
repeat (split; [assumption|]). assumption.
Qed.

Lemma hfa_to_WALK : forall x r F' fc regs mem md regs2 mem2 md2, call_ok B x ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md -> hp_fxw F' fc ->
hp_m_walk x r (r + 16) (length (hx_bs x)) None [] 0 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
 mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 ->
pa_loop x r [] 0 regs2 mem2 -> pa_a45 x r regs2 ->
getr regs2 23 = w64 (hx_P x + (r + 16)) -> getr regs2 24 = w64 0 -> getr regs2 25 = w64 0 ->
WALK_at B x r (r + 16) (length (hx_bs x)) None [] 0 0 F' fc regs2 mem2 md2.
Proof.
intros x r F' fc regs mem md regs2 mem2 md2 Hc Hcore Hfx Hm HK HJ Hio HCR HL H45 H23 H24 H25.
unfold WALK_at.
split; [exact (hfa_core_frame x regs mem md regs2 mem2 md2 Hc Hcore HK HJ Hio HCR)|].
cbn [hp_keyv]. repeat (split; [assumption|]). assumption.
Qed.

(* fs0 after `fmv.d.x fs0,zero`: +0.0, every other float register as at the cut *)
Lemma hfa_fxw : forall F fc (rd : bv 5) (v : word), hp_fx F fc -> bv_unsigned rd = 8 -> v = Z_to_bv 64 0 ->
hp_fxw (bvmap_set rd v F) fc.
Proof.
intros F fc rd v (HK & Hz) Hrd Hv. split; [split|].
- intros k Hk. cbn [fp_regs]. rewrite FP.freg_get_other; [apply HK; exact Hk|].
  unfold bv_eqb. apply Z.eqb_neq. rewrite Hrd. intros E. apply Hk. rewrite <- E. cbn. tauto.
- exact Hz.
- rewrite FP.freg_get_same; [exact Hv | rewrite Hrd; reflexivity].
Qed.

(* a register goal at the end of a run, reduced to the U value of its symbolic value in the segment's entry env *)
Ltac hfa_rg HAE :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) q) in
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with e;
  unfold w64; rewrite denot_lit_U; f_equal;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (U_agree k E0 E e HAE ltac:(vm_compute; reflexivity)) end
end end.
(* a register the run kept *)
Ltac hfa_rkeep regs L HAE n q :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
  rewrite (hfa_reg_of regs L E ss ms (w_H W) q n HS ltac:(vm_compute; reflexivity) HAE ltac:(lia)
                   ltac:(vm_compute; reflexivity))
end.
Ltac hfa_cregs regs L HAE HCR :=
apply (hk_cregs_same _ regs _ HCR);
[ hfa_rkeep regs L HAE 2%nat (2%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 3%nat (3%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 4%nat (4%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 8%nat (8%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 9%nat (9%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 18%nat (18%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 19%nat (19%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 26%nat (26%bv : bv 5); reflexivity
| hfa_rkeep regs L HAE 27%nat (27%bv : bv 5); reflexivity ].

Lemma hfa_land3 : forall a, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(* ======================================= the segment ======================================= *)
(* exits: EPI with the answer (0, [], (0, 0, 0)) *)
Ltac hfa_epi x regs L HAE HCR Hans HEPI :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)) end;
eapply HEPI;
eapply hfa_to_EPI;
[ eassumption | eassumption | eassumption | exact Hans
| lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end
| lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end
| hfa_kio
| hfa_cregs regs L HAE HCR
| first [ hfa_rg HAE; rewrite U_lit by lia; reflexivity
        | hfa_rkeep regs L HAE 20%nat (20%bv : bv 5); assumption ] ].

Theorem hp_segFIND_A : segFIND_stmt B MT.
Proof.
unfold segFIND_stmt, FIND_ok. intros x r n Hc HFIND HEPI HEXIT HWALK F fc regs mem md HF.
unfold EPI_ok, WALK_ok, cfg_at in *. clear HEXIT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct HF as (Hcore & Hfx & Hm & H10 & H11 & H12 & H13 & H14 & H20).
pose proof Hm as (Hn & Hobj & HS16 & Hr & Hr8 & Hfuel & Hres).
pose proof (hfa_call x Hc Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
pose proof Hcore as ((HJ & HOK & HPAT) & _ & _ & _ & _ & _ & _ & H2 & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof (hgw_u32_range (hx_bs x) r) as R0.
pose proof (hgw_u32_range (hx_bs x) (r + 8)) as R8.
pose proof (hgw_u32_range (hx_bs x) (r + 12)) as R12.
assert (HPL : 0 < hx_P x /\ hx_P x + hx_len x + 8 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemEnd in P6; lia).
change (w64 PC_FIND) with (Z_to_bv 64 PC_FIND).
destruct (Z_le_gt_dec (r + 16) (hx_len x)) as [Hin|Hout].
- (* (A) the property header lies in the pod *)
  destruct (hfa_entryA x r F fc regs mem md Hc Hn Hcore H11 ltac:(lia) Hr8 Hin) as [HS SHOK].
  assert (HAE : env_agree 36 (hfa_env regs (hfa_L x r)) (hfa_env regs (hfa_L x r))) by apply env_agree_refl.
  assert (B20 : bv_unsigned (ew (hfa_env regs (hfa_L x r)) 2) = hx_spa x).
  { rewrite (hfa_env_reg regs _ 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
    mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
  assert (U10 : U (hfa_env regs (hfa_L x r)) (SOff 10 0) = hx_P x + 8)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 10 10%bv eq_refl), H10; reflexivity | lia]).
  assert (U11 : U (hfa_env regs (hfa_L x r)) (SOff 11 0) = hx_P x + r)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 11 11%bv eq_refl), H11; reflexivity | lia]).
  assert (U12 : U (hfa_env regs (hfa_L x r)) (SOff 12 0) = hx_SZ x - 16)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 12 12%bv eq_refl), H12; reflexivity | lia]).
  assert (U13 : U (hfa_env regs (hfa_L x r)) (SOff 13 0) = hx_P x + hx_SZ x - 8)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 13 13%bv eq_refl), H13; reflexivity | lia]).
  assert (U14 : U (hfa_env regs (hfa_L x r)) (SOff 14 0) = 524289)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 14 14%bv eq_refl), H14; reflexivity | lia]).
  assert (U27 : U (hfa_env regs (hfa_L x r)) (SOff 27 0) = SHADOW_OFF)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia]).
  assert (U33 : U (hfa_env regs (hfa_L x r)) (SOff 33 0) = Spa.u32_at (hx_bs x) r)
    by (apply U_atom; [exact (hfa_env_seg regs (hfa_L x r) 0) | lia]).
  assert (U34 : U (hfa_env regs (hfa_L x r)) (SOff 34 0) = Spa.u32_at (hx_bs x) (r + 8))
    by (apply U_atom; [exact (hfa_env_seg regs (hfa_L x r) 1) | lia]).
  assert (U35 : U (hfa_env regs (hfa_L x r)) (SOff 35 0) = Spa.u32_at (hx_bs x) (r + 12))
    by (apply U_atom; [exact (hfa_env_seg regs (hfa_L x r) 2) | lia]).
  assert (E11 : ew (hfa_env regs (hfa_L x r)) 11 = Z_to_bv 64 (hx_P x + r))
    by (rewrite (hfa_env_reg regs _ 11 11%bv eq_refl), H11; reflexivity).
  assert (U11_8 : U (hfa_env regs (hfa_L x r)) (SOff 11 8) = hx_P x + r + 8)
    by (rewrite (U_atom_off _ 11 (hx_P x + r) 8 E11 ltac:(lia) ltac:(lia)); lia).
  assert (U11_16 : U (hfa_env regs (hfa_L x r)) (SOff 11 16) = hx_P x + r + 16)
    by (rewrite (U_atom_off _ 11 (hx_P x + r) 16 E11 ltac:(lia) ltac:(lia)); lia).
  assert (Uz34 : U (hfa_env regs (hfa_L x r)) (SExt false 32 (SOff 34 0)) = Spa.u32_at (hx_bs x) (r + 8)).
  { rewrite U_zext, U34. change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_small. lia. }
  assert (Uc0 : U (hfa_env regs (hfa_L x r)) (SLit 0) = 0) by (apply U_lit; lia).
  assert (Uc1 : U (hfa_env regs (hfa_L x r)) (SLit 1) = 1) by (apply U_lit; lia).
  assert (Uc3 : U (hfa_env regs (hfa_L x r)) (SLit 3) = 3) by (apply U_lit; lia).
  assert (Uc7 : U (hfa_env regs (hfa_L x r)) (SLit 7) = 7) by (apply U_lit; lia).
  assert (Uc8 : U (hfa_env regs (hfa_L x r)) (SLit 8) = 8) by (apply U_lit; lia).
  assert (Uc14 : U (hfa_env regs (hfa_L x r)) (SLit 14) = 14) by (apply U_lit; lia).
  assert (Uc15 : U (hfa_env regs (hfa_L x r)) (SLit 15) = 15) by (apply U_lit; lia).
  assert (Uc20 : U (hfa_env regs (hfa_L x r)) (SLit 20) = 20) by (apply U_lit; lia).
  (* 0x847c4 bltu a1,a0: P + r < P + 8 never *)
  hfa_run x HAE B20. hfa_br Hb1.
  { exfalso. hfa_hc HAE Hb1. rewrite U11, U10 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  clear Hb1.
  (* 0x847c8 sub a5,a1,a0; 0x847cc bltu a2,a5: SZ - 16 < r - 8 never here *)
  hfa_run x HAE B20. hfa_br Hb2.
  { exfalso. hfa_hc HAE Hb2. rewrite hpf_U_sub_l, U11, U10, U12 in Hb2.
    replace (hx_P x + r - (hx_P x + 8)) with (r - 8) in Hb2 by lia. rewrite (Z.mod_small (r - 8)) in Hb2 by lia.
    apply Z.ltb_lt in Hb2. lia. }
  clear Hb2.
  (* 0x847d0 .. 0x847e4: the instrumented lwu of the value size; 0x847e8 sub a6,a3,a1; 0x847ec bltu a6,a5 *)
  hfa_run x HAE B20. hfa_br Hb3; hfa_hc HAE Hb3; rewrite hpf_U_sub_l, U13, U11, Uz34 in Hb3;
  replace (hx_P x + hx_SZ x - 8 - (hx_P x + r)) with (hx_SZ x - 8 - r) in Hb3 by lia;
  rewrite (Z.mod_small (hx_SZ x - 8 - r)) in Hb3 by lia.
  { (* taken: the value does not fit; 0x84734 li s4,0; EPI with the answer 0 *)
    apply Z.ltb_lt in Hb3.
    pose proof (hpf_find_out x r n Hm ltac:(right; unfold hp_vs; lia)) as Hans.
    hfa_run_to x HAE B20 PC_EPI. hfa_epi x regs (hfa_L x r) HAE HCR Hans HEPI. }
  apply Z.ltb_ge in Hb3.
  (* 0x847f0 .. 0x84800: the instrumented lw of the key; 0x84804 beq a6,a4 *)
  hfa_run x HAE B20. hfa_br Hb4; hfa_hc HAE Hb4;
  rewrite U14, (hpf_U_sx32_eqb _ _ _ 524289 U33 R0 ltac:(lia)) in Hb4.
  { (* taken: the key is SPA_PROP_params *)
    apply Z.eqb_eq in Hb4.
    (* 0x84848 .. 0x84854: the size again; 0x84858 bnez (size >> 20) *)
    hfa_run x HAE B20. hfa_br Hb5; hfa_hc HAE Hb5;
    rewrite Uc0 in Hb5; rewrite hpf_U_srl in Hb5 by (rewrite Uc20; lia); rewrite Uz34, Uc20 in Hb5.
    { (* taken: size >= 2^20, not a Struct; EPI with the answer 0 *)
      apply negb_true_iff, Z.eqb_neq in Hb5.
      assert (HB20 : Spa.SPA_POD_MAX_SIZE <= hp_vs x r).
      { unfold Spa.SPA_POD_MAX_SIZE, hp_vs. change (2 ^ 20) with 1048576 in *. lia. }
      pose proof (hpf_find_nostruct x r n Hm ltac:(lia) ltac:(unfold hp_vs; lia) Hb4 (or_introl HB20)) as Hans.
      hfa_run_to x HAE B20 PC_EPI. hfa_epi x regs (hfa_L x r) HAE HCR Hans HEPI. }
    apply negb_false_iff, Z.eqb_eq in Hb5.
    assert (HB20 : hp_vs x r < Spa.SPA_POD_MAX_SIZE).
    { unfold Spa.SPA_POD_MAX_SIZE, hp_vs. change (2 ^ 20) with 1048576 in *. lia. }
    (* 0x8485c .. 0x84870: the instrumented lw of the value type; 0x84878 bne a0,a1 (type <> 14) *)
    hfa_run x HAE B20. hfa_br Hb6; hfa_hc HAE Hb6;
    rewrite Uc14, (hpf_U_sx32_eqb _ _ _ 14 U35 R12 ltac:(lia)) in Hb6.
    { (* taken: not a Struct; EPI with the answer 0 *)
      apply negb_true_iff, Z.eqb_neq in Hb6.
      pose proof (hpf_find_nostruct x r n Hm ltac:(lia) ltac:(unfold hp_vs; lia) Hb4 (or_intror Hb6)) as Hans.
      hfa_run_to x HAE B20 PC_EPI. hfa_epi x regs (hfa_L x r) HAE HCR Hans HEPI. }
    apply negb_false_iff, Z.eqb_eq in Hb6.
    pose proof (hpf_find_walk x r n Hm P5 ltac:(lia) ltac:(unfold hp_vs; lia) Hb4 HB20 Hb6 ltac:(lia)) as Hmw.
    assert (Usr : U (hfa_env regs (hfa_L x r)) (SAlu ALU_SRL (SOff 11 8) (SLit 3)) = (hx_P x + r + 8) / 8).
    { rewrite hpf_U_srl by (rewrite Uc3; lia). rewrite U11_8, Uc3. reflexivity. }
    assert (Us5 : U (hfa_env regs (hfa_L x r)) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 8) (SLit 3)) (SOff 27 0)) =
                  shadow_addr (hx_P x + r + 8)).
    { rewrite hpf_U_add by (rewrite Usr, U27; unfold SHADOW_OFF; lia). rewrite Usr, U27. unfold shadow_addr. lia. }
    (* 0x8487c andi a0,s6,3 (decided by the engine: s6 = P + r + 8 is 8-aligned); 0x848e0 .. 0x848f8 the walk
       setup up to the float move *)
    hfa_run_to x HAE B20 0x848fc.
    pose proof (AR_laws_ok rsegs B) as LAWS.
    (* 0x848fc fmv.d.x fs0,zero: one concrete step, then the engine again at the new float state *)
    lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H (hx_W x)) E ss ms HS ltac:(vm_compute; reflexivity)) as Ems;
      assert (Hpc : ss_pc ss = 0x848fc) by (vm_compute; reflexivity);
      rewrite Hpc in Ems; rewrite Ems in HS |- *; clear Ems Hpc;
      eapply (hgf_SRr_fmv_d_x rsegs pa_tbl pa_tbl_ok pa_wx F fc (hx_W x) (ms_regs ms) 0x848fc (ms_mem ms) _ _
        0xf2000453 (Z_to_bv 5 8) (Z_to_bv 5 0));
        [vm_compute; reflexivity | vm_compute; reflexivity | first [vm_compute; reflexivity | vm_refl_bv] |];
      let md' := fresh "md" in let Hsame := fresh "Hsame" in intros md' Hsame;
      change (getr (ms_regs ms) (Z_to_bv 5 0)) with (Z_to_bv 64 0);
      pose proof (hgf_st_ok_freg rsegs F (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 0) F) fc E ss
        (w_H (hx_W x)) (ms_regs ms) (ms_mem ms) HS) as HS2;
      clear HS; rename HS2 into HS;
      lazymatch type of HJ with ajournal ?segs ?B ?STK ?sp0 ?FP ?ly ?S ?W0 ?m0 ?d0 ?own ?lyc ?Sc ?W ?mm ?mdc ?k =>
        assert (HJ2 : ajournal segs B STK sp0 FP ly S W0 m0 d0 own lyc Sc W mm
          (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized md') mdc) k)
          by (eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ]) end;
      clear HJ; rename HJ2 into HJ; rewrite (same_but_materialized_wvb _ _ Hsame); clear Hsame
    end.
    (* 0x84900 .. 0x8490c: [spa + 16] = (s6 & 7) + 3, s7 = [spa + 32] = P + r + 16; WALK at the first child *)
    hfa_run_to x HAE B20 PC_WALK.
    lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
      assert (B2 : bv_unsigned (ew E 2) = hx_spa x) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20);
      let m := eval vm_compute in (ss_mem ss) in
      lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
        assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x40 0 0x40 cs :: rest) by (vm_compute; reflexivity);
        pose proof (fun off e v => hfa_frame_val E ss ms (w_H (hx_W x)) rest cs off 8%N e v HS Hmem) as HFV
      end;
      rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity))
    end.
    eapply (HWALK r (r + 16) (length (hx_bs x)) None [] 0 0).
    eapply hfa_to_WALK; [ exact Hc | exact Hcore | | exact Hmw | exact KW | exact HJ | hfa_kio
      | hfa_cregs regs (hfa_L x r) HAE HCR | | | | | ].
    + apply hfa_fxw; [exact Hfx | reflexivity | reflexivity].
    + unfold pa_loop.
      split; [hfa_rg HAE; exact Uc0|].
      split; [hfa_rg HAE; exact Us5|].
      split; [hfa_rg HAE; exact U11_8|].
      split; [rewrite <- B2; replace ((hx_P x + r + 8) mod 8 + 3) with 3 by lia;
              apply (HFV 16 (SLit 3) 3); [cbn [In]; auto | reflexivity | cbn; lia | cbn; lia]|].
      split; [rewrite <- B2;
              apply (HFV 32 (SOff 11 16) (hx_P x + r + 16)); [cbn [In]; auto | | cbn; lia | cbn; lia]|].
      { rewrite denot_lit_U. f_equal.
        rewrite (U_agree 36 _ _ (SOff 11 16) HAE ltac:(vm_compute; reflexivity)). exact U11_16. }
      rewrite <- B2. apply (HFV 40 (SLit 0) 0); [cbn [In]; auto | reflexivity | cbn; lia | cbn; lia].
    + unfold pa_a45. split; [hfa_rg HAE; exact U11_16 | hfa_rg HAE; exact Uc8].
    + hfa_rg HAE. rewrite U11_16. lia.
    + hfa_rg HAE; exact Uc0.
    + hfa_rg HAE; exact Uc0. }
  (* not taken: the key is not SPA_PROP_params; the next property at r' = r + round_up8 (16 + VS) *)
  apply Z.eqb_neq in Hb4.
  pose proof (hpf_ru8 (Spa.u32_at (hx_bs x) (r + 8)) ltac:(lia)) as (RU0 & RU1 & RU2).
  assert (Uad : U (hfa_env regs (hfa_L x r)) (SAlu ALU_ADD (SExt false 32 (SOff 34 0)) (SLit 15)) =
                Spa.u32_at (hx_bs x) (r + 8) + 15).
  { rewrite hpf_U_add by (rewrite Uz34, Uc15; lia). rewrite Uz34, Uc15. reflexivity. }
  assert (Ur' : U (hfa_env regs (hfa_L x r))
                  (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0)
                     (SAlu ALU_OR (SAlu ALU_ADD (SExt false 32 (SOff 34 0)) (SLit 15)) (SLit 7))) (SLit 1)) =
                hx_P x + (r + Spa.round_up8 (16 + Spa.u32_at (hx_bs x) (r + 8)))).
  { rewrite (hpf_U_next _ _ _ (hx_P x + r) (Spa.u32_at (hx_bs x) (r + 8)) U11 Uad ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  (* 0x84808 .. 0x84818; 0x8481c bnez (r' & 3): never *)
  hfa_run x HAE B20. hfa_br Hb7.
  { exfalso. hfa_hc HAE Hb7. rewrite Uc0, (U_and_lit _ _ 3 ltac:(lia)), Ur', hfa_land3 in Hb7.
    apply negb_true_iff, Z.eqb_neq in Hb7. apply Hb7. lia. }
  clear Hb7.
  (* 0x84820 j 0x847c4: FIND at r' with fuel n *)
  hfa_run_to x HAE B20 PC_FIND.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)) end.
  eapply (HFIND (r + Spa.round_up8 (16 + hp_vs x r))).
  eapply hfa_to_FIND; [ exact Hc | exact Hcore | exact Hfx
    | exact (hpf_find_next x r n Hm P5 ltac:(lia) ltac:(unfold hp_vs; lia) Hb4)
    | exact KW | exact HJ | hfa_kio | hfa_cregs regs (hfa_L x r) HAE HCR | | | | | | ].
  + hfa_rkeep regs (hfa_L x r) HAE 10%nat (10%bv : bv 5). exact H10.
  + hfa_rg HAE. unfold hp_vs. exact Ur'.
  + hfa_rkeep regs (hfa_L x r) HAE 12%nat (12%bv : bv 5). exact H12.
  + hfa_rkeep regs (hfa_L x r) HAE 13%nat (13%bv : bv 5). exact H13.
  + hfa_rkeep regs (hfa_L x r) HAE 14%nat (14%bv : bv 5). exact H14.
  + hfa_rkeep regs (hfa_L x r) HAE 20%nat (20%bv : bv 5). exact H20.
- (* (B) the property header does not lie in the pod: the loop ends at its bounds test *)
  destruct (hfa_entryB x F fc regs mem md Hc Hn Hcore) as [HS SHOK].
  assert (HAE : env_agree 36 (hfa_env regs []) (hfa_env regs [])) by apply env_agree_refl.
  assert (B20 : bv_unsigned (ew (hfa_env regs []) 2) = hx_spa x).
  { rewrite (hfa_env_reg regs _ 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x40) ->
    mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
  assert (U10 : U (hfa_env regs []) (SOff 10 0) = hx_P x + 8)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 10 10%bv eq_refl), H10; reflexivity | lia]).
  assert (U11 : U (hfa_env regs []) (SOff 11 0) = hx_P x + r)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 11 11%bv eq_refl), H11; reflexivity | lia]).
  assert (U12 : U (hfa_env regs []) (SOff 12 0) = hx_SZ x - 16)
    by (apply U_atom; [rewrite (hfa_env_reg regs _ 12 12%bv eq_refl), H12; reflexivity | lia]).
  assert (Hans : hx_ans x = (0, [], (0, 0, Headamp.REFUSE_NONE)))
    by exact (hpf_find_out x r n Hm ltac:(left; lia)).
  (* 0x847c4 bltu a1,a0: never *)
  hfa_run x HAE B20. hfa_br Hb1.
  { exfalso. hfa_hc HAE Hb1. rewrite U11, U10 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  clear Hb1.
  (* 0x847cc bltu a2,a5: SZ - 16 < r - 8, taken; EPI with the answer 0 *)
  hfa_run x HAE B20. hfa_br Hb2; hfa_hc HAE Hb2; rewrite hpf_U_sub_l, U11, U10, U12 in Hb2;
  replace (hx_P x + r - (hx_P x + 8)) with (r - 8) in Hb2 by lia; rewrite (Z.mod_small (r - 8)) in Hb2 by lia.
  { hfa_run_to x HAE B20 PC_EPI. hfa_epi x regs (@nil word) HAE HCR Hans HEPI. }
  exfalso. apply Z.ltb_ge in Hb2. lia.
Qed.

End b.

Print Assumptions hp_segFIND_A.
