(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v; 260 of its 336 lines of code are new or changed and 2680 lines of the source are left out. *)
(* rule 24: proves no function (kind: helper lemmas of check_round_trip's D1 segment lemma, PORTED from a working branch d25a984c903 check_round_trip_sd16.v / sd17.v / sd18.v)
   This file holds segment 31's bcmp call with the callee's frame clause and md relation handed to the continuation
   (crtD1_bcmp_call), the walk's boundary state crt_ss_ret r crt_cs1 csF rebuilt over the memory after that call
   (crtD1_bcmp_resume), and the call as an empty-footprint callee journal (crtD1_bcmp_journal).

   crtD1_bcmp_call is FSH_crt_base.v's crt_bcmp_call with ONE change: its continuation also receives two facts of
   fr_bcmp's post (FSupoisonU.abcmp_realizesU), the md relation same_but_materialized and the frame clause on the raw
   memory (every byte outside the callee's stack window [sp - 2 * ESTACK, sp) keeps its view). The base's crt_bcmp_call
   drops both, and without them neither the resume state nor the callee journal can be built; the base's lemma should
   gain them (a Theorem Labs lane forwards this to a Theorem Labs lane), after which crtD1_bcmp_call is that lemma.

   crtD1_bcmp_resume takes the call-site state as ANY symbolic state ss whose memory regions are crt_ss_ret's (the
   caller passes its engine state and a vm_compute equation), not as crt_ss_ret 0x82274 itself: YP0l.st_ok asks
   ms_pc_val = Z_to_bv 64 (ss_pc ss), so `st_ok E (crt_ss_ret 0x82274 ..) (.. Z_to_bv 64 PC_bcmp ..)` cannot hold.
   It is generic in the return address r and in the frame chunks csF; it states nothing about a0. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_crt_base.
Import ListNotations.
Local Open Scope Z_scope.

Section d1b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SKfp : YI16.sink_head}.
Variable B : asyms.

(* ---- segment 31's call, bcmp (got, bd, len) through the __wrap_bcmp thunk: crt_bcmp_call's premises and proof, with
   the contract's frame clause (FSupoisonU.abcmp_realizesU, outside [sp - 2 * ESTACK, sp)) also passed to K ---- *)
Lemma crtD1_bcmp_call : forall (ss : sstate) (r : Z) (na : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT got
  (Q : world tfibsegs -> config -> Prop),
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> sr_get (ss_regs ss) 10%bv = SOff na 0 ->
  sr_get (ss_regs ss) 11%bv = SOff 21 0 -> sr_get (ss_regs ss) 12%bv = SOff 20 0 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  YK0s.ret_ok (Z_to_bv 64 r) ->
  CrtRt B ->
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) -> YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))) ->
  let len := Z.of_nat (length (c_bs cx)) in
  bv_unsigned (ew E na) = got -> bv_unsigned (ew E 21) = c_bd cx -> bv_unsigned (ew E 20) = len ->
  0 <= len < 2 ^ 32 -> 0 <= got -> got + len <= 2 ^ 63 -> 0 <= c_bd cx -> c_bd cx + len <= 2 ^ 63 ->
  src_ok tfibsegs W3 regsT memT got len -> src_ok tfibsegs W3 regsT memT (c_bd cx) len ->
  (forall a, got <= a < got + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, c_bd cx <= a < c_bd cx + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range got len -> amem_range (c_bd cx) len ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF got len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) got len) ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_bd cx) len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_bd cx) len) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2 (v : word),
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     same_but_materialized mdT md2 ->
     aregs_preserved regsT regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
        aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
     YK11.getr regs2 10%bv = v ->
     (v = w64 0 <-> forall i, 0 <= i < len ->
        aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i)) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (YK11.getr regsT 1%bv) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na cx E k ly3 S3 U3 W3 regsT memT mdT got Q Sr1 Hr Sr10 Sr11 Sr12 Sr2 Sr3 Sr4 HRet RT HE H16 H0 H47 Hgp Htp HS len Eg Ebd Elen Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb HJ HARU K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & Hsp1_32 & Hsp1_16).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & Eex).
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & Hh47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
(* the registers at the call: a0 = got, a1 = bd, a2 = len, ra = r, sp / gp / tp *)
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G10 : YK11.getr regsT 10%bv = w64 got).
{ rewrite (Rd 10%bv na Sr10). unfold w64. rewrite <- Eg. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G11 : YK11.getr regsT 11%bv = w64 (c_bd cx)).
{ rewrite (Rd 11%bv _ Sr11). unfold w64. rewrite <- Ebd. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G12 : YK11.getr regsT 12%bv = w64 len).
{ rewrite (Rd 12%bv _ Sr12). unfold w64. rewrite <- Elen. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G3 : YK11.getr regsT 3%bv = w64 (as_gp B)) by (rewrite (Rd 3%bv _ Sr3), E3; exact Hgp).
assert (G4 : YK11.getr regsT 4%bv = w64 (as_tp B)) by (rewrite (Rd 4%bv _ Sr4), E4; exact Htp).
assert (GSP : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv _ Sr2); exact E2).
assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 r).
{ exact (fsw_reg_lit (w_H W3) E ss (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) 1%bv r HS Sr1 Hr). }
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite G1; exact HRet).
(* the callee's pre, and the 2 * ESTACK of present stack the contract asks *)
assert (HPRE : FSupoison.ecall_preU tfibsegs B ly3 S3 U3 W3 regsT memT mdT).
{ eapply (fsw_ecall_preU_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k regsT
    (crt_sp1 cx - spZ (c_regs cx)) HJ HARU);
  [lia | rewrite Zminus_mod, H16, Hsp1_16; reflexivity | lia | unfold ESTACK; lia | exact Hra | exact G3
  | exact G4]. }
assert (HSK1 : ly_stk_lo ly3 + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, GSP; unfold ESTACK; lia).
assert (HSK2 : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W3) memT a).
{ intros a Ha. rewrite GSP in Ha. unfold ESTACK in Ha.
  apply (fsw_apresent_unpoison B ly3 S3 U3 W3 memT mdT a HARU); [unfold kHighMemBeg in *; lia|].
  apply Hpres. lia. }
(* the contract *)
pose proof (crt_fr_bcmp B RT ly3 S3 U3 W3 regsT memT mdT got (c_bd cx) len HPRE HSK1 HSK2 G10 G11 G12 Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb) as HC.
change (cfg_at tfibsegs PC_bcmp regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) in HC.
(* the journal back over the call: the write set is the callee's own stack window; the contract's frame clause rides
   along in the callee facts, on the raw memory *)
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => spZ regsT - 2 * ESTACK <= a < spZ regsT) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => same_but_materialized mdT md' /\ aregs_preserved regsT regs' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a) /\
       exists v : word, YK11.getr regs' 10%bv = v /\
       (v = w64 0 <-> forall i, 0 <= i < len ->
          aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i))) HJ).
  - eapply SRr_mono; [exact HC|].
    intros W' c' _ (-> & regs' & mem' & md' & v & Ec & HARU' & HP & Hsame & Hv & Hres & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    split; [exact (crt_unpoison_keep (w_H W3) U3 memT mem' _ Hfr)|].
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact Hsame|]. split; [exact HP|]. split; [exact Hfr|]. exists v. split; [exact Hv | exact Hres].
  - intros a Ha. left. left. rewrite GSP in Ha. unfold ESTACK in Ha. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HSM2 & HP2 & HFR2 & v & Hv & Hres).
exact (K regs2 mem2 md2 v HJ2 HARU2 HSM2 HP2 HFR2 Hv Hres).
Qed.

(* ---- the walk's boundary state at the return r of the bcmp thunk. The runtime call keeps every byte outside its
   own stack window [sp1 - 2 * ESTACK, sp1): the saved words at s0 and the s1 slots lie above sp1, the frame and the
   frame's shadow lie below alloc_ceiling, which is under the window (the journal's astk_ok), so crt_ss_ret is rebuilt
   at r over the memory after the call: the saved words through FSW_rres.fsw_resume_after_rtU_s0, the slots, the frame
   and its shadow as in crt_after_call (presence from the journal's stack window and from al_frames, chunk bytes
   carried by the call's frame clause). The call-site state ss is any state with crt_ss_ret's regions and with sp, gp,
   tp, s0, s1, s3 at their own atoms. ---- *)
Lemma crtD1_bcmp_resume : forall cx E (ss : sstate) k ly3 S3 U3 (W3 : world tfibsegs) regsT memT regs2 mem2 md2 csF r,
  crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
  ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
  crt_frame_ok cx S3 W3 (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))) ->
  ss_mem ss = ss_mem (crt_ss_ret 0 crt_cs1 csF) ->
  map (fun q => sr_get (ss_regs ss) q) [2; 3; 4; 8; 9; 19]%bv =
    [SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0; SOff 9 0; SOff 19 0] ->
  aregs_preserved regsT regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crt_atom_chunks csF ->
  crt_E cx (Ereg regs2 (crt_extra cx)) /\
  crt_frame_ok cx S3 W3 (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)) /\
  st_ok tfibsegs (Ereg regs2 (crt_extra cx)) (crt_ss_ret r crt_cs1 csF)
    (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros cx E ss k ly3 S3 U3 W3 regsT memT regs2 mem2 md2 csF r
  HE HJ HARU HFR HS Hmem Hrg HP Hfr HcsFin HcsFat.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx Hal16 H0) as (Hsp1b & Fm32 & _).
destruct HFR as (Hfrs & Hnotin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
(* the registers: at the call they are their own atoms; the callee keeps the callee-saved ones *)
cbn [map] in Hrg. injection Hrg as R2 R3 R4 R8 R9 R19.
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G : forall (q : Z) n, acallee_saved q -> sr_get (ss_regs ss) (Z_to_bv 5 q) = SOff n 0 ->
  YK11.getr regs2 (Z_to_bv 5 q) = ew E n).
{ intros q n Hq Hs. rewrite (HP q Hq). exact (Rd _ n Hs). }
assert (G2 : YK11.getr regs2 2%bv = ew E 2) by exact (G 2 2%nat ltac:(unfold acallee_saved; lia) R2).
assert (G3 : YK11.getr regs2 3%bv = ew E 3) by exact (G 3 3%nat ltac:(unfold acallee_saved; lia) R3).
assert (G4 : YK11.getr regs2 4%bv = ew E 4) by exact (G 4 4%nat ltac:(unfold acallee_saved; lia) R4).
assert (G8 : YK11.getr regs2 8%bv = ew E 8) by exact (G 8 8%nat ltac:(unfold acallee_saved; lia) R8).
assert (G9 : YK11.getr regs2 9%bv = ew E 9) by exact (G 9 9%nat ltac:(unfold acallee_saved; lia) R9).
assert (G19 : YK11.getr regs2 19%bv = ew E 19) by exact (G 19 19%nat ltac:(unfold acallee_saved; lia) R19).
assert (SPT : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv 2%nat R2); exact E2).
set (E' := Ereg regs2 (crt_extra cx)) in *.
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite G2. exact E2.
  - rewrite G3. exact E3.
  - rewrite G4. exact E4.
  - rewrite G8. exact E8.
  - rewrite G9. exact E9.
  - rewrite G19. exact E19. }
assert (Hag : forall n, (32 <= n < 50)%nat -> ew E' n = ew E n) by exact (crt_env_agree cx E E' HE HE').
(* the frame and its shadow, on the state after the call *)
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & HFapp).
rewrite EF in HF0, HFc, HFapp. rewrite crt_frame3 in HFc, HFapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (unpoison U3 mem2) md2 3 (c_pos cx) HAR Hin3) as (Hal32 & _ & Hfp & Hsp).
rewrite EF in Hal32, Hfp, Hsp. rewrite crt_frame3 in Hfp, Hsp. change (512 / 8) with 64 in Hsp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
assert (Hceil1 : alloc_ceiling + 2 * ESTACK <= crt_sp1 cx) by (unfold ESTACK; lia).
(* the resumed env's atom values *)
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & X & _); exact X).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & X & _); exact X).
assert (E19v : bv_unsigned (ew E' 19) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & X & _); exact X).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
(* a byte outside the call's window reads the same on both memories *)
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ (crt_sp1 cx - 2 * ESTACK <= a < crt_sp1 cx) ->
  mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a).
{ intros a Ha Hw. apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W3)). apply Hfr; [exact Ha|]. rewrite SPT. exact Hw. }
(* what the call-site state held: the saved words, the s1 slots and the frame chunks, on the memory before the call *)
assert (Hnth : forall i rg, nth_error (ss_mem (crt_ss_ret 0 crt_cs1 csF)) i = Some rg ->
  region_ok tfibsegs E (mrestrict (w_H W3) memT) rg).
{ intros i rg Hi. rewrite <- Hmem in Hi. exact (fsw_region_nth E ss _ i rg HS Hi). }
assert (HSV : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (spZ (c_regs cx))) crt_sv_chunks).
{ pose proof (Hnth 0%nat (fs_ret_s0_region (-104) 0 crt_sv_chunks) eq_refl) as (_ & _ & _ & X).
  unfold fs_ret_s0_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E8 in X. exact X. }
assert (HCS1 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1).
{ pose proof (Hnth 1%nat (crt_slot_region crt_cs1) eq_refl) as (_ & _ & _ & X).
  unfold crt_slot_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E9 in X. exact X. }
assert (HCSF : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) (crt_F cx)) csF).
{ pose proof (Hnth 2%nat (crt_frame_region csF) eq_refl) as (_ & _ & _ & X).
  unfold crt_frame_region in X. cbn [YP09.r_base YP09.r_chunks base_val] in X. rewrite E47 in X. exact X. }
(* the three extra regions of the boundary state, on the memory after the call *)
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) (crt_slot_region crt_cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly3 S3 U3 W3 mem2 md2 _ HARU); [unfold kHighMemBeg in *; lia|].
    apply Hpres. lia.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) memT) (crt_sp1 cx)) crt_cs1)
      by (eapply crt_chunks_env; [exact Hag | exact crt_cs1_atoms | exact HCS1]).
    pose proof crt_cs1_in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) memT)); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    apply Hk; [lia | unfold ESTACK; lia]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp o ltac:(lia)) as (Hp & Hno).
  apply (fsw_apresent_notowned B ly3 S3 U3 W3 mem2 md2 _ HARU); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W3) mem2) (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly3 S3 U3 W3 mem2 md2 _ HARU); [lia | exact Hno | exact Hp].
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) memT) (crt_F cx)) csF)
      by (eapply crt_chunks_env; [exact Hag | exact HcsFat | exact HCSF]).
    pose proof HcsFin as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) memT)); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). rewrite crt_frame3 in Ho3.
    apply Hk; lia. }
(* the frame's region is well formed: its chunks lie inside [0, 512) *)
assert (WFframe : YP09.region_wf (crt_frame_region csF) = true).
{ unfold YP09.region_wf, crt_frame_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite !andb_true_iff. split; [split|].
  - apply Z.leb_le. rewrite crt_frame3. lia.
  - apply orb_true_iff. right. rewrite !andb_true_iff. split; apply Z.leb_le; lia.
  - apply forallb_forall. intros c Hc. pose proof HcsFin as Hin1. rewrite Forall_forall in Hin1.
    destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). unfold YP09.chunk_inside.
    cbn [YP09.r_lo YP09.r_hi]. rewrite !andb_true_iff. split; [split|]; apply Z.leb_le; lia. }
(* the boundary state itself *)
assert (HS4 : st_ok tfibsegs E' (crt_ss_ret r crt_cs1 csF)
  (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs)))).
{ unfold crt_ss_ret.
  eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 mem2 md2 k regs2 memT
    (crt_extra cx) crt_sv_chunks (crt_ret_regions crt_cs1 csF) crt_ret_facts r (-104) 0 HJ HARU).
  - rewrite G8. rewrite <- E8. symmetry. apply Z_to_bv_bv_unsigned.
  - lia.
  - lia.
  - lia.
  - unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
    rewrite WFframe. cbn [andb].
    assert (X0 : YP09.region_wf (fs_ret_s0_region (-104) 0 crt_sv_chunks) = true) by (vm_compute; reflexivity).
    assert (X1 : YP09.region_wf (crt_slot_region crt_cs1) = true) by (vm_compute; reflexivity).
    assert (X3 : YP09.region_wf crt_shadow_region = true) by (vm_compute; reflexivity).
    rewrite X0, X1, X3. reflexivity.
  - exact crt_sv_in.
  - eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HSV].
  - intros a Ha. apply Hk; [lia | unfold ESTACK; lia].
  - unfold crt_ret_regions. constructor; [exact ROslot|]. constructor; [exact ROframe|].
    constructor; [exact ROshadow | apply Forall_nil].
  - apply pairwise_disjoint_of_extents.
    unfold fss_ret_s0_regs, crt_ret_regions, crt_slot_region, crt_frame_region, crt_shadow_region, fs_ret_s0_region.
    cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    fold E'. rewrite E8v, E9v, E47v, E19v. rewrite !crt_frame3. change (512 / 8) with 64.
    unfold ESTACK in Hceil1.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I;
      first [right; lia | left; lia | destruct Dfs as [Hd|Hd]; [left; lia | right; lia]].
  - unfold crt_ret_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E'.
    rewrite E9v, E47v. change (2 ^ 5) with 32.
    split; [split; [lia | split; [exact Fm32 | lia]]|].
    split; [|exact I]. split; [lia | split; [exact Hal32 | lia]]. }
split; [exact HE'|]. split; [|exact HS4].
(* the frame facts: the frames do not move, and the flag word is a frame byte, below the call's window *)
split; [exact Hfrs|]. split; [exact Hnotin|].
cbn [ms_mem mkst] in Hflag |- *. rewrite <- Hflag. apply rdword_ext. intros kk Hk8.
rewrite crt_frame3. apply Hfr; [lia|]. rewrite SPT. unfold ESTACK in Hceil1 |- *. lia.
Qed.

(* ---- the bcmp call as a CALLEE journal with an empty footprint (a Theorem Labs lane's statement): the thunk allocates nothing,
   frees nothing, changes no layout and no state, and writes only its own stack window, so every block byte and every
   frame byte is kept; with it the walk transports its boundary invariant across the call with FSW_rd's *_kept_call
   lemmas at FPc := []. YCbq.call_effect_journal at stk := ASTACK (16384, which holds the contract's 2 * ESTACK
   window), Eb := nothing, FP1 := [], nf := [], k1 := 0; astk_ok at the re-aligned sp comes from the walk's own astk_ok
   (STK_check_round_trip >= 17000 and sp1 >= sp0 - 208). The md relation is the contract's own same_but_materialized
   (crtD1_bcmp_call's K hands it over), made same_io by YCbq.same_io_materialized. call_effect_journal's errno /
   image facts are api_env, the same Section hypothesis FSH_crt_segD.v carries as HENV. ---- *)
Hypothesis HENV : api_env tfibsegs B.
Lemma crtD1_bcmp_journal : forall cx ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT mem2 md2 k,
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT -> ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
  same_but_materialized mdT md2 ->
  spZ regsT = crt_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
     aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) memT a) ->
  (forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) mem2 a) ->
  ajournal tfibsegs B ASTACK (spZ regsT) [] ly3 S3 W3 (unpoison U3 memT) mdT []
    ly3 S3 W3 (unpoison U3 mem2) md2 0.
Proof.
intros cx ly3 S3 U3 W3 regsT memT mdT mem2 md2 k HJ HARU HARU2 Hsm SPT Hfr Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx Hal16 H0) as (Hsp1b & _ & Hsp1_16).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the callee's stack window at the re-aligned sp *)
assert (HstkA : astk_ok ASTACK ly3 (spZ regsT)).
{ unfold astk_ok. unfold ly_bot in Hbot |- *. rewrite SPT, Etop, Eslo, Eshi. unfold ASTACK in Hbot |- *.
  split; [exact Hsp1_16|]. repeat split; lia. }
assert (HpresU : forall a, spZ regsT - ASTACK <= a < spZ regsT -> apresent (w_H W3) (unpoison U3 mem2) a).
{ intros a Ha. apply (fsw_apresent_poison B ly3 S3 U3 W3 mem2 md2 a HARU2); [|exact (Hpr a Ha)].
  rewrite SPT in Ha. unfold ASTACK in Ha. unfold kHighMemBeg in *. lia. }
eapply (call_effect_journal tfibsegs B LAWS fs_segs_low HENV ASTACK ly3 S3 W3 regsT (unpoison U3 memT) mdT ly3 S3 W3
  (unpoison U3 mem2) md2 (fun _ => False) [] [] 0);
  [exact (ARU_AR tfibsegs B ly3 S3 U3 W3 mem2 md2 HARU2) | apply layout_le_refl | apply wle_refl
  | apply same_io_materialized; exact Hsm | | exact HpresU | exact (ARU_AR tfibsegs B ly3 S3 U3 W3 memT mdT HARU)
  | exact HstkA | reflexivity | lia | lia | lia | intros a [] | | exact HQT ].
- (* the frame clause: outside the callee's 2 * ESTACK window, so outside its ascratch ASTACK window *)
  intros a Ha _ _ Hs _. apply (crt_unpoison_keep (w_H W3) U3 memT mem2 _ Hfr a Ha).
  intros Hw. cbv beta in Hw. apply Hs. left. unfold ASTACK. unfold ESTACK in Hw. lia.
- (* no block is freed: the state does not change *)
  intros p n i Hp Hnp. exfalso. exact (Hnp Hp).
Qed.

End d1b.
