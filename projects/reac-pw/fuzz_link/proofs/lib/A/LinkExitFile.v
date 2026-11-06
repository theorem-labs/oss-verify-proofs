(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths changed; 372 of its 416 lines of code are new or changed and 1631 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build fuzz_link.asan, pin 059dae63e07c): the open-file loop of __stdio_exit on
   link's one memory FILE.

   On link the target call leaves the fmemopen FILE open, so at exit the open-file list head (0x652308) holds that FILE
   f (AMemFileSink.v amf_gi [(f, AMF_BLOCK)]). __stdio_exit 0x96878 (420 bytes; listing
   (internal path) (internal record, sha256 12e8b61d11a3)) walks the list with
   close_file inlined:
     +0x10  ld s0,0(a0)           s0 = the list head (a0 = its address, from __ofl_lock)
     +0x14  bnez s0  (0x9688c)    taken: s0 = f
     +0x140 lw a0,0x8c(s0); bltz  the lock word is -1 (amemfile_static), so __lockfile is not called
     +0x150 ld wpos; +0x154 ld wbase; +0x158 beq
            wpos <> wbase: +0x15c ld a3,0x48(s0) (f->write = mwrite 0x96cc0, amemfile_static); a0 = f, a1 = a2 = 0;
            +0x16c jalr a3: LinkRwDefs.v amwrite_mf_flush_realizes (the Section hypothesis HMW), return to +0x170
     +0x170 ld rpos; +0x174 ld rend; +0x178 beq   taken: both are 0 (amemfile_window)
     +0x138 ld s0,0x70(s0)        f->next = 0 (amemfile_static); +0x13c beqz s0: taken, to +0x18 (0x96890)
   The loop body stores nothing, so the only bytes it changes are mwrite's. The two segments run the frame's symbolic
   engine (the method of lib/A/Rt/LinkRwRewind.v) over xf_tbl, the 105 instructions of __stdio_exit. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AFhf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs LinkRwRewind.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   1. Image facts: g_said and the three list heads are image bytes of the writable segment
   ========================================================================== *)

(* [0x62fec0, 0x652310) (g_sink 0x62fec0 .. the list head 0x652308 + 8) lies in the segment 0xa3000 .. 0x654000 *)
Lemma xf_heads_img : forall a, 0x62fec0 <= a < 0x652310 -> YG0d.in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x62fec0) &&
  (0x652310 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

Lemma xf_wz_said : wseg_ok tfibsegs (Z_to_bv 64 0x62fee0) (Z.to_nat 4096) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xf_said_owned_chk :
  forallb (fun r => (fst r + snd r <=? 0x62fee0) || (0x62fee0 + 4096 <=? fst r)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xf_said_writable : forall m a, 0x62fee0 <= a < 0x62fee0 + 4096 -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at.
apply (store_ok_all tfibsegs m (Z.to_nat 4096) (Z_to_bv 64 0x62fee0));
[rewrite unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia
| apply store_ok_wseg; exact xf_wz_said
| rewrite !unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a byte the reader shows the same in two memories is the same byte *)
Lemma xf_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ==========================================================================
   2. The code table, the symbolic runs and the registers they keep
   ========================================================================== *)

Definition A_SX_LOOP : Z := 0x9688c.   (* +0x14 bnez s0, after +0x10 ld s0,0(a0) read the list head *)
Definition A_SX_RET : Z := 0x969e8.    (* +0x170, the return of f->write *)
Definition A_SX_NEXT : Z := 0x96890.   (* +0x18, where the loop ends (+0x13c beqz s0) *)

(* __stdio_exit's size in link's .symtab over 4: 420 / 4 *)
Definition xf_ranges : list (Z * nat) := [(0x96878, 105%nat)].
Definition xf_tbl : ctable := Eval vm_compute in build_ranges xf_ranges TEmpty.
Lemma xf_tbl_eq : xf_tbl = build_ranges xf_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl xf_tbl). Qed.
Lemma xf_tbl_ok : table_ok tfibsegs xf_tbl.
Proof.
rewrite xf_tbl_eq. apply build_ranges_ok; [| apply table_ok_empty].
unfold xf_ranges. repeat constructor; cbn; discriminate.
Qed.

Lemma xf_run_to : forall (W : world tfibsegs) E stop ss ss' ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs xf_tbl FUEL stop ss = (ss', RS_running) ->
  SRr tfibsegs W (mkCfg ms md)
  (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
   st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E stop ss ss' ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs xf_tbl xf_tbl_ok AF0x.Hwx_tfa W FUEL stop E ss ss' RS_running ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.

Lemma xf_run : forall (W : world tfibsegs) E ss ss' why ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs xf_tbl FUEL ss = (ss', RS_stopped why) ->
  SRr tfibsegs W (mkCfg ms md)
  (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
   st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E ss ss' why ms md HS Hrun.
eapply (SRr_run_gen tfibsegs xf_tbl xf_tbl_ok AF0x.Hwx_tfa W FUEL E ss ss' (RS_stopped why) ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.

(* the FILE's words the head reads (base s0 = f): wpos (atom 32), wbase (atom 33), f->write, the lock word *)
Definition R_fA : YP09.region :=
  YP09.mkRegion (Some 8%nat) 40 144 40 40
    [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 33 0));
     YP09.mkChunk 72 (CVal 8 (SLit 0x96cc0)); YP09.mkChunk 140 (CVal 4 (SLit 0xffffffff))].
(* the FILE's words the tail reads: rpos, rend, next *)
Definition R_fC : YP09.region :=
  YP09.mkRegion (Some 8%nat) 8 120 8 8
    [YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0))].
Definition xf_facts : facts := mkFacts [(8%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition ssA : sstate := mkSS A_SX_LOOP sr_atoms [R_fA] None xf_facts.
Definition ssC : sstate := mkSS A_SX_RET sr_atoms [R_fC] None xf_facts.

Definition eA : sstate := Eval vm_compute in fst (sym_runN tfibsegs xf_tbl FUEL ssA).
Lemma r_A : sym_runN tfibsegs xf_tbl FUEL ssA = (eA, RS_stopped (SR_branch BC_EQ (SOff 32 0) (SOff 33 0))).
Proof. vm_compute. reflexivity. Qed.
Definition eAe : sstate := Eval vm_compute in
  fst (sym_run_toN tfibsegs xf_tbl FUEL A_SX_RET (YP06.add_cond eA (mkAC BC_EQ (SOff 32 0) (SOff 33 0)))).
Lemma r_Ae : sym_run_toN tfibsegs xf_tbl FUEL A_SX_RET (YP06.add_cond eA (mkAC BC_EQ (SOff 32 0) (SOff 33 0))) =
  (eAe, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition eAn : sstate := Eval vm_compute in
  fst (sym_run_toN tfibsegs xf_tbl FUEL LA_MWRITE (YP06.add_cond eA (mkAC (neg_bc BC_EQ) (SOff 32 0) (SOff 33 0)))).
Lemma r_An : sym_run_toN tfibsegs xf_tbl FUEL LA_MWRITE
  (YP06.add_cond eA (mkAC (neg_bc BC_EQ) (SOff 32 0) (SOff 33 0))) = (eAn, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition eC : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs xf_tbl FUEL A_SX_NEXT ssC).
Lemma r_C : sym_run_toN tfibsegs xf_tbl FUEL A_SX_NEXT ssC = (eC, RS_running).
Proof. vm_compute. reflexivity. Qed.

(* the callee-saved registers other than s0 *)
Definition L_CS : list Z := [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_kept (s : sstate) (L : list Z) : bool :=
  forallb (fun r => sv_eqb (sr_get (ss_regs s) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) L.
Lemma kept_eAe : regs_kept eAe (8 :: L_CS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma kept_eAn : regs_kept eAn (8 :: L_CS) = true. Proof. vm_compute. reflexivity. Qed.
Lemma kept_eC : regs_kept eC L_CS = true. Proof. vm_compute. reflexivity. Qed.

Lemma regs_kept_get : forall H E ss ms regs0 extra L,
  st_ok tfibsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> regs_kept ss L = true ->
  forall r, In r L -> 0 <= r < 32 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros H E ss ms regs0 extra L HS HE Hk r Hr Hr32. unfold regs_kept in Hk. rewrite forallb_forall in Hk.
specialize (Hk r Hr). apply sv_eqb_eq in Hk.
rewrite (st_ok_reg_denot H E ss ms _ HS), Hk. subst E. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply ew_Ereg_nat. rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma acs_L_CS : forall r, acallee_saved r -> r <> 8 -> In r L_CS /\ 0 <= r < 32.
Proof. intros r Hr H8. unfold acallee_saved in Hr. split; [cbv [L_CS In]; lia | lia]. Qed.

Lemma acs_L8 : forall r, acallee_saved r -> In r (8 :: L_CS) /\ 0 <= r < 32.
Proof. intros r Hr. unfold acallee_saved in Hr. split; [cbv [L_CS In]; lia | lia]. Qed.

(* ==========================================================================
   3. The head: from +0x14 (s0 = f) to the call of f->write, or to +0x170 when the window holds nothing
   ========================================================================== *)

Lemma xf_head : forall (W : world tfibsegs) regs mem md f wpos wbase,
  getr regs 8 = w64 f -> 4096 <= f -> f + AMF_BLOCK <= 2 ^ 47 -> f mod 16 = 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 40) 8 wpos ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 56) 8 wbase ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 72) 8 LA_MWRITE ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 140) 4 AU32M1 ->
  0 <= wpos < 2 ^ 64 -> 0 <= wbase < 2 ^ 64 ->
  SRr tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs mem md)
   (fun W' c' => W' = W /\ exists regs' md', same_but_materialized md md' /\ aregs_preserved regs regs' /\
     ((wpos = wbase /\ c' = cfg_at tfibsegs A_SX_RET regs' mem md') \/
      (wpos <> wbase /\ c' = cfg_at tfibsegs LA_MWRITE regs' mem md' /\ getr regs' 1 = w64 A_SX_RET /\
       getr regs' 10 = w64 f /\ getr regs' 11 = w64 0 /\ getr regs' 12 = w64 0))).
Proof.
intros W regs mem md f wpos wbase G8 Hf4 Hfh Hf16 V40 V56 V72 V140 Rp Rb.
unfold AMF_BLOCK in Hfh.
unfold cfg_at. change (w64 A_SX_LOOP) with (Z_to_bv 64 A_SX_LOOP).
set (E := Ereg regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase]).
assert (EREG : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
  by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
assert (U8 : bv_unsigned (ew E 8) = f)
  by (rewrite (EREG 8%nat 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 wpos)
  by (pose proof (ew_Ereg_extra regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase] 0) as X; cbn [nth Nat.add] in X; exact X).
assert (E33 : ew E 33 = Z_to_bv 64 wbase)
  by (pose proof (ew_Ereg_extra regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase] 1) as X; cbn [nth Nat.add] in X; exact X).
assert (HS0 : st_ok tfibsegs E ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SX_LOOP) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
  apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 wpos; Z_to_bv 64 wbase]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, R_fA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + eapply (chunk_ok_val tfibsegs E _ f 40 8 (SOff 32 0) wpos);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V40].
    + eapply (chunk_ok_val tfibsegs E _ f 56 8 (SOff 33 0) wbase);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V56].
    + eapply (chunk_ok_val tfibsegs E _ f 72 8 (SLit 0x96cc0) 0x96cc0); [reflexivity | zside | zside | exact V72].
    + eapply (chunk_ok_val tfibsegs E _ f 140 4 (SLit 0xffffffff) 0xffffffff);
      [reflexivity | zside | zside | exact V140].
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; exact I]. cbn [xf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8. change (2 ^ 4) with 16. repeat split; first [exact Hf16 | lia]. }
(* +0x14 .. +0x158: the run stops at beq wpos, wbase *)
eapply SRr_bind; [exact (xf_run W E ssA eA _ _ md HS0 r_A)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
apply frame_of_read_only in HF1; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF1.
destruct (Z.eq_dec wpos wbase) as [Heq | Hne].
- (* the window holds nothing: on to +0x170 *)
  assert (Hbr : branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SOff 33 0)) = true)
    by (rewrite branch_eq_U, (U_atom E 32 wpos E32 Rp), (U_atom E 33 wbase E33 Rb); apply Z.eqb_eq; exact Heq).
  pose proof (st_ok_add_cond tfibsegs E eA _ BC_EQ (SOff 32 0) (SOff 33 0) HS1 Hbr) as HS1c.
  eapply SRr_bind; [exact (xf_run_to W E A_SX_RET _ eAe ms1 _ HS1c r_Ae)|].
  cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
  apply frame_of_read_only in HF2; [|vm_compute; reflexivity].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS2 eq_refl) as Hsh2.
  apply SRr_ret. cbv beta. rewrite ?m_vm_lazy_wvb, ?wvb_wvb.
  split; [reflexivity|]. exists (ms_regs ms2), (with_vm_backing (m_vm_lazy md) mat2 md).
  split; [apply with_vm_backing_same|]. split.
  + intros r Hr. destruct (acs_L8 r Hr) as [Hin Hr32].
    exact (regs_kept_get (w_H W) E eAe ms2 regs _ (8 :: L_CS) HS2 eq_refl kept_eAe r Hin Hr32).
  + left. split; [exact Heq|]. unfold cfg_at. rewrite Hsh2 at 1. rewrite HF2, HF1. reflexivity.
- (* pending bytes: on to the call of f->write *)
  assert (Hbr : branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SOff 33 0)) = false)
    by (rewrite branch_eq_U, (U_atom E 32 wpos E32 Rp), (U_atom E 33 wbase E33 Rb); apply Z.eqb_neq; exact Hne).
  pose proof (st_ok_add_cond_neg tfibsegs E eA _ BC_EQ (SOff 32 0) (SOff 33 0) HS1 Hbr) as HS1c.
  eapply SRr_bind; [exact (xf_run_to W E LA_MWRITE _ eAn ms1 _ HS1c r_An)|].
  cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
  apply frame_of_read_only in HF2; [|vm_compute; reflexivity].
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS2 eq_refl) as Hsh2.
  rreg HS2 (1%bv : bv 5) R1. rreg HS2 (10%bv : bv 5) R10. rreg HS2 (11%bv : bv 5) R11. rreg HS2 (12%bv : bv 5) R12.
  apply SRr_ret. cbv beta. rewrite ?m_vm_lazy_wvb, ?wvb_wvb.
  split; [reflexivity|]. exists (ms_regs ms2), (with_vm_backing (m_vm_lazy md) mat2 md).
  split; [apply with_vm_backing_same|]. split.
  + intros r Hr. destruct (acs_L8 r Hr) as [Hin Hr32].
    exact (regs_kept_get (w_H W) E eAn ms2 regs _ (8 :: L_CS) HS2 eq_refl kept_eAn r Hin Hr32).
  + right. split; [exact Hne|]. split; [unfold cfg_at; rewrite Hsh2 at 1; rewrite HF2, HF1; reflexivity|].
    split; [rewrite R1; reflexivity|].
    split; [rewrite R10, (EREG 8%nat 8%bv eq_refl); exact G8|].
    split; [rewrite R11; reflexivity | rewrite R12; reflexivity].
Qed.

(* ==========================================================================
   4. The tail: from +0x170 (rpos = rend, next = 0) to +0x18 with s0 = 0
   ========================================================================== *)

Lemma xf_tail : forall (W : world tfibsegs) regs mem md f,
  getr regs 8 = w64 f -> 4096 <= f -> f + AMF_BLOCK <= 2 ^ 47 -> f mod 16 = 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 8) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 16) 8 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 112) 8 0 ->
  SRr tfibsegs W (cfg_at tfibsegs A_SX_RET regs mem md)
   (fun W' c' => W' = W /\ exists regs' md', c' = cfg_at tfibsegs A_SX_NEXT regs' mem md' /\
     same_but_materialized md md' /\ getr regs' 8 = w64 0 /\
     (forall r, acallee_saved r -> r <> 8 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))).
Proof.
intros W regs mem md f G8 Hf4 Hfh Hf16 V8 V16 V112.
unfold AMF_BLOCK in Hfh.
unfold cfg_at. change (w64 A_SX_RET) with (Z_to_bv 64 A_SX_RET).
set (E := Ereg regs []).
assert (U8 : bv_unsigned (ew E 8) = f)
  by (unfold E; rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs E ssC (restrict (w_H W) (mkst regs (Z_to_bv 64 A_SX_RET) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC.
  apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, R_fC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + eapply (chunk_ok_val tfibsegs E _ f 8 8 (SLit 0) 0); [reflexivity | zside | zside | exact V8].
    + eapply (chunk_ok_val tfibsegs E _ f 16 8 (SLit 0) 0); [reflexivity | zside | zside | exact V16].
    + eapply (chunk_ok_val tfibsegs E _ f 112 8 (SLit 0) 0); [reflexivity | zside | zside | exact V112].
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; exact I]. cbn [xf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U8. change (2 ^ 4) with 16. repeat split; first [exact Hf16 | lia]. }
eapply SRr_bind; [exact (xf_run_to W E A_SX_NEXT ssC eC _ md HS0 r_C)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
apply frame_of_read_only in HF1; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF1.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS1 eq_refl) as Hsh1.
rreg HS1 (8%bv : bv 5) R8.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms1), (with_vm_backing (m_vm_lazy md) mat1 md).
split; [unfold cfg_at; rewrite Hsh1 at 1; rewrite HF1; reflexivity|].
split; [apply with_vm_backing_same|]. split; [rewrite R8; reflexivity|].
intros r Hr H8. destruct (acs_L_CS r Hr H8) as [Hin Hr32].
exact (regs_kept_get (w_H W) E eC ms1 regs _ L_CS HS1 eq_refl kept_eC r Hin Hr32).
Qed.

(* ==========================================================================
   5. The loop on link's FILE: from +0x14 with s0 = f to +0x18 with s0 = 0
   ========================================================================== *)

Section t.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
(* mwrite's flush contract (lib/A/Rt/LinkRwDefs.v) *)
Hypothesis HMW : amwrite_mf_flush_realizes tfibsegs B link_amf LA_MWRITE.

Theorem link_exit_file_loop : forall ly S (W : world tfibsegs) regs mem md f,
  AR tfibsegs B ly S W mem md -> spZ regs mod 16 = 0 -> ly_stk_lo ly + AMW_STK <= spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = w64 f ->
  In (f, AMF_BLOCK) (ablocks B ly S) -> amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x62fee0 4096 ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) 0x62fee0 4096 ->
  SRr tfibsegs W (cfg_at tfibsegs A_SX_LOOP regs mem md)
   (fun W' c' => W' = W /\ exists regs' mem' md', c' = cfg_at tfibsegs A_SX_NEXT regs' mem' md' /\
     AR tfibsegs B ly S W mem' md' /\ same_but_materialized md md' /\ getr regs' 8 = w64 0 /\
     (forall r, acallee_saved r -> r <> 8 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
     amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (mrestrict (w_H W) mem') /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AMW_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
        ~ (0x62fee0 <= a < 0x62fee0 + 4096) -> ~ (as_errno B <= a < as_errno B + 4) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
     (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md f HAR Hal16 [Hslo Hshi] Hpres Hgp Htp G8 Hblk Hgi Hra Hhull.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (F16 & F4k & Fceil & Fapp & Fby & _ & _).
pose proof alloc_ceiling_lt as Hcl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hf47 : f + AMF_BLOCK <= 2 ^ 47) by lia.
assert (KS : AMW_STK = 4192 /\ ESTACK = 4096 /\ AMF_BLOCK = 1304 /\ AMF_ZEROED = 272 /\ AMF_BUF = 280 /\
  AMF_BUFSIZ = 1024 /\ as_errno B = 0x631b6c) by (rewrite (ts_errno B TB); repeat split; reflexivity).
destruct KS as (KA & KE & KB & KZ & KBF & KBS & KERR).
(* the FILE at f, from the GI conjunct *)
destruct Hgi as [(_ & Hnil) | (f' & Hheads & Hl & Hat)]; [discriminate Hnil|].
injection Hl as Hff. subst f'.
pose proof Hat as (_ & _ & _ & _ & Hfl & Hom & Hwin & Hck).
pose proof (amemfile_close_reads tfibsegs link_amf _ f Hat) as (V140 & V72 & V8 & V16 & V112).
destruct Hwin as (_ & _ & Hw).
assert (WIN : exists k wend wpos wbase, amf_win tfibsegs (mrestrict (w_H W) mem) f k /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 32) 8 wend /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 40) 8 wpos /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (f + 56) 8 wbase /\
  0 <= wend < 2 ^ 64 /\ 0 <= wpos < 2 ^ 64 /\ 0 <= wbase < 2 ^ 64 /\ 0 <= k <= AMF_BUFSIZ).
{ destruct Hw as [(W32 & W40 & W56) | (kk & Hkk & W32 & W40 & W56)].
  - exists 0, 0, 0, 0. split; [left; split; [reflexivity|]; split; [exact W32|]; split; [exact W40 | exact W56]|].
    split; [exact W32|]. split; [exact W40|]. split; [exact W56|]. rewrite KBS. lia.
  - exists kk, (f + AMF_BUF + AMF_BUFSIZ), (f + AMF_BUF + kk), (f + AMF_BUF).
    split; [right; split; [exact Hkk|]; split; [exact W32|]; split; [exact W40 | exact W56]|].
    split; [exact W32|]. split; [exact W40|]. split; [exact W56|].
    unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *. lia. }
destruct WIN as (k & wend & wpos & wbase & Hwk & W32 & W40 & W56 & Rw & Rp & Rb & Rk).
assert (FL : exists fl, 0 <= fl < 2 ^ 32 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (f + 0) 4 fl).
{ destruct Hfl as [Hx|Hx]; eexists; (split; [|exact Hx]); unfold AF_NORD, AF_ERR; lia. }
assert (OM : exists om, 0 <= om < 2 ^ 32 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (f + 136) 4 om).
{ destruct Hom as [Hx|Hx]; eexists; (split; [|exact Hx]); unfold AU32M1; lia. }
destruct FL as (fl & Rfl & Vfl). destruct OM as (om & Rom & Vom).
destruct Hck as (pos & len & Hpl & Hlen & Vpos & Vlen).
(* the head *)
eapply SRr_bind; [exact (xf_head W regs mem md f wpos wbase G8 F4k Hf47 F16 W40 W56 V72 V140 Rp Rb)|].
cbv beta. intros W1 c1 _ (-> & regs1 & md1 & Hsb1 & HP1 & [(Heq & ->) | (Hne & -> & R1 & R10 & R11 & R12)]).
- (* nothing pending: no call; the tail on the same memory *)
  assert (G8_1 : getr regs1 8 = w64 f)
    by (rewrite (ap_lit regs regs1 8%bv 8 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact G8).
  eapply SRr_bind; [exact (xf_tail W regs1 mem md1 f G8_1 F4k Hf47 F16 V8 V16 V112)|].
  cbv beta. intros W2 c2 _ (-> & regs2 & md2 & -> & Hsb2 & R8 & HP2).
  apply SRr_ret. split; [reflexivity|]. exists regs2, mem, md2.
  split; [reflexivity|].
  split; [rewrite (same_but_materialized_wvb _ _ (same_but_materialized_trans _ _ _ Hsb1 Hsb2));
    apply AFhf.AR_wvb; exact HAR|].
  split; [exact (same_but_materialized_trans _ _ _ Hsb1 Hsb2)|].
  split; [exact R8|].
  split; [intros r Hr H8; rewrite (HP2 r Hr H8); exact (HP1 r Hr)|].
  split; [right; exists f; split; [exact Hheads|]; split; [reflexivity | exact Hat]|].
  split; [intros; reflexivity|]. split; [intros a Ha; exact Ha | exact Hpres].
- (* bytes pending: f->write(f, 0, 0) is mwrite's flush *)
  assert (SP1 : spZ regs1 = spZ regs)
    by (unfold spZ; rewrite (ap_lit regs regs1 2%bv 2 HP1 ltac:(unfold acallee_saved; lia) eq_refl); reflexivity).
  assert (HAR1 : AR tfibsegs B ly S W mem md1)
    by (rewrite (same_but_materialized_wvb _ _ Hsb1); apply AFhf.AR_wvb; exact HAR).
  assert (P1 : ecall_pre tfibsegs B ly S W regs1 mem md1).
  { split; [exact HAR1|]. split; [rewrite R1; unfold w64; apply ret_ok_lit; [unfold A_SX_RET; lia | reflexivity]|].
    rewrite SP1. split; [exact Hal16|]. split; [lia|]. split; [lia|].
    split; [intros a Ha; apply Hpres; lia|].
    split; [rewrite (ap_lit regs regs1 3%bv 3 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact Hgp|].
    rewrite (ap_lit regs regs1 4%bv 4 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact Htp. }
  assert (P2 : ly_stk_lo ly + AMW_STK <= spZ regs1) by (rewrite SP1; lia).
  assert (P3 : forall a, spZ regs1 - AMW_STK <= a < spZ regs1 -> apresent (w_H W) mem a)
    by (rewrite SP1; exact Hpres).
  assert (Hk : amf_k tfibsegs link_amf (mrestrict (w_H W) mem) f k) by (split; [exact Hat | exact Hwk]).
  assert (Hdyn : amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem) f fl om wend wpos wbase pos len).
  { unfold amf_dyn. split; [exact Rfl|]. split; [exact Rom|]. split; [exact Rw|]. split; [exact Rp|].
    split; [exact Rb|]. split; [exact Hpl|]. split; [exact Hlen|].
    split; [exact Vfl|]. split; [exact Vom|]. split; [exact W32|]. split; [exact W40|]. split; [exact W56|].
    split; [exact Vpos | exact Vlen]. }
  set (pbf := fun i : nat => match aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i) with
                             | Some v => v | None => 0 end).
  set (pb := map pbf (seq 0 (Z.to_nat k))).
  assert (Hlenpb : Z.of_nat (length pb) = k) by (unfold pb; rewrite length_map, length_seq; lia).
  assert (Hpend : amf_pend tfibsegs (mrestrict (w_H W) mem) f pb).
  { unfold amf_pend, azbytes. intros i Hi.
    assert (Hik : (i < Z.to_nat k)%nat) by (unfold pb in Hi; rewrite length_map, length_seq in Hi; exact Hi).
    change (amf_rd tfibsegs (mrestrict (w_H W) mem) (f + AMF_BUF + Z.of_nat i))
      with (aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i)).
    unfold pb. erewrite nth_indep with (d' := pbf 0%nat) by (rewrite length_map, length_seq; exact Hik).
    rewrite map_nth, seq_nth by exact Hik. unfold pbf. cbn [Nat.add].
    assert (Hp : apresent (w_H W) mem (f + AMF_BUF + Z.of_nat i))
      by (apply (proj1 (Fby (f + AMF_BUF + Z.of_nat i) ltac:(rewrite KBF, KB; rewrite KBS in Rk; lia)))).
    pose proof (aview_some_of_apresent (w_H W) mem _ Hp) as Hs.
    destruct (aview tfibsegs (w_H W) mem (f + AMF_BUF + Z.of_nat i)) as [v|]; [reflexivity | exfalso; exact (Hs eq_refl)]. }
  assert (Hbuf : amf_buf_ok tfibsegs B link_amf AMW_STK ly S W regs1 mem).
  { unfold amf_buf_ok. cbn [amf_buf amf_size link_amf]. rewrite SP1.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros a Ha. split; [exact (xf_said_writable _ a Ha)|]. split.
      + intros O. apply (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR (said_img a Ha))) in O.
        rewrite (ts_owned B TB) in O. apply Exists_exists in O as (r & Hr & Hz).
        pose proof (proj1 (forallb_forall _ _) xf_said_owned_chk r Hr) as Hc. cbv beta in Hc.
        unfold in_zr in Hz. apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
      + lia.
    - split; [unfold amem_range, kLowMemEnd; lia|]. split; [exact Hra | exact Hhull]. }
  eapply SRr_bind; [exact (HMW ly S W regs1 mem md1 f k fl om wend wpos wbase pos len pb
    P1 P2 P3 R10 R11 R12 Hblk Hk Hdyn Hpend Hlenpb Hbuf)|].
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hpost). cbv zeta in Hpost.
  destruct Hpost as (-> & HAR2 & HP2 & Hsb2 & _ & Hk2 & _ & _ & _ & _ & Hkept2 & Hpm2 & Hpw2).
  rewrite SP1 in Hkept2, Hpw2.
  assert (RA1 : raZ regs1 = A_SX_RET)
    by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; unfold A_SX_RET; lia).
  rewrite RA1.
  assert (G8_2 : getr regs2 8 = w64 f)
    by (rewrite (ap_lit regs1 regs2 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) eq_refl),
          (ap_lit regs regs1 8%bv 8 HP1 ltac:(unfold acallee_saved; lia) eq_refl); exact G8).
  pose proof (amemfile_close_reads tfibsegs link_amf _ f (proj1 Hk2)) as (_ & _ & V8' & V16' & V112').
  eapply SRr_bind; [exact (xf_tail W regs2 mem2 md2 f G8_2 F4k Hf47 F16 V8' V16' V112')|].
  cbv beta. intros W3 c3 _ (-> & regs3 & md3 & -> & Hsb3 & R8 & HP3).
  assert (SB : same_but_materialized md md3)
    by exact (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ Hsb1 Hsb2) Hsb3).
  apply SRr_ret. split; [reflexivity|]. exists regs3, mem2, md3.
  split; [reflexivity|].
  split; [rewrite (same_but_materialized_wvb _ _ Hsb3); apply AFhf.AR_wvb; exact HAR2|].
  split; [exact SB|]. split; [exact R8|].
  split; [intros r Hr H8; rewrite (HP3 r Hr H8), (HP2 r Hr); exact (HP1 r Hr)|].
  split.
  { right. exists f. split; [|split; [reflexivity | exact (proj1 Hk2)]].
    apply (amf_heads_frame tfibsegs link_amf (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2) f); [|exact Hheads].
    intros a Ha. apply xf_mbyte_of_aview.
    assert (Hai : 0x62fec0 <= a < 0x652310)
      by (cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha; lia).
    apply Hkept2; [lia | lia | | cbn [amf_buf amf_size link_amf];
      cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha; lia
      | rewrite KERR; cbv [amf_head_addr amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha; lia].
    intros Hfa. apply (proj2 (proj2 (Fby a ltac:(rewrite KZ in Hfa; rewrite KB; lia)))). exact (xf_heads_img a Hai). }
  split; [intros a Ha H1 H2 H3 H4; exact (Hkept2 a Ha H1 H2 H3 H4)|].
  split; [exact Hpm2 | exact Hpw2].
Qed.

End t.
End d.
