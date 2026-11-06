(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_rp: the re-poison stretch of image B's LLVMFuzzerTestOneInput after the two frees,
   from +0xac8 (segX_exit_defs.v ex_fr) to the join +0xae0 (llvm_b_st_ae0 of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v):
     +0xac8 li a0,-8; +0xacc ld t0, 8(s1); +0xad0 sb a0, 4(t0); +0xad4 sb a0, 5(t0); +0xad8 ld a6, 16(s1);
     +0xadc ld a7, 0(s1)
   One Pa run (lib/B/Prog/DecodeBPaLib.v paj_run_to_tok, stopped at +0xae0) over two regions: the three spill slots at
   s1 (read: the frame, the shadow address, the frame), and the frame's shadow bytes 4 / 5 (written, through the
   shadow address the run loads, the extra atom 32; the frame is the extra atom 33). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa
  DecodeBPaLib DecodeBImg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_exit_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the
   plain ones (YM03.v:179-180 lf_lia_orig / lf_nia_orig). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Open Scope Z_scope.

Definition rp_extra (cx : dctx) : list word := [w64 (d_SH cx); w64 (d_F cx)].
Definition rp_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition rp_sh : YP09.region := YP09.mkRegion (Some 32%nat) 4 6 4 6 [].
(* The stretch's absolute pcs (DEC_A_LLVMF + 0xac8, + 0xae0). The run is the absolute engine's (YCbq.v aj_run_to,
   as segX_exit_td.v's), not the Pa engine's: it writes the shadow band, which the Pa engine's token check
   (YCbn.v cells_safe_b) refuses outside a tracked shadow entry. *)
Definition RP_PC : Z := 527224.
Definition RP_END : Z := 527248.
Lemma rp_pc_eq : DEC_A_LLVMF + 0xac8 = RP_PC.
Proof. vm_compute. reflexivity. Qed.
Definition ss_rp : sstate := mkSS RP_PC sr_atoms [rp_slots; rp_sh] None (mkFacts [] [] []).

Section rp. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := decodesegsB0.

Ltac rp_base_val Ex n v Hn :=
  replace (base_val Ex (Some n)) with v by (cbn [base_val]; rewrite Hn; symmetry; apply unsigned_lit_small; lia).

Ltac rp_rg HS r :=
  lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?H ?msx) =>
    rewrite (st_ok_restrict_reg sg H Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end.

Lemma rp_ae0 : AR_laws segs B -> ameter_laws MT ->
  forall (cx : dctx) (W : world segs) (c : config) k spent rest (R : bvmap 5 word -> Prop),
  d_n cx = Z.of_nat (length (d_pl cx)) ->
  ex_fr B MT 0xac8 k [] spent rest R cx W c ->
  k <= dec_ev_ae0 -> spent <= dec_spent_ae0 MT (d_n cx) ->
  SRr segs W c (llvm_b_st_ae0 B MT cx).
Proof.
intros LAWS MTL cx W c k spent rest R Hnlen
  (fx' & ly & S & regs & mem & md & -> & Hfz & Hcore & Hperm & Hmle & _ & Hfrs & Hfsh & _) Hk Hsp.
pose proof decodeb_segs_low as Hsegs. pose proof decodeb_wx as Hwx.
pose proof Hcore as (HJ & Hfrm & Hs0 & Hs1 & Hsp1 & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof ASAN_CEIL_range as (HAC & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrm; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
destruct (frames_bounds segs B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (HF1 & HF2 & HF3).
rewrite EFA in HF1, HF2, HF3. change (fs_frame_bytes DEC_FCLASS) with 64 in HF2, HF3.
assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity.
assert (HSHr : kLowShadowBeg <= d_SH cx /\ d_SH cx + 8 <= kHighMemBeg).
{ rewrite ESH. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
  assert (d_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). cbn in *. lia. }
assert (HAC' : 0x7fff7f800000 <= alloc_ceiling) by (unfold ASAN_CEIL in HAC; lia).
unfold kLowShadowBeg, kHighMemBeg in HSHr.
destruct Hfrs as (Q0 & Q8 & Q16). unfold dec_b_slot in Q0, Q8, Q16.
set (E := Ereg regs (rp_extra cx)).
assert (E9 : ew E 9 = w64 (d_sp1 cx)) by (exact (eq_trans (ew_Ereg_nat regs _ 9 9%bv eq_refl) Hs1)).
assert (E32 : ew E 32 = w64 (d_SH cx)) by (exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (d_F cx)) by (exact (ew_Ereg_extra regs _ 1)).
assert (Hsp1lo : alloc_ceiling + 32000 <= d_sp1 cx < 2 ^ 47) by lia.
assert (HS : st_ok segs E ss_rp (restrict (w_H W) (mkst regs (Z_to_bv 64 RP_PC) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_rp. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ss_rp. cbn [ss_mem]. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, rp_slots, rp_sh;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; fold E.
    + rp_base_val E 9%nat (d_sp1 cx) E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ (d_sp1 cx) 0 8 (SOff 33 0) (d_F cx));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ Q0).
      * apply (chunk_ok_val segs E _ (d_sp1 cx) 8 8 (SOff 32 0) (d_SH cx));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ Q8).
      * apply (chunk_ok_val segs E _ (d_sp1 cx) 16 8 (SOff 33 0) (d_F cx));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ Q16).
    + rp_base_val E 32%nat (d_SH cx) E32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs).
      exact (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
        (ex_awr_frame B cx ly S W regs mem md k (d_SH cx + o) Hcore ltac:(lia)))).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
    rp_base_val E 9%nat (d_sp1 cx) E9. rp_base_val E 32%nat (d_SH cx) E32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold rp_slots, rp_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rp_base_val E 9%nat (d_sp1 cx) E9. rp_base_val E 32%nat (d_SH cx) E32.
    repeat split; lia.
  - split; [exact I | split; exact I]. }
change (w64 (DEC_A_LLVMF + 0xac8)) with (Z_to_bv 64 (DEC_A_LLVMF + 0xac8)). rewrite rp_pc_eq.
aj_run_to decodebtbl_ok HS HJ RP_END.
- unfold ss_rp. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil].
  + rewrite E32. apply unsigned_lit_small. lia.
  + intros a Ha. unfold rp_sh in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    exact (ex_awr_frame B cx ly S W regs mem md k a Hcore ltac:(lia)).
- (* the bytes outside the two written shadow bytes are the ones before the run *)
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_SH cx + 4 <= a < d_SH cx + 6) ->
            aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Hn. unfold aview. cbv beta. f_equal. unfold mbyte.
    rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hin & Hr).
    rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    rewrite Z.mod_small in Hr by lia.
    unfold ss_rp in Hin. cbn [ss_mem In] in Hin.
    assert (B32 : base_val E (Some 32%nat) = d_SH cx)
      by (cbn [base_val]; rewrite E32; apply unsigned_lit_small; lia).
    destruct Hin as [<- | [<- | []]]; unfold rp_slots, rp_sh in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
      fold E in Hr; [lia | rewrite B32 in Hr; lia]. }
  assert (HP : aregs_preserved regs (ms_regs ms)).
  { apply (aregs_preserved_of_st_ok segs (w_H W) E _ ms regs (rp_extra cx) HS);
      [apply env_agree_refl | vm_compute; reflexivity]. }
  assert (P2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
  assert (P3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
  assert (P4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
  assert (P8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
  assert (P9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
  unfold in_app, kLowShadowBeg, kHighMemBeg in HF3.
  pmkst HS. apply SRr_ret. unfold llvm_b_st_ae0. cbv beta.
  exists fx', ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md), k.
  split.
  { assert (RE : Z_to_bv 64 527248 = w64 (DEC_A_LLVMF + 0xae0)) by (unfold w64; f_equal; vm_compute; reflexivity).
    rewrite RE. reflexivity. }
  split; [exact Hfz|].
  split.
  { apply (ex_core_kept B cx ly S W regs mem md k ly S W (ms_regs ms) (ms_mem ms) _ k Hcore HJ Hfrm P8 P9).
    - unfold spZ. rewrite P2. reflexivity.
    - exact P3.
    - exact P4.
    - intros a Ha. apply KV; lia.
    - intros a Ha. apply KV; lia.
    - intros a Ha. destruct (HFpres a Ha) as [Hh [b Hb]]. split; [exact Hh|].
      pose proof (HG (Z_to_bv 64 a)) as G. unfold mrestrict in G. rewrite Hh in G.
      destruct (ms_mem ms (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
      exfalso. apply G; [rewrite Hb; discriminate | reflexivity].
    - exact Hpay.
    - intros i Hi. rewrite <- Hnlen in Hi.
      pose proof (Hpay ltac:(lia)) as Hp.
      destruct (al_blocks _ _ LAWS ly S W mem md (d_p cx) (d_n cx) HAR Hp) as (_ & Hb4096 & Hbc & Happ & _).
      pose proof (req_size_pos (d_n cx) ltac:(lia)) as [Hq1 Hq2].
      unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
      apply KV; lia. }
  split; [exact Hk|].
  split; [rewrite app_nil_r in Hperm; exact Hperm|].
  split; [exact (mo_le_mono MT MTL _ _ _ _ Hmle Hsp)|].
  split.
  { unfold dec_b_fr. split; [|split].
    - rp_rg HS (5%bv : bv 5). cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - rp_rg HS (16%bv : bv 5). cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - rp_rg HS (17%bv : bv 5). cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  unfold dec_b_fsh in Hfsh |- *. destruct Hfsh as (L0 & L4 & L5 & L6).
  lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
    let rr := eval vm_compute in (nth_error (ss_mem ssx) 1) in
    lazymatch rr with Some ?r =>
      pose proof (st_ok_region_nth (segs := segs) Ex ssx _ 1 r HS ltac:(vm_compute; reflexivity)) as HR
    end end.
  pose proof (field_of_region_any E _ 32 (d_SH cx) _ _ _ _ _ 4 1%N (SLit 18446744073709551608) HR
    ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(right; left; reflexivity) ltac:(cbn; lia)) as V4.
  pose proof (field_of_region_any E _ 32 (d_SH cx) _ _ _ _ _ 5 1%N (SLit 18446744073709551608) HR
    ltac:(rewrite E32; apply unsigned_lit_small; lia) ltac:(left; reflexivity) ltac:(cbn; lia)) as V5.
  replace (bv_unsigned (sv_denot E (SLit 18446744073709551608)) mod 2 ^ (8 * Z.of_N 1)) with 248 in V4, V5
    by (vm_compute; reflexivity).
  change (N.to_nat 1) with 1%nat in V4, V5.
  split; [intros i Hi; rewrite KV by lia; exact (L0 i Hi)|].
  split; [exact (ex_aview_of_val1 (w_H W) (ms_mem ms) _ 248 V4 ltac:(lia))|].
  split; [exact (ex_aview_of_val1 (w_H W) (ms_mem ms) _ 248 V5 ltac:(lia))|].
  intros i Hi. rewrite KV by lia. exact (L6 i Hi).
Qed.
End rp.
