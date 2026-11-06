(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_head: the head of image B's LLVMFuzzerTestOneInput segment crt1, +0x5cc .. the first
   call (check_round_trip at +0x68c, check_braid at +0x6bc or __asan_memset at +0x6d4): c1h_head proves
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_defs.v c1_head_stmt.
   The code is one footprint run, lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_runs.v c1_run_head, carried into SRr by
   LLVMFuzzerTestOneInput_segX_crt1_fevt.v c1f_run from the state LeafCgKit.ms_of_regs of llvm_b_st_5cc, as
   a working branch 02bbf1e30df lib/B/Prog/crtB_w_setup.v:92-206 carries crt_seg4_F: the
   run's premises read off the cut point (its slots as 8-byte loads, crt1_geo.v; the store window 80(s1); the buffer
   addressable; the 0xa5 fill when the decode failed), the journal re-established across the run by
   lib/Reusable/YCbq.v:636 ajournal_exec with Wr = [sp1 + 80, sp1 + 88), the frame invariant and the memory clauses by
   LLVMFuzzerTestOneInput_segX_crt1_cut.v c1_step, and at each of the three exits the matching continuation
   c1_K_crt / c1_K_braid / c1_K_memset (the last two at the whole segment's journal count and meter: c1h_st_6f0). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require DecodeCallocWrapB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_cut
  LLVMFuzzerTestOneInput_segX_crt1_glue LLVMFuzzerTestOneInput_segX_crt1_geo LLVMFuzzerTestOneInput_segX_crt1_runs
  LLVMFuzzerTestOneInput_segX_crt1_fevt LLVMFuzzerTestOneInput_segX_crt1_defs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally; this file uses the plain ones (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* ---- an 8-byte load of the run back to cgif's reader (the converse of crt1_fevt.v c1f_rd8) ---- *)
Lemma c1h_rdn_nth : forall m (n : nat) A bs, rdn rsegs m (wa A) n = Some bs ->
  forall k, (k < n)%nat -> mrd rsegs m (wa (A + Z.of_nat k)) = nth_error bs k.
Proof.
  intros m n. induction n as [|n IH]; intros A bs H k Hk; [lia|].
  rewrite rdn_unfold in H.
  destruct (mrd rsegs m (wa A)) as [b|] eqn:Eb; [|discriminate].
  lazymatch type of H with context [rdn rsegs m ?a2 n] =>
    destruct (rdn rsegs m a2 n) as [r|] eqn:Er; [|discriminate] end.
  injection H as <-. rewrite wa_succ in Er.
  destruct k as [|k].
  - cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. rewrite <- (IH (A + 1) r Er k ltac:(lia)). do 2 f_equal. lia.
Qed.

Lemma c1h_rd8_slot : forall (W : world decodesegsB0) mem a v,
  0 <= v < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> w_H W (wa (a + i)) = false) ->
  ov_read_bytes rsegs mem (Z_to_bv 64 a) 8 = Some (le8 (Z_to_bv 64 v)) ->
  rdword (aview decodesegsB0 (w_H W) mem) a = Some v.
Proof.
  intros W mem a v Hv Hvis HR.
  apply DecodeCallocWrapB.val_mem_rdwordB; [exact Hv|].
  rewrite ov_rdn in HR. change (Z_to_bv 64 a) with (wa a) in HR.
  intros k Hk.
  rewrite (c1f_mbyte_mrd (w_H W) mem (a + Z.of_nat k)) by (apply Hvis; lia).
  rewrite (c1h_rdn_nth mem 8 a _ HR k Hk).
  unfold le8, word_to_le_bytes.
  rewrite (c1f_nth_le_bytes 8 (bv_unsigned (Z_to_bv 64 v)) k Hk). f_equal.
  first [unfold YO0f.le_byte | unfold YG0f.le_byte]. rewrite c1f_zbv8_mod, unsigned_lit_wrap.
  change (8 * Z.of_nat 8) with 64. reflexivity.
Qed.

Lemma c1h_zmod64 : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma c1h_shadow_addr : forall x, AsanCells.shadow_addr x = shadow_addr x.
Proof. intros x. unfold AsanCells.shadow_addr, shadow_addr, AsanCells.ASAN_K, SHADOW_OFF. ring. Qed.

(* ---- the braid / memset exits: the state at the whole segment's journal count and meter ---- *)
Lemma c1h_st_6f0 : forall {rc : YM05.RunCeil} B MT cx res out mode nch ns fx' ly' S' W' regs' mem' md',
  ameter_laws MT ->
  @c1_st rc B MT cx res out mode nch ns dec_ev_5cc (dec_spent_5cc MT (d_n cx)) (dec_rest_5cc MT)
    fx' ly' S' W' regs' mem' md' ->
  @c1_st rc B MT cx res out mode nch ns dec_ev_6f0 (dec_spent_6f0 MT (d_n cx)) (dec_rest_6f0 MT)
    fx' ly' S' W' regs' mem' md'.
Proof.
  intros rc B MT cx res out mode nch ns fx' ly' S' W' regs' mem' md' MTL
    (Hfz & Hcore & HP & Hr & Ho & Hmle & Hmok & Hmem & H80).
  pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_free_nonneg MT MTL).
  split; [exact Hfz|].
  split.
  { destruct Hcore as (HJ & REST). split; [|exact REST].
    eapply ajournal_mono_k; [exact HJ|]. unfold dec_ev_5cc, dec_ev_6f0. lia. }
  split; [exact HP|]. split; [exact Hr|]. split; [exact Ho|].
  split.
  { apply (mo_le_mono MT MTL _ _ _ _ Hmle). unfold dec_spent_6f0, dec_crt_cost_max. lia. }
  split.
  { apply (mo_ok_le MT MTL _ _ _ Hmok). unfold dec_rest_5cc, dec_crt_cost_max. lia. }
  exact (conj Hmem H80).
Qed.

(* ---- the head ---- *)
Theorem c1h_head : forall (rc : YM05.RunCeil) (B : asyms) (MT : ameter_ops) (RA_LLVMF : Z),
  @AR_laws rc decodesegsB0 B -> ameter_laws MT -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  @c1_head_stmt rc B MT RA_LLVMF.
Proof.
intros rc B MT RA_LLVMF LAWS MTL HCELLS HROS HRNE.
unfold c1_head_stmt. intros KCRT KBRAID KMSET cx W' c' HPRE H5cc.
destruct H5cc as (fx' & ly' & S' & regs' & mem' & md' & res & out & mode & nch & ns & -> & Hfz & Hcore & HBL &
  Hres4 & Hout4 & Hmle & Hmok & Hfrs & R10 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R26 & R27 & Hmode & Hfsh &
  Hgres & Hgout & Hfill & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
pose proof HPRE as (Hret & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hch & Hpay & Hn & Hnlen & Hnev & Hlive & Hrom).
assert (HP : Permutation (ablocks B ly' S')
  (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++ [(out, dec_b_olen nch ns)]))
  by (rewrite HBL; apply Permutation_refl).
pose proof Hcore as (HJ & Hfrs' & R8 & R9 & Hsp & Hsp1r & Hsp1al & Rgp & Rtp & _ & _ & _ & HFpres & _ & Hpayb & _).
pose proof (proj1 HJ) as HAR.
destruct (c1g_layout B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc res out nch ns Hcore HP Hnlen Hpay) as
  (Hsp0 & Hsp1 & H47 & Hinr & Hino & Ho4096 & Hoc & Hoapp & Hr4096 & Hrc & Hro & Hpo & Hof).
pose proof (c1e_geo B cx ly' S' W' regs' mem' md' dec_ev_5cc Hcore) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof (c1g_frame B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc Hcore) as (HF4096 & HFc & HFapp & _ & _).
pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
pose proof (c1g_body_len cx Hnlen) as Hbl.
pose proof (c1g_mode B LAWS cx ly' S' W' regs' mem' md' dec_ev_5cc mode nch ns HCELLS HROS HRNE Hrom Hcore Hmode Hfsh)
  as (Hm0 & Hmc & _).
pose proof Hmode as (_ & Hnch & Hns & _).
assert (HS32 : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hlen : 0 <= dec_b_len (d_n cx) < 2 ^ 26) by (unfold dec_b_len; lia).
assert (Holen1 : 1 <= dec_b_olen nch ns <= 48387).
{ unfold dec_b_olen. destruct ((0 <? nch) && (0 <? ns))%bool eqn:E; [|lia].
  apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1, E2. nia. }
assert (Hreqo : req_size (dec_b_olen nch ns) = dec_b_olen nch ns)
  by (unfold req_size; destruct (Z.eqb_spec (dec_b_olen nch ns) 0); lia).
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(lia)) as [Hq1 Hq2].
pose (wf := CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx)).
pose (fits0 := ((0 <? nch) && (0 <? ns))%bool).
pose (fits := dec_b_prod nch ns <? 481).
assert (Ed : c1_dok nch wf fits0 fits = CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
  by exact (c1g_dok (dec_b_len (d_n cx)) (d_body cx) nch ns Hnch Hns).
assert (Ep : c1_pok wf fits0 fits = CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
  by exact (c1g_pok (dec_b_len (d_n cx)) (d_body cx) nch ns Hnch Hns).
assert (Hpos : fits0 = true -> 0 < nch /\ 0 < ns).
{ intros E. apply andb_true_iff in E as [E1 E2]. apply Z.ltb_lt in E1, E2. lia. }
assert (Hpos2 : CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true -> 0 < nch /\ 0 < ns).
{ intros Hd. rewrite <- Ed in Hd. unfold c1_dok in Hd. apply Hpos. rewrite !andb_true_iff in Hd. tauto. }
(* ---- the run's premises ---- *)
assert (HSB : 0 <= d_sp1 cx /\ d_sp1 cx + 120 <= 18446744073709551616) by lia.
assert (Holen : 0 < dec_b_olen nch ns < 2 ^ 32) by lia.
assert (Hres : 4096 <= res /\ res + 1543 <= 18446744073709551616) by lia.
assert (Hout : 0 <= out /\ out + dec_b_olen nch ns + 1 <= 18446744073709551616) by lia.
assert (Hmode' : 0 <= mode < 2 ^ 64) by lia.
assert (RSTK : ExecF.rng (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W') (d_sp1 cx + 24) 72)
  by (apply (c1e_rng_stk B cx ly' S' W' regs' mem' md' dec_ev_5cc); [exact Hcore | lia | lia | lia]).
assert (RBUF : ExecF.rng (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W') out (dec_b_olen nch ns))
  by (apply (c1e_rng_block B LAWS ly' S' W' mem' md' out (dec_b_olen nch ns)); [exact HAR | exact Hino | lia | lia | lia]).
assert (RSH : ExecF.rng (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W')
  (AsanCells.shadow_addr out / 8 * 8)
  (AsanCells.shadow_addr (out + dec_b_olen nch ns - 1) / 8 * 8 + 8 - AsanCells.shadow_addr out / 8 * 8)).
{ rewrite !c1h_shadow_addr.
  pose proof (c1e_rng_shadow B LAWS ly' S' W' mem' md' out (dec_b_olen nch ns) HAR Hino ltac:(lia)) as X.
  rewrite Hreqo in X. exact X. }
assert (RD32 : ov_read_bytes rsegs mem' (Z_to_bv 64 (d_sp1 cx + 32)) 8 = Some (le8 (Z_to_bv 64 AsanCells.ASAN_K)))
  by exact (c1e_slot_rd8 B cx ly' S' W' regs' mem' md' dec_ev_5cc 32 SHADOW_OFF Hcore ltac:(lia) ltac:(lia) S32).
assert (RD40 : ov_read_bytes rsegs mem' (Z_to_bv 64 (d_sp1 cx + 40)) 8 = Some (le8 (Z_to_bv 64 res)))
  by exact (c1e_slot_rd8 B cx ly' S' W' regs' mem' md' dec_ev_5cc 40 res Hcore ltac:(lia) ltac:(lia) S40).
assert (RD72 : ov_read_bytes rsegs mem' (Z_to_bv 64 (d_sp1 cx + 72)) 8 = Some (le8 (Z_to_bv 64 ns))).
{ pose proof (c1e_slot_rd8 B cx ly' S' W' regs' mem' md' dec_ev_5cc 72 (ns mod 2 ^ 64) Hcore ltac:(lia) ltac:(lia) S72)
    as X. rewrite c1h_zmod64 in X. exact X. }
assert (RD88 : ov_read_bytes rsegs mem' (Z_to_bv 64 (d_sp1 cx + 88)) 8 = Some (le8 (Z_to_bv 64 out)))
  by exact (c1e_slot_rd8 B cx ly' S' W' regs' mem' md' dec_ev_5cc 88 out Hcore ltac:(lia) ltac:(lia) S88).
assert (HSTKP : forall a, d_sp0 cx - DEC_LLVMF_STK <= a < d_sp0 cx -> apresent (w_H W') mem' a)
  by exact (c1e_stk_present B cx ly' S' W' regs' mem' md' dec_ev_5cc Hcore).
assert (HW80 : store_ok rsegs mem' (Z_to_bv 64 (d_sp1 cx + 80)) 8 = true).
{ pose proof (wr_at_store_ok rsegs mem' (d_sp1 cx + 80) 8 0 8
    (c1f_wr_at_of (w_H W') mem' (d_sp1 cx + 80) 8 ltac:(lia) ltac:(lia) (fun a Ha => HSTKP a ltac:(lia)))
    ltac:(lia) ltac:(lia)) as X.
  rewrite Z.add_0_r in X. exact X. }
assert (AD : AsanCells.addressable mem' out (dec_b_olen nch ns)).
{ apply (dec_leafb_addressable W' mem' out (dec_b_olen nch ns)).
  - apply (range_addressable_of_block decodesegsB0 B LAWS ly' S' W' mem' md' out (dec_b_olen nch ns) out
      (dec_b_olen nch ns) HAR Hino); lia.
  - lia.
  - lia.
  - unfold AsanCells.APPMEM_END. lia.
  - intros i Hi. apply (dec_leafb_app_of_in_app out (req_size (dec_b_olen nch ns)) i Hoapp). lia. }
assert (HA5 : c1_dok nch wf fits0 fits = false ->
  forall i, 0 <= i < dec_b_olen nch ns -> mrd rsegs mem' (wa (out + i)) = Some (Z_to_bv 8 165)).
{ rewrite Ed. intros Hd i Hi.
  destruct (dec_leafb_mrd_aview W' mem' (out + i) _ (Hfill Hd i Hi)) as (b & Hb & Hbv).
  transitivity (Some b); [exact Hb|]. f_equal. apply bv_eq. rewrite Hbv. reflexivity. }
(* ---- the start state ---- *)
assert (G2r : YK11.getr regs' (Z_to_bv 5 2) = Z_to_bv 64 (d_sp1 cx)).
{ apply bv_eq. rewrite (MState.unsigned_lit (d_sp1 cx)) by lia. exact Hsp. }
assert (G9r : YK11.getr regs' (Z_to_bv 5 9) = Z_to_bv 64 (d_sp1 cx)) by exact R9.
assert (G10r : YK11.getr regs' (Z_to_bv 5 10) =
  Z_to_bv 64 (if CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then ns else -1)) by exact R10.
assert (G18r : YK11.getr regs' (Z_to_bv 5 18) = Z_to_bv 64 (if fits then 1 else 0)) by exact R18.
assert (G19r : YK11.getr regs' (Z_to_bv 5 19) = Z_to_bv 64 (if wf then 1 else 0)) by exact R19.
assert (G20r : YK11.getr regs' (Z_to_bv 5 20) = Z_to_bv 64 (dec_b_len (d_n cx))) by exact R20.
assert (G21r : YK11.getr regs' (Z_to_bv 5 21) = Z_to_bv 64 mode) by exact R21.
assert (G22r : YK11.getr regs' (Z_to_bv 5 22) = Z_to_bv 64 out) by exact R22.
assert (G23r : YK11.getr regs' (Z_to_bv 5 23) = Z_to_bv 64 nch) by exact R23.
assert (G24r : YK11.getr regs' (Z_to_bv 5 24) = Z_to_bv 64 (if fits0 then 1 else 0)) by exact R24.
assert (G26r : YK11.getr regs' (Z_to_bv 5 26) = Z_to_bv 64 (dec_b_olen nch ns)) by exact R26.
assert (G27r : YK11.getr regs' (Z_to_bv 5 27) = Z_to_bv 64 res) by exact R27.
pose (X3 := YK11.getr regs' (Z_to_bv 5 3)). pose (X4 := YK11.getr regs' (Z_to_bv 5 4)).
pose (X8 := YK11.getr regs' (Z_to_bv 5 8)). pose (X25 := YK11.getr regs' (Z_to_bv 5 25)).
pose (FR := @fp_regs fx'). pose (FC := @fp_csr fx').
pose proof (c1_run_head (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W') X3 X4 X8 X25 FR FC
  (d_sp1 cx) res out mode (dec_b_len (d_n cx)) (dec_b_olen nch ns) nch ns wf fits0 fits
  HSB Hnch Hns Holen Hres Hout Hlen Hmode' Hpos RSTK RBUF RSH mem' RD32 RD40 RD72 RD88 HW80 AD HA5
  (CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns)
  (YK11.getr regs' (Z_to_bv 5 1)) (YK11.getr regs' (Z_to_bv 5 5)) (YK11.getr regs' (Z_to_bv 5 6))
  (YK11.getr regs' (Z_to_bv 5 7)) (YK11.getr regs' (Z_to_bv 5 28)) (YK11.getr regs' (Z_to_bv 5 29))
  (YK11.getr regs' (Z_to_bv 5 30)) (YK11.getr regs' (Z_to_bv 5 31))
  (YK11.getr regs' (Z_to_bv 5 11)) (YK11.getr regs' (Z_to_bv 5 12)) (YK11.getr regs' (Z_to_bv 5 13))
  (YK11.getr regs' (Z_to_bv 5 14)) (YK11.getr regs' (Z_to_bv 5 15)) (YK11.getr regs' (Z_to_bv 5 16))
  (YK11.getr regs' (Z_to_bv 5 17)) Ed) as HRUN.
lazymatch type of HRUN with ExecF.evtF _ _ ?P _ =>
  assert (HRUN2 : ExecF.evtF rsegs (LeafCgKit.RNG_W (world decodesegsB0) (@w_H decodesegsB0) W') P
                    (@LeafCgKit.ms_of_regs fx' (DEC_A_LLVMF + 0x5cc) regs' mem')) end.
{ unfold LeafCgKit.ms_of_regs.
  rewrite G2r, G9r, G10r, G18r, G19r, G20r, G21r, G22r, G23r, G24r, G26r, G27r.
  replace (LeafCgKit.w64 (DEC_A_LLVMF + 1484)) with (Z_to_bv 64 (C1 1484))
    by (unfold LeafCgKit.w64; f_equal; unfold C1, DEC_A_LLVMF, DecodeBList.AF_LLVMFuzzerTestOneInput; lia).
  exact HRUN. }
clear HRUN.
apply (c1f_run W' regs' mem' md' (DEC_A_LLVMF + 0x5cc) _ _ (c1g_evtF_grows _ _ _ HRUN2)).
intros ms' md'' (ms0 & (HQ & HGROW) & HEQ) HSBM.
destruct HQ as (mm & (MU & WM & R80) & HCASES).
(* ---- what the run leaves, at any of its three exits ---- *)
assert (KAV : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 80 <= a < d_sp1 cx + 88) ->
  aview decodesegsB0 (w_H W') mm a = aview decodesegsB0 (w_H W') mem' a).
{ intros a Ha Hn'. unfold aview, mbyte, mrestrict. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  cbn [outside]. rewrite (MState.unsigned_lit a) by lia. split; [exact Hn' | exact I]. }
assert (HFR : forall x : word, ~ (d_sp1 cx + 80 <= bv_unsigned x < d_sp1 cx + 88) ->
  mrestrict (w_H W') mm x = mrestrict (w_H W') mem' x).
{ intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I]. }
assert (HHID : forall x : word, w_H W' x = true -> mm x = mem' x).
{ intros x Hx. apply MU. cbn [outside]. split; [|exact I]. intros Hr.
  pose proof (bv_unsigned_in_range 64 x) as Hxr.
  destruct (HSTKP (bv_unsigned x) ltac:(lia)) as (Hh & _).
  rewrite Z_to_bv_bv_unsigned in Hh. rewrite Hh in Hx. discriminate. }
assert (HWB : forall a, d_sp1 cx + 80 <= a < d_sp1 cx + 88 ->
  awr_byte DEC_LLVMF_STK (d_sp0 cx) [] (ablocks B (d_ly cx) (d_S cx)) (ablocks B ly' S') ly'
    [(DEC_FCLASS, d_fpos cx)] a)
  by (intros a Ha; left; lia).
assert (COMMON : forall (pc ra : Z) (a0 a1 a2 a3 s2v s6v : word),
  0 <= ra < 2 ^ 64 ->
  c1_at X3 X4 X8 X25 FR FC (d_sp1 cx) res mode (dec_b_len (d_n cx)) (dec_b_olen nch ns) nch fits0 pc ra
    a0 a1 a2 a3 s2v (Z_to_bv 64 (if c1_pok wf fits0 fits then 1 else 0)) s6v mm ms0 ->
  ms' = @YK11.mkst fx' (ms_regs ms') (Z_to_bv 64 pc) mm (YK11.seg_rom decodesegsB0) /\
  @c1_st rc B MT cx res out mode nch ns dec_ev_5cc (dec_spent_5cc MT (d_n cx)) (dec_rest_5cc MT)
    fx' ly' S' W' (ms_regs ms') mm md'' /\
  c1_regs cx res out mode nch ns (ms_regs ms') /\
  YK11.getr (ms_regs ms') 1 = Z_to_bv 64 ra /\
  YK11.getr (ms_regs ms') 10 = a0 /\ YK11.getr (ms_regs ms') 11 = a1 /\
  YK11.getr (ms_regs ms') 12 = a2 /\ YK11.getr (ms_regs ms') 13 = a3 /\
  YK11.getr (ms_regs ms') 18 = s2v /\ YK11.getr (ms_regs ms') 22 = s6v /\
  (CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true ->
     garr8 decodesegsB0 (mrestrict (w_H W') mm) out
       (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)))).
{ intros pc ra a0 a1 a2 a3 s2v s6v Hra' (r1' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & a4' & a5' & a6' & a7' &
    Ems0 & Hr1').
  subst ms0.
  pose proof (@c1f_ms_shape fx' _ _ _ ms' HEQ) as Ems'.
  pose proof (fun r Hr => c1f_ms_reg _ _ _ _ _ _ _ ms' r HEQ Hr) as GEQ.
  assert (Q2 : YK11.getr (ms_regs ms') (Z_to_bv 5 2) = YK11.getr regs' (Z_to_bv 5 2))
    by (etransitivity; [exact (GEQ (Z_to_bv 5 2) eq_refl) | symmetry; exact G2r]).
  assert (Q3 : YK11.getr (ms_regs ms') 3 = YK11.getr regs' 3) by exact (GEQ (Z_to_bv 5 3) eq_refl).
  assert (Q4 : YK11.getr (ms_regs ms') 4 = YK11.getr regs' 4) by exact (GEQ (Z_to_bv 5 4) eq_refl).
  assert (Q8 : YK11.getr (ms_regs ms') 8 = YK11.getr regs' 8) by exact (GEQ (Z_to_bv 5 8) eq_refl).
  assert (Q9 : YK11.getr (ms_regs ms') 9 = YK11.getr regs' 9)
    by (etransitivity; [exact (GEQ (Z_to_bv 5 9) eq_refl) | symmetry; exact G9r]).
  assert (Qsp : spZ (ms_regs ms') = spZ regs').
  { change (bv_unsigned (YK11.getr (ms_regs ms') (Z_to_bv 5 2)) = bv_unsigned (YK11.getr regs' (Z_to_bv 5 2))).
    rewrite Q2. reflexivity. }
  (* the journal across the run *)
  pose proof (ajournal_exec decodesegsB0 B LAWS c1f_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm md''
    (fun a => d_sp1 cx + 80 <= a < d_sp1 cx + 88) HJ HFR (c1g_mem_grows_restrict _ _ _ HGROW) HHID HSBM HWB)
    as HJ2.
  (* the five kept regions *)
  assert (KS : forall a, d_sp1 cx <= a < d_sp0 cx -> ~ (d_sp1 cx + 80 <= a < d_sp1 cx + 88) ->
    aview decodesegsB0 (w_H W') mm a = aview decodesegsB0 (w_H W') mem' a)
    by (intros a Ha Hn'; apply KAV; [lia | exact Hn']).
  assert (KF : forall a, d_F cx <= a < d_F cx + 64 ->
    aview decodesegsB0 (w_H W') mm a = aview decodesegsB0 (w_H W') mem' a /\ apresent (w_H W') mm a).
  { intros a Ha. split; [apply KAV; lia|].
    destruct (HFpres a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b.
    rewrite (MU (Z_to_bv 64 a)); [exact Hb|]. cbn [outside]. rewrite (MState.unsigned_lit a) by lia.
    split; [lia | exact I]. }
  assert (KH : forall a, d_SH cx <= a < d_SH cx + 8 ->
    aview decodesegsB0 (w_H W') mm a = aview decodesegsB0 (w_H W') mem' a).
  { intros a Ha. unfold d_SH, shadow_addr, SHADOW_OFF in Ha.
    pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
    assert (Hd : d_F cx / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    apply KAV; lia. }
  assert (KR : forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
    aview decodesegsB0 (w_H W') mm (res + i) = aview decodesegsB0 (w_H W') mem' (res + i))
    by (intros i Hi; apply KAV; lia).
  assert (KP : forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
    aview decodesegsB0 (w_H W') mm (d_p cx + i) = aview decodesegsB0 (w_H W') mem' (d_p cx + i)).
  { intros i Hi. destruct (Hpo i Hi) as (Hp1 & _). apply KAV; lia. }
  destruct (c1_step B cx ly' S' W' regs' mem' md' dec_ev_5cc res out mode nch ns ly' S' W' (ms_regs ms') mm md''
              dec_ev_5cc HCELLS HROS HRNE Hrom Hcore
              (conj Hfrs (conj Hmode (conj Hfsh (conj Hgres (conj S24 (conj S32 (conj S40 (conj S56 (conj S64
                (conj S72 (conj S88 S112)))))))))))
              HJ2 Hfrs' (fun b Hb => Hb) Q8 Q9 Qsp Q3 Q4 KS KF KH KR KP) as (Hcore2 & Hmem2).
  assert (H80 : dec_b_slot cx (aview decodesegsB0 (w_H W') mm) 80 (res + 50)).
  { unfold dec_b_slot. apply (c1h_rd8_slot W' mm (d_sp1 cx + 80) (res + 50)); [lia | | exact R80].
    intros i Hi. exact (proj1 (HSTKP (d_sp1 cx + 80 + i) ltac:(lia))). }
  split; [exact Ems'|].
  split.
  { split; [exact Hfz|]. split; [exact Hcore2|]. split; [exact HP|]. split; [exact Hres4|].
    split; [exact Hout4|]. split; [exact Hmle|]. split; [exact Hmok|]. split; [exact Hmem2 | exact H80]. }
  split.
  { split.
    { transitivity (Z_to_bv 64 (if c1_pok wf fits0 fits then 1 else 0));
        [exact (GEQ (Z_to_bv 5 19) eq_refl) | rewrite Ep; reflexivity]. }
    split; [exact (GEQ (Z_to_bv 5 20) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 21) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 23) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 24) eq_refl)|].
    split; [exact (GEQ (Z_to_bv 5 26) eq_refl) | exact (GEQ (Z_to_bv 5 27) eq_refl)]. }
  split.
  { transitivity r1'; [exact (GEQ (Z_to_bv 5 1) eq_refl)|].
    apply bv_eq. rewrite Hr1', (MState.unsigned_lit ra) by lia. reflexivity. }
  split; [exact (GEQ (Z_to_bv 5 10) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 11) eq_refl)|].
  split; [exact (GEQ (Z_to_bv 5 12) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 13) eq_refl)|].
  split; [exact (GEQ (Z_to_bv 5 18) eq_refl)|]. split; [exact (GEQ (Z_to_bv 5 22) eq_refl)|].
  intros Hd. destruct (Hpos2 Hd) as [Pn Ps].
  apply (c1_garr8_kept (w_H W') (w_H W') mem' mm out); [|exact (Hgout Hd)].
  rewrite length_map. intros i Hi.
  assert (Hbl' : length (CDec.braid_out (d_body cx) nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CDec.braid_out; rewrite !length_map, length_seq; reflexivity).
  rewrite Hbl' in Hi.
  assert (Eo : dec_b_olen nch ns = 3 * nch * ns).
  { unfold dec_b_olen. rewrite (proj2 (Z.ltb_lt 0 nch) Pn), (proj2 (Z.ltb_lt 0 ns) Ps). reflexivity. }
  apply KAV; lia. }
assert (RAo : forall o, 0 <= o < 4096 -> 0 <= C1 o < 2 ^ 64) by (intros o Ho; unfold C1, decodeb_text; lia).
assert (RAe : forall o, Z_to_bv 64 (C1 o) = w64 (DEC_A_LLVMF + o))
  by (intros o; unfold w64, C1, DEC_A_LLVMF, DecodeBList.AF_LLVMFuzzerTestOneInput; f_equal; lia).
destruct HCASES as [(Hq & Hdk & Hns12) | [(Hq & Hdk & Hns12) | (Hq & Hdk)]].
- (* check_round_trip at +0x68c *)
  destruct Hq as (s2v & Hat).
  destruct (COMMON _ _ _ _ _ _ _ _ (RAo 0x690 ltac:(lia)) Hat) as
    (Ems' & HST & HREG & Q1 & Q10 & Q11 & Q12 & Q13 & _ & Q22 & HGB).
  rewrite Ed in Hdk. rewrite Ems'.
  refine (KCRT cx res out mode nch ns fx' ly' S' W' (ms_regs ms') mm md'' HPRE HST HREG Hdk Hns12 (HGB Hdk)
            Q22 _ Q10 Q11 Q12 Q13).
  rewrite Q1. apply RAe.
- (* check_braid at +0x6bc *)
  destruct Hq as (s2v & Hat).
  destruct (COMMON _ _ _ _ _ _ _ _ (RAo 0x6c0 ltac:(lia)) Hat) as
    (Ems' & HST & HREG & Q1 & Q10 & Q11 & Q12 & Q13 & _ & Q22 & HGB).
  rewrite Ed in Hdk. rewrite Ems'.
  refine (KBRAID cx res out mode nch ns fx' ly' S' W' (ms_regs ms') mm md'' HPRE (c1h_st_6f0 B MT cx res out mode
            nch ns fx' ly' S' W' (ms_regs ms') mm md'' MTL HST) HREG Hdk (HGB Hdk) Q22 _ Q10 Q11 Q12 Q13).
  rewrite Q1. apply RAe.
- (* __asan_memset at +0x6d4 *)
  destruct Hq as (a3 & Hat).
  destruct (COMMON _ _ _ _ _ _ _ _ (RAo 0x6d8 ltac:(lia)) Hat) as
    (Ems' & HST & HREG & Q1 & Q10 & Q11 & Q12 & _ & Q18 & _ & _).
  rewrite Ems'.
  refine (KMSET cx res out mode nch ns fx' ly' S' W' (ms_regs ms') mm md'' HPRE (c1h_st_6f0 B MT cx res out mode
            nch ns fx' ly' S' W' (ms_regs ms') mm md'' MTL HST) HREG Q18 _ Q10 Q11 Q12).
  rewrite Q1. apply RAe.
Qed.
