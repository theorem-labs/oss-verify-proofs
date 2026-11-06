(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, with its module paths and module names changed; 844 of its 885 lines of code are new or changed and 166 lines of the source are left out. *)
(* fs program part, lane ENTRY, segment S8 of the LLVMFuzzerTestOneInput walk (fs.asan 0x810f0-0x8110c):
   `ld a2, 0(s4)` (len), check_reject_clean_starved(text, body, len) (0x810fc, ra 0x81100), fuzz_free(body) (0x81104,
   ra 0x81108), free(text) (0x8110c, ra 0x81110 = PC_epi). rule 24: no function proved (fs's own harness entry, written
   in the donor cgif_file_fuzzer's form; `proof-index LLVMFuzzerTestOneInput` covers other units' harnesses only).
   fe_seg8 : fe_from ... (fe_ss PC_epi []) INV_C9 -> fe_from ... (fe_ss RA_crc [fe_len_atom 46]) INV_C7, composed of
   three call steps, each between two canonical states (FSW_entry_canon.fe_canon): fe8_st (the starved check),
   fe8_ff (fuzz_free), fe8_free (free). Before each run the state's regions are made read-only (YP06.st_ok_submem), so
   the run leaves memory unchanged (YI04.frame_of_ro) and every data premise carries over by same_below.
   Port-from: donor cgif_file_fuzzer lib/A/ACfd.v:133-171 (free(img) at the end of the entry walk through YC85.afree04_sub,
   chain_pre by achain_chain_pre, the trace in the universe, Permutation_app_inv on the freed block), lib/A/ACfi.v:128
   (afree04_rule_triv from afree_realizes), lib/YCf6.v:82-101 (ablocks_perm_twice); program calls as the contract's
   recipe (YCbq.afn_pre_at, FSW_K3.fsw_ajournal_sub5, fe_canon). The saved words are read back with
   ACem.rdword_of_val_mem (Require only). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_pstat_store FSW_strkit FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import ACfn FSH_Harness FSH_Fn_entry FSW_entry_defs
FSW_entry_canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_crt FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require ACem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the read-only view of the canonical regions: the frame (with the chunks cs), the saved words; no write window ---- *)
Definition fe8_ro_regions (cs : list YP09.chunk) : list YP09.region :=
  [YP09.mkRegion (Some 24%nat) 0 64 0 0 (YP09.mkChunk 56 (CVal 8 (SOff 44 0)) :: cs);
   YP09.mkRegion (Some 8%nat) (-88) 0 0 0 fe_sv_chunks].
Lemma fe8_ro_sub : forall cs, submem (fe8_ro_regions cs) (fe_regions cs).
Proof.
intros cs. unfold fe8_ro_regions, fe_regions, fe_frame_region, fe_shadow_region, fs_ret_s0_region.
apply submem_keep; [|apply submem_drop; apply submem_keep; [|apply submem_nil]].
- unfold subregion. cbn. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. auto.
- unfold subregion. cbn. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. auto.
Qed.
Lemma fe8_ro_all : forall cs, all_ro (fe8_ro_regions cs) = true.
Proof. intros cs. reflexivity. Qed.

(* the saved words: eleven 8-byte chunks of extra atoms 33 .. 43, in [-88, 0) *)
Lemma fe8_sv_shape : Forall (fun c => exists j, (1 <= j < 12)%nat /\ YP09.c_val c = CVal 8 (SOff (32 + j) 0) /\
  -88 <= YP09.c_off c /\ YP09.c_off c + 8 <= 0) fe_sv_chunks.
Proof.
unfold fe_sv_chunks. cbn.
repeat (constructor; [eexists; split; [|split; [reflexivity|]]; cbn; lia|]). constructor.
Qed.

(* a CVal chunk read under another env and another memory: same atom values, same bytes *)
Lemma fe8_chunk_move : forall E E' (m m' : word -> option byte) base c w v,
  YP09.c_val c = CVal w v -> sv_denot E' v = sv_denot E v ->
  (forall i, 0 <= i < Z.of_N w -> mbyte tfibsegs m' (base + YP09.c_off c + i) = mbyte tfibsegs m (base + YP09.c_off c + i)) ->
  YP09.chunk_ok tfibsegs E m base c -> YP09.chunk_ok tfibsegs E' m' base c.
Proof.
intros E E' m m' base [off cv] w v Hc Hv Hm H i Hi. cbn in Hc. subst cv. cbn [YP09.c_off] in *.
unfold YP09.c_len in Hi. cbn in Hi. destruct (H i Hi) as (b & H1 & H2). exists b. split.
- cbn in H1 |- *. rewrite Hv. exact H1.
- rewrite (Hm i Hi). exact H2.
Qed.
Lemma fe8_sv_move : forall cx E E' (m m' : word -> option byte),
  fe_E cx E -> fe_E cx E' ->
  (forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m (fe_sp0 cx)) fe_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E' m' (fe_sp0 cx)) fe_sv_chunks.
Proof.
intros cx E E' m m' HE HE' Hm HF. pose proof fe8_sv_shape as Hsh.
rewrite Forall_forall in HF, Hsh |- *. intros c Hc.
destruct (Hsh c Hc) as (j & Hj & Hv & Ho1 & Ho2).
apply (fe8_chunk_move E E' m m' (fe_sp0 cx) c 8 (SOff (32 + j) 0) Hv); [| |exact (HF c Hc)].
- rewrite !fsw_SOff0. rewrite (HE j ltac:(lia)), (HE' j ltac:(lia)). reflexivity.
- intros i Hi. apply Hm. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis tl_code : as_code B = Tfib_code.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis fe_fr : FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis en_starved : @check_reject_clean_starved_spec fx rc SK tfibsegs B.
Hypothesis en_free : @fuzz_free_spec fx rc SK tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* donor lib/YCf6.v:82-101 ablocks_perm_twice: a block listed twice in a permutation of ablocks contradicts AR *)
Lemma fe8_perm_twice : forall ly S (W : world tfibsegs) mem md l1 l2 x,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros ly S W mem md l1 l2 x HAR HP H1 H2.
apply in_split in H1 as (a1 & a2 & E1). apply in_split in H2 as (c1 & c2 & E2). subst l1 l2.
assert (HP2 : Permutation (ablocks B ly S) (x :: x :: ((a1 ++ a2) ++ c1) ++ c2)).
{ eapply Permutation_trans; [exact HP|].
  eapply Permutation_trans. { apply Permutation_app; [apply Permutation_sym; apply (Permutation_middle a1 a2 x) | apply Permutation_refl]. }
  change ((x :: a1 ++ a2) ++ c1 ++ x :: c2) with (x :: ((a1 ++ a2) ++ (c1 ++ x :: c2))).
  apply perm_skip.
  replace ((a1 ++ a2) ++ (c1 ++ x :: c2)) with (((a1 ++ a2) ++ c1) ++ x :: c2) by (first [rewrite app_assoc; reflexivity | rewrite <- app_assoc; reflexivity]).
  change (x :: ((a1 ++ a2) ++ c1) ++ c2) with (x :: (((a1 ++ a2) ++ c1) ++ c2)).
  apply Permutation_sym. apply (Permutation_middle ((a1 ++ a2) ++ c1) c2 x). }
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
destruct x as [b m].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hx) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (sep_blocks_perm tfibsegs B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* an application byte reads the same through the unpoisoned memory (U's bytes are shadow bytes) *)
Lemma fe8_aview_unp : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U m) a = aview tfibsegs (w_H W) m a.
Proof.
intros ly S U W m md a H Ha Happ. apply (aview_unpoison_out tfibsegs). rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
destruct (ush_facts tfibsegs B ly S U W m md a H E) as (_ & L1 & L2). lia.
Qed.

(* the numbers of the entry *)
Lemma fe8_nums : forall cx, fe_base B cx ->
  fe_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= fe_sp0 cx /\ fe_sp0 cx <= 2 ^ 47 /\
  fe_sp0 cx - 112 <= fe_sp1 cx <= fe_sp0 cx - 96 /\ fe_sp1 cx mod 32 = 0 /\ fe_sp1 cx mod 16 = 0 /\
  fe_sp0 cx <= ly_top (c_ly cx) /\ ly_top (c_ly cx) <= 2 ^ 47.
Proof.
intros cx (HPRE & _). pose proof HPRE as (Hafn & _). pose proof Hafn as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
unfold fe_sp1. unfold fe_sp0 in *.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 96) ltac:(unfold LLVMF_STK in *; lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (R1 & R2 & R3).
unfold LLVMF_STK in *. lia.
Qed.

Lemma fe8_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.
Lemma fe8_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof. intros a Ha. apply fs_rw3_img. exact (pstat_bounds a Ha). Qed.

(* lia on the arithmetic hypotheses only (some kit hypotheses stop lia's preprocessing) *)
Ltac fe8_lia :=
  repeat match goal with H : ?T |- _ =>
    match type of T with Prop =>
      lazymatch T with
      | _ <= _ => fail | _ < _ => fail | @eq Z _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail
      | _ => clear H
      end
    end
  end; lia.

Ltac fe8_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] => let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end;
  lia.

(* a register the state holds as an atom *)
Lemma fe8_reg : forall H E ss ms (r : bv 5) n, st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  YK11.getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fsw_SOff0. Qed.
(* a callee-saved register the call-site state holds as an atom, read after the call *)
Lemma fe8_kept : forall H E ss ms regs' (r : bv 5) n, st_ok tfibsegs E ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> aregs_preserved (ms_regs ms) regs' -> acallee_saved (bv_unsigned r) ->
  YK11.getr regs' r = ew E n.
Proof.
intros H E ss ms regs' r n HS Hr HP Hc. rewrite (fsw_pres (ms_regs ms) regs' r HP Hc). exact (fe8_reg H E ss ms r n HS Hr).
Qed.
(* the canonical registers after a call, from a call-site state that holds them as atoms *)
Lemma fe8_core_after : forall cx E ss H ms regs' xs,
  fe_regs_core cx E -> st_ok tfibsegs E ss (restrict H ms) ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 /\ sr_get (ss_regs ss) 3%bv = SOff 3 0 /\ sr_get (ss_regs ss) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ss) 8%bv = SOff 8 0 /\ sr_get (ss_regs ss) 9%bv = SOff 9 0 /\ sr_get (ss_regs ss) 18%bv = SOff 18 0 /\
  sr_get (ss_regs ss) 24%bv = SOff 24 0 /\ sr_get (ss_regs ss) 25%bv = SOff 25 0 /\
  sr_get (ss_regs ss) 26%bv = SOff 26 0 /\ sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
  aregs_preserved (ms_regs ms) regs' ->
  fe_regs_core cx (Ereg regs' (fe_extra cx ++ xs)).
Proof.
intros cx E ss H ms regs' xs (H8 & H9 & H2 & H18 & H24 & H25 & H3 & H4 & H26 & H27) HS
  (S2 & S3 & S4 & S8 & S9 & S18 & S24 & S25 & S26 & S27) HP.
assert (K : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  sr_get (ss_regs ss) r = SOff n 0 -> ew (Ereg regs' (fe_extra cx ++ xs)) n = ew E n).
{ intros r n Hn Hc Hr. rewrite (ew_Ereg_nat regs' _ n r Hn). exact (fe8_kept H E ss ms regs' r n HS Hr HP Hc). }
unfold fe_regs_core.
rewrite (K 8%bv 8%nat eq_refl ltac:(fe8_cs) S8), (K 9%bv 9%nat eq_refl ltac:(fe8_cs) S9), (K 2%bv 2%nat eq_refl ltac:(fe8_cs) S2),
  (K 18%bv 18%nat eq_refl ltac:(fe8_cs) S18), (K 24%bv 24%nat eq_refl ltac:(fe8_cs) S24), (K 25%bv 25%nat eq_refl ltac:(fe8_cs) S25),
  (K 3%bv 3%nat eq_refl ltac:(fe8_cs) S3), (K 4%bv 4%nat eq_refl ltac:(fe8_cs) S4), (K 26%bv 26%nat eq_refl ltac:(fe8_cs) S26),
  (K 27%bv 27%nat eq_refl ltac:(fe8_cs) S27).
repeat split; assumption.
Qed.

(* the callee's chain at a call from a canonical state: s0 is the entry sp, a frame record over the entry's (empty)
   chain when the entry sp is not within 16 of ly_top (YCbq.achain_push), else the empty chain *)
Definition fe8_ch (cx : fecx) : list (Z * Z * Z) :=
  if fe_sp0 cx <? ly_top (c_ly cx) - 16 then [(fe_sp0 cx, RA_LLVMF, s0Z (c_regs cx))] else [].
Lemma fe8_achain : forall cx lyc Sc U (W : world tfibsegs) mem mdc k E,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison U mem) mdc k ->
  ARU tfibsegs B lyc Sc U W mem mdc -> fe_E cx E ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (fe_sp0 cx)) fe_sv_chunks ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U mem)) (fe_sp1 cx) (fe_sp0 cx) (fe8_ch cx).
Proof.
intros cx lyc Sc U W mem mdc k E Hbase HJ HARU HE Hsv.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof Hbase as (HPRE & _). pose proof HPRE as (Hafn & Hra & _).
pose proof Hafn as (_ & _ & _ & _ & _ & _ & _ & Hch & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite Forall_forall in Hsv.
assert (RW : forall off j v, (1 <= j < 12)%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0))) fe_sv_chunks ->
  nth j (fe_extra cx) (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> fe_sp0 cx - 88 <= fe_sp0 cx + off ->
  off + 8 <= 0 ->
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) (fe_sp0 cx + off) = Some v).
{ intros off j v Hj Hin Hn Hv Ho1 Ho2.
  pose proof (val_of_chunk_ok tfibsegs E _ (fe_sp0 cx) off 8 (SOff (32 + j) 0) v (Hsv _ Hin)
    ltac:(rewrite fsw_SOff0, (HE j ltac:(lia)); exact Hn) ltac:(cbn; lia) ltac:(cbn; lia)) as Hval.
  change (N.to_nat 8) with 8%nat in Hval.
  rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) (unpoison U mem))).
  - apply ACem.rdword_of_val_mem; [exact Hval | exact Hv].
  - intros q Hq. assert (Hb : 0 <= fe_sp0 cx + off + q < 2 ^ 64) by (clear - N2 N3 Ho1 Ho2 Hq C1; unfold LLVMF_STK in N2; lia).
    apply (fe8_aview_unp lyc Sc U W mem mdc _ HARU Hb). right. clear - N2 Ho1 Hq C1 C3. unfold LLVMF_STK in N2. lia. }
assert (Hsv8 : rdword (aview tfibsegs (w_H W) (unpoison U mem)) (fe_sp0 cx - 8) = Some RA_LLVMF).
{ replace (fe_sp0 cx - 8) with (fe_sp0 cx + -8) by lia.
  apply (RW (-8) 1%nat); [lia | cbn; left; reflexivity | | unfold RA_LLVMF; lia | lia | lia].
  cbn [nth fe_extra map app fe_saved_regs]. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hsv16 : rdword (aview tfibsegs (w_H W) (unpoison U mem)) (fe_sp0 cx - 16) = Some (s0Z (c_regs cx))).
{ replace (fe_sp0 cx - 16) with (fe_sp0 cx + -16) by lia.
  apply (RW (-16) 2%nat); [lia | cbn; right; left; reflexivity | | | lia | lia].
  - cbn [nth fe_extra map app fe_saved_regs]. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned.
  - unfold s0Z. pose proof (bv_unsigned_in_range 64 (YK11.getr (c_regs cx) 8%bv)) as Hq.
    change (bv_modulus 64) with (2 ^ 64) in Hq. exact Hq. }
unfold fe8_ch. destruct (Z.ltb_spec (fe_sp0 cx) (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
- apply (achain_ly_top (c_ly cx) lyc _ _ _ _ Etop).
  apply (achain_push (c_ly cx) (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) _ (fe_sp0 cx) (s0Z (c_regs cx)) RA_LLVMF []
    (fe_sp1 cx)); [exact Hch | lia | | exact Hsv8 | exact Hsv16 | unfold RA_LLVMF; lia | unfold LLVMF_STK in N2; lia | | lia | lia].
  + intros a Ha. apply F1; [unfold LLVMF_STK in N2; lia | lia].
  + clear - N1. Z.div_mod_to_equations. lia.
- left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* the read-only data view at a call (fpreU's arodata): the entry's, kept by the walk's static clause *)
Lemma fe8_ro_segs : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fe8_relro : seg_covers FS_RLO (FS_RHI - FS_RLO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fe8_arodata : forall cx lyc Sc U (W : world tfibsegs) mem mdc own k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own lyc Sc W (unpoison U mem) mdc k ->
  ARU tfibsegs B lyc Sc U W mem mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem).
Proof.
intros cx lyc Sc U W mem mdc own k Hbase HJ HARU a Ha Ho He.
pose proof Hbase as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Hi : in_img tfibsegs a).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] |].
  apply (seg_covers_img FS_RLO (FS_RHI - FS_RLO) a fe8_relro). lia. }
assert (Hnp : ~ inFP FS_PSTAT_FP a).
{ intros Hp. pose proof (pstat_bounds a Hp) as Hb.
  destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  pose proof (proj1 (forallb_forall _ _) fe8_ro_segs sg Hin) as Hs. cbv beta in Hs. rewrite Hw in Hs. cbn [orb] in Hs.
  apply Z.leb_le in Hs. lia. }
pose proof (fs_segs_low a Hi) as Hlow.
rewrite <- (fe8_aview_unp lyc Sc U W mem mdc a HARU) by (unfold kLowMemEnd, SHADOW_OFF in *; lia).
rewrite (F3 a Hi Ho He Hnp (fp_spares_closed FS_PSTAT_FP a fe8_pstat_closed)).
exact (Hro a Ha Ho He).
Qed.

(* the facts of a read-only canonical state: the saved words, the flag word, the frame chunks *)
Lemma fe8_ro_read : forall cx E ss (W : world tfibsegs) ms cs ly S U md,
  fe_base B cx -> st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_mem ss = fe8_ro_regions cs ->
  fe_E cx E -> fe_regs_core cx E ->
  ARU tfibsegs B ly S U W (ms_mem ms) md -> In (0, c_fpos cx) (frames S) -> ly_F ly = ly_F (c_ly cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_sp0 cx)) fe_sv_chunks /\
  rdword (aview tfibsegs (w_H W) (ms_mem ms)) (fe_F cx + 56) = Some (fe_FL cx) /\
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) (fe_F cx)) cs.
Proof.
intros cx E ss W ms cs ly S U md Hbase HS Hm HE Hcore HARU Hin ELY.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & _).
pose proof (ARU_AR tfibsegs B ly S U W (ms_mem ms) md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W _ md 0 (c_fpos cx) HAR Hin) as (Hf0 & Hfc & _).
destruct (al_flag _ _ LAWS ly S W _ md 0 (c_fpos cx) HAR Hin) as (_ & _ & Hflapp & Hflc).
assert (EF : frame_addr ly 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (EFL : flag_addr ly 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
rewrite EF in Hf0, Hfc. rewrite EFL in Hflapp, Hflc. change (fs_frame_bytes 0) with 64 in Hfc.
unfold in_app in Hflapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcore as (H8 & H9 & H2 & H18 & H24 & H25 & _).
pose proof (fsw_region_nth E ss _ 0 _ HS ltac:(rewrite Hm; reflexivity)) as R0.
pose proof (fsw_region_nth E ss _ 1 _ HS ltac:(rewrite Hm; reflexivity)) as R1.
cbn [ms_mem restrict] in R0, R1.
destruct R0 as (_ & _ & _ & Hc0). destruct R1 as (_ & _ & _ & Hc1).
cbn [YP09.r_chunks YP09.r_base base_val] in Hc0, Hc1.
rewrite H24, unsigned_lit_small in Hc0 by (unfold LLVMF_STK in *; lia).
rewrite H8, unsigned_lit_small in Hc1 by (unfold LLVMF_STK in *; lia).
inversion Hc0 as [|c0 l0 Hfl Hcs]; subst.
split; [exact Hc1|]. split; [|exact Hcs].
pose proof (val_of_chunk_ok tfibsegs E _ (fe_F cx) 56 8 (SOff 44 0) (fe_FL cx) Hfl) as Hv.
apply ACem.rdword_of_val_mem; [|lia]. apply Hv; [|cbn; lia|cbn; lia].
rewrite fsw_SOff0. change 44%nat with (32 + 12)%nat. rewrite (HE 12%nat ltac:(lia)). reflexivity.
Qed.

(* the canonical state after a call (fe_canon), from the call-site state's saved words and the callee's keeps *)
Lemma fe8_rebuild : forall cx E (W : world tfibsegs) mem ly' S' U' (W' : world tfibsegs) mem' md' regs' xs r,
  fe_base B cx -> fe_E cx E -> fe_regs_core cx (Ereg regs' (fe_extra cx ++ xs)) ->
  ARU tfibsegs B ly' S' U' W' mem' md' -> In (0, c_fpos cx) (frames S') -> ly_F ly' = ly_F (c_ly cx) ->
  (forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx -> apresent (w_H W') mem' a) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) (fe_sp0 cx)) fe_sv_chunks ->
  (forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  rdword (aview tfibsegs (w_H W') mem') (fe_F cx + 56) = Some (fe_FL cx) ->
  st_ok tfibsegs (Ereg regs' (fe_extra cx ++ xs)) (fe_ss r [])
    (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 r) mem' (YK11.seg_rom tfibsegs))).
Proof.
intros cx E W mem ly' S' U' W' mem' md' regs' xs r Hbase HE Hcore' HARU' Hfin ELY Hpres Hsv Hav Hflag.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcore' as (H8 & H9 & H2 & H18 & H24 & H25 & _).
rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 8 8%bv eq_refl) in H8.
rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 24 24%bv eq_refl) in H24.
rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 18 18%bv eq_refl) in H18.
rewrite (ew_Ereg_nat regs' (fe_extra cx ++ xs) 25 25%bv eq_refl) in H25.
apply (fe_canon B cx ly' S' U' W' mem' md' regs' xs r []); try assumption.
- unfold LLVMF_STK in N2. lia.
- apply (fe8_sv_move cx E _ (mrestrict (w_H W) mem)); [exact HE | apply fe_E_Ereg | | exact Hsv].
  intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- exact fe_regions_wf_nil.
- constructor.
- constructor.
Qed.

(* fuzz/alloc.c's statics across a callee journal that does not write them *)
Lemma fe8_glob_keep : forall STK1 sp1 FP1 lyc Sc (W : world tfibsegs) mem mdc nf ly' S' W' mem' md' k1 live peak cnt fail,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W mem mdc nf ly' S' W' mem' md' k1 ->
  ~ YI16.sink_open_fp FP1 -> (forall a, inFP FS_PSTAT_FP a -> ~ inFP FP1 a) ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros STK1 sp1 FP1 lyc Sc W mem mdc nf ly' S' W' mem' md' k1 live peak cnt fail HJc Hcl Hnf (G1 & G2 & G3 & G4 & R).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv q Hq. rewrite <- (Hv q Hq). apply (mbyte_of_aview tfibsegs).
  assert (Hp : inFP FS_PSTAT_FP (g + Z.of_nat q)) by (apply (inFP_FS_PSTAT_FP g Hg); lia).
  apply F3; [exact (fe8_pstat_img _ Hp) | exact (proj1 (proj1 IMG _ Hp))
    | exact (proj2 (proj1 IMG _ Hp)) | exact (Hnf _ Hp) | exact (fp_spares_closed FP1 _ Hcl)]. }
unfold fs_glob, fs_glob_at.
split; [apply VK; [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto | exact G1]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto | exact G2]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto | exact G3]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto | exact G4]|].
exact R.
Qed.

(* the payload: an entry block (or empty), kept by the walk's block clause while the entry's blocks are live *)
Lemma fe8_payload : forall cx own ly' S' (W' : world tfibsegs) mem' md' k,
  fe_base B cx ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly' S' W' mem' md' k ->
  (forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly' S')) ->
  forall i, 0 <= i < c_n cx ->
    aview tfibsegs (w_H W') mem' (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i).
Proof.
intros cx own ly' S' W' mem' md' k Hbase HJ Hsub i Hi.
pose proof Hbase as (HPRE & _). pose proof HPRE as (Hafn & _ & _ & _ & Hpn & _).
pose proof Hafn as (HAR0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct Hpn as [(Hn0 & _) | (Hn & Hin)]; [lia|].
pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq).
apply (F2 (c_p cx) (c_n cx) i Hin (Hsub _ Hin) ltac:(lia)).
intros Hp. apply (blk_img tfibsegs B LAWS _ _ _ _ _ (c_p cx) (c_n cx) (c_p cx + i) HAR0 Hin ltac:(lia)).
exact (fe8_pstat_img _ Hp).
Qed.

(* ---- the boundary after fuzz_free returns (0x81108): the text is the only block of the walk, U = [] ---- *)
Definition KB7 : Z := EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written + EV_check_round_trip.
Definition INV8_F : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text cnt,
  U3 = [] /\ Permutation (ablocks B ly3 S3) ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  0 <= k <= KB7 + 1 /\ fe_regs_core cx E /\ ew E 21 = Z_to_bv 64 text /\
  fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) cnt /\ c_cnt cx <= cnt <= c_cnt cx + FE_CNT_MAX.


(* ---- free(text) at 0x8110c (ra 0x81110 = PC_epi): __wrap_free 0x53070 = pc_wrap_free (as_code B), the S-form route at
   U = []: FsEntryRt's fe_free -> FSupoisonU.afree_realizes_of_U -> YCbp.afree04_rule_triv -> YC85.afree04_sub
   (donor ACfd.v:149-171, ACfi.v:128) ---- *)
Lemma fe8_free : forall POST, fe_from B FS_PSTAT_FP POST (fe_ss PC_epi []) (INV_C9 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_fuzz_free []) INV8_F.
Proof.
intros POST HNEXT cx E k ly3 S3 U3 W3 ms3 md3 Hbase HE HJ HARU HINV HS.
destruct HINV as (text & cnt & -> & HPerm & Hk & Hcore & E21 & Hstat & Hcnt).
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof Hbase as (HPRE & Hstat0 & Hc0 & Hcmax & Hlive0).
pose proof HPRE as (Hafn0 & Hra0 & Hp0 & Hn0 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hbb0 & Hro0 & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & Hio3 & Hfrs3 & Hnev3 & Hk3 & _).
assert (ELY3 : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Hfin3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY3; reflexivity).
assert (Htxt3 : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity]).
assert (Htxt0 : ~ In (text, fe_n cx + 1) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hx. exact (fe8_perm_twice ly3 S3 W3 _ md3 [(text, fe_n cx + 1)] (ablocks B (c_ly cx) (c_S cx))
    (text, fe_n cx + 1) HAR3 HPerm ltac:(left; reflexivity) Hx). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ text (fe_n cx + 1) HAR3 Htxt3) as (_ & Ht4096 & Htceil & _).
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ md3 text (fe_n cx + 1) 0 (c_fpos cx) HAR3 Htxt3 Hfin3) as HdTF.
unfold zdisjoint in HdTF; cbn [fst snd] in HdTF; change (fs_frame_bytes 0) with 64 in HdTF; rewrite EF3 in HdTF.
(* read-only state, then the run to __wrap_free *)
assert (HS0 : st_ok tfibsegs E (mkSS RA_fuzz_free sr_atoms (fe8_ro_regions []) None (ss_facts (fe_ss RA_fuzz_free [])))
  (restrict (w_H W3) ms3))
  by exact (st_ok_submem tfibsegs E (fe_ss RA_fuzz_free []) _ (fe8_ro_regions []) HS (fe8_ro_sub []) eq_refl).
clear HS.
fsw_aj_runU entry_tbl_ok HS0 HJ HARU.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with HF0 : frame_of _ _ (ms_mem ms3) (ms_mem ?m) |- _ => rename m into msR; rename HF0 into HFR end.
assert (Hmem : forall x, ms_mem msR x = ms_mem ms3 x) by (apply (frame_of_ro E (fe8_ro_regions [])); [reflexivity | exact HFR]).
assert (Hsb : same_below (ms_mem ms3) (ms_mem msR) alloc_ceiling) by (intros x _; apply Hmem).
destruct (fe8_ro_read cx E _ W3 msR [] ly3 S3 [] _ Hbase HS0 eq_refl HE Hcore HARU Hfin3 ELY3) as (Hsv & Hflag & _).
pose proof (fe8_reg _ _ _ _ 10%bv 21 HS0 eq_refl) as R10.
pose proof (fsw_reg_lit _ _ _ _ 1%bv 528656 HS0 eq_refl ltac:(lia)) as R1.
pose proof (fe8_reg _ _ _ _ 2%bv 2 HS0 eq_refl) as R2.
pose proof (fe8_reg _ _ _ _ 3%bv 3 HS0 eq_refl) as R3.
pose proof (fe8_reg _ _ _ _ 4%bv 4 HS0 eq_refl) as R4.
pose proof (fe8_reg _ _ _ _ 8%bv 8 HS0 eq_refl) as R8.
pose proof Hcore as (H8 & H9 & H2 & H18 & H24 & H25 & H3 & H4 & H26 & H27).
assert (Esp : spZ (ms_regs msR) = fe_sp1 cx) by (unfold spZ; rewrite R2, H2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (Es0 : s0Z (ms_regs msR) = fe_sp0 cx) by (unfold s0Z; rewrite R8, H8; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (Era : raZ (ms_regs msR) = 528656) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
pose proof (fe8_achain cx ly3 S3 [] W3 (ms_mem msR) _ k E Hbase HJ HARU HE Hsv) as Hch.
pose proof HJ as (_ & _ & _ & _ & _ & _ & HnevR & _).
set (AFREE4 := afree04_rule_triv tfibsegs B fs_segs_low errno_low LAWS ML
  (afree_realizes_of_U tfibsegs B fe_fr)).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ msR HS0 eq_refl). cbn [ss_pc].
replace 340080 with (pc_wrap_free (as_code B)) by (rewrite tl_code; reflexivity).
eapply SRr_bind.
{ eapply (afree04_sub tfibsegs B LAWS fs_segs_low ameter_triv AFREE4 W3 (ms_regs msR) (ms_mem msR) LLVMF_STK (fe_sp0 cx)
    FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(0, c_fpos cx)] ly3 S3 _ k text (fe_n cx + 1)
    (fe_sp1 cx - fe_sp0 cx) (Z_to_bv 64 528656) (fe8_ch cx) HJ Htxt3).
  - rewrite R10, E21. reflexivity.
  - rewrite Esp. lia.
  - clear - N1 N6. Z.div_mod_to_equations. lia.
  - lia.
  - rewrite Has. unfold LLVMF_STK. lia.
  - rewrite R3, H3. pose proof Hafn0 as (_ & _ & _ & Hgp & _). exact Hgp.
  - rewrite R4, H4. pose proof Hafn0 as (_ & _ & _ & _ & Htp & _). exact Htp.
  - exact R1.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold KB7, EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip, EV_LIB, EV_MAX in *.
    lia.
  - apply (achain_chain_pre ly3 _ (fe_sp1 cx) (fe_sp0 cx) (fe8_ch cx) (ms_regs msR) Hch); [|exact Es0|].
    + rewrite Esp. unfold LLVMF_STK in *. lia.
    + rewrite Era. lia.
  - intros Hx. exfalso. exact (Htxt0 Hx).
  - exact I. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & _ & HJS4).
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & Hio4 & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
assert (ELY4 : ly_F ly4 = ly_F (c_ly cx)) by (destruct Hly4 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B (c_ly cx) (c_S cx))).
{ rewrite Ebl4. apply (@Permutation_app_inv _ l1 l2 [] _ (text, fe_n cx + 1)). cbn [app]. rewrite <- Ebl3. exact HPerm. }
assert (Hcore4 : fe_regs_core cx (Ereg regs4 (fe_extra cx ++ []))).
{ apply (fe8_core_after cx E _ (w_H W3) msR regs4 [] Hcore HS0); [|exact HP4]. repeat split; reflexivity. }
destruct HK as (K1 & _ & _ & K4 & _).
apply (HNEXT cx (Ereg regs4 (fe_extra cx ++ [])) (k + 1) ly4 S4 [] W4
  (YK11.mkst regs4 (Z_to_bv 64 528656) mem4 (YK11.seg_rom tfibsegs)) md4 Hbase (fe_E_Ereg cx regs4 [])).
- exact HJ4.
- apply (proj2 (ARU_nil tfibsegs B ly4 S4 W4 mem4 md4)). exact HAR4.
- (* INV_C9 *)
  split; [reflexivity|]. split; [exact HPerm4|]. split; [|split; [exact Hcore4|]].
  + split; [unfold KB7 in Hk; unfold EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip in *; lia|].
    split; [exact (aos_step_closed_same_io FS_PSTAT_FP _ _ fe8_pstat_closed Hio4)|].
    split.
    * apply (fe8_payload cx _ ly4 S4 W4 mem4 md4 (k + 1) Hbase HJ4).
      intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | exact Hb].
    * rewrite (blocks_bytes_bsum B ly4 S4), (blocks_bytes_bsum B (c_ly cx) (c_S cx)), (bsum_perm _ _ HPerm4). lia.
  + exists cnt. split; [|exact Hcnt].
    destruct Hstat as (peak & Hg). exists peak.
    apply (fe8_glob_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS4).
    * apply sink_closed_ablocks_fp. constructor; [cbn; lia | constructor].
    * intros a Ha Hb. destruct (inFP_ablocks_fp_inv _ a Hb) as (p' & n' & [Hpn' | []] & Hr).
      injection Hpn' as <- <-.
      exact (blk_img tfibsegs B LAWS _ _ _ _ _ text (fe_n cx + 1) a HAR3 Htxt3 Hr (fe8_pstat_img _ Ha)).
    * exact (fs_glob_below W3 _ _ _ _ _ _ Hsb Hg).
- (* the canonical state at PC_epi *)
  apply (fe8_rebuild cx E W3 (ms_mem msR) ly4 S4 [] W4 mem4 md4 regs4 [] PC_epi Hbase HE Hcore4).
  + apply (proj2 (ARU_nil tfibsegs B ly4 S4 W4 mem4 md4)). exact HAR4.
  + rewrite Hfrs4. exact Hfin3.
  + exact ELY4.
  + intros a Ha. apply Hpres4. unfold LLVMF_STK. lia.
  + exact Hsv.
  + intros a Ha. apply K1; [unfold LLVMF_STK in *; lia | lia].
  + rewrite (rdword_ext (aview tfibsegs (w_H W3) (ms_mem msR)) (aview tfibsegs (w_H W4) mem4)); [exact Hflag|].
    intros q Hq. apply (K4 0 (c_fpos cx)); [exact Hfin3 | left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EF3;
      change (fs_frame_bytes 0) with 64; lia | lia].
Qed.


(* ---- a program call from a read-only canonical call-site state: the callee's fpreU (YCbq.afn_pre_at over the walk's
   journal, ARU's U facts, the journal's arodata) and the composition on return (FSW_K3.fsw_ajournal_sub5, fe_canon) ---- *)
Lemma fe8_fpre : forall cx E lyc Sc U (W : world tfibsegs) msR mdc k ssR cs STK1 ra,
  fe_base B cx -> fe_E cx E -> fe_regs_core cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison U (ms_mem msR)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem msR) mdc ->
  st_ok tfibsegs E ssR (restrict (w_H W) msR) -> ss_mem ssR = fe8_ro_regions cs ->
  sr_get (ss_regs ssR) 2%bv = SOff 2 0 -> sr_get (ss_regs ssR) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssR) 4%bv = SOff 4 0 -> sr_get (ss_regs ssR) 8%bv = SOff 8 0 ->
  sr_get (ss_regs ssR) 1%bv = SLit ra -> 4096 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  0 <= STK1 <= 32000 ->
  fpreU tfibsegs B STK1 lyc Sc U W (ms_regs msR) (ms_mem msR) mdc (fe8_ch cx) /\ raZ (ms_regs msR) = ra /\
  spZ (ms_regs msR) = fe_sp1 cx.
Proof.
intros cx E lyc Sc U W msR mdc k ssR cs STK1 ra Hbase HE Hcore HJ HARU HS Hm S2 S3 S4 S8 S1 Hra Hra2 HSTK.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hbase as (HPRE & _). pose proof HPRE as (Hafn0 & _).
pose proof Hafn0 as (_ & _ & _ & Hgp & Htp & _).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (ELY : ly_F lyc = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Hfin : In (0, c_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (fe8_ro_read cx E ssR W msR cs lyc Sc U mdc Hbase HS Hm HE Hcore HARU Hfin ELY) as (Hsv & _).
pose proof Hcore as (H8 & H9 & H2 & H18 & H24 & H25 & H3 & H4 & _).
assert (Esp : spZ (ms_regs msR) = fe_sp1 cx)
  by (unfold spZ; rewrite (fe8_reg _ _ _ _ 2%bv 2 HS S2), H2; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (Es0 : s0Z (ms_regs msR) = fe_sp0 cx)
  by (unfold s0Z; rewrite (fe8_reg _ _ _ _ 8%bv 8 HS S8), H8; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
pose proof (fsw_reg_lit _ _ _ _ 1%bv ra HS S1 ltac:(lia)) as R1.
assert (Era : raZ (ms_regs msR) = ra) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
pose proof (fe8_achain cx lyc Sc U W (ms_mem msR) mdc k E Hbase HJ HARU HE Hsv) as Hch.
split; [|split; [exact Era | exact Esp]].
split; [|exact (fe8_arodata cx lyc Sc U W (ms_mem msR) mdc _ k Hbase HJ HARU)].
split; [|destruct HARU as (_ & OK & PO); split; [exact OK | exact PO]].
apply (afn_pre_at tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(0, c_fpos cx)] lyc Sc W (unpoison U (ms_mem msR)) mdc k (ms_regs msR) STK1 (fe_sp1 cx - fe_sp0 cx) (fe8_ch cx) HJ).
- rewrite Esp. lia.
- clear - N1 N6. Z.div_mod_to_equations. lia.
- lia.
- lia.
- unfold LLVMF_STK. lia.
- rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. exact Hra2.
- rewrite Era. lia.
- rewrite (fe8_reg _ _ _ _ 3%bv 3 HS S3), H3. exact Hgp.
- rewrite (fe8_reg _ _ _ _ 4%bv 4 HS S4), H4. exact Htp.
- rewrite Esp, Es0. exact Hch.
Qed.

Lemma fe8_after_pcall : forall cx E lyc Sc Uc (W : world tfibsegs) msR mdc k ssR cs
    STK1 FP1 ly' S' U' (W' : world tfibsegs) mem' md' k1 regs' r,
  fe_base B cx -> fe_E cx E -> fe_regs_core cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc (ms_mem msR)) mdc k ->
  ARU tfibsegs B lyc Sc Uc W (ms_mem msR) mdc ->
  st_ok tfibsegs E ssR (restrict (w_H W) msR) -> ss_mem ssR = fe8_ro_regions cs ->
  sr_get (ss_regs ssR) 2%bv = SOff 2 0 /\ sr_get (ss_regs ssR) 3%bv = SOff 3 0 /\ sr_get (ss_regs ssR) 4%bv = SOff 4 0 /\
  sr_get (ss_regs ssR) 8%bv = SOff 8 0 /\ sr_get (ss_regs ssR) 9%bv = SOff 9 0 /\ sr_get (ss_regs ssR) 18%bv = SOff 18 0 /\
  sr_get (ss_regs ssR) 24%bv = SOff 24 0 /\ sr_get (ss_regs ssR) 25%bv = SOff 25 0 /\
  sr_get (ss_regs ssR) 26%bv = SOff 26 0 /\ sr_get (ss_regs ssR) 27%bv = SOff 27 0 ->
  ajournal tfibsegs B STK1 (fe_sp1 cx) FP1 lyc Sc W (unpoison Uc (ms_mem msR)) mdc [] ly' S' W' (unpoison U' mem') md' k1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved (ms_regs msR) regs' ->
  0 <= STK1 <= 32000 ->
  fsw_fp_sub B (c_ly cx) (c_S cx) lyc Sc [(0, c_fpos cx)] FS_PSTAT_FP FP1 ->
  (forall a, fe_F cx <= a < fe_F cx + 64 -> ~ inFP FP1 a) ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly' S' W' (unpoison U' mem') md' (k + k1) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  fe_regs_core cx (Ereg regs' (fe_extra cx ++ [])) /\
  st_ok tfibsegs (Ereg regs' (fe_extra cx ++ [])) (fe_ss r [])
    (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 r) mem' (YK11.seg_rom tfibsegs))).
Proof.
intros cx E lyc Sc Uc W msR mdc k ssR cs STK1 FP1 ly' S' U' W' mem' md' k1 regs' r
  Hbase HE Hcore HJ HARU HS Hm Hregs HJc OK' PO' HP HSTK HF HnF.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
assert (ELY : ly_F lyc = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Hfin : In (0, c_fpos cx) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr lyc 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
destruct (fe8_ro_read cx E ssR W msR cs lyc Sc Uc mdc Hbase HS Hm HE Hcore HARU Hfin ELY) as (Hsv & Hflag & _).
assert (HJ4 : ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly' S' W' (unpoison U' mem') md' (k + k1)).
{ exact (fsw_ajournal_sub5 B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] lyc Sc W (unpoison Uc (ms_mem msR)) mdc k STK1 (fe_sp1 cx) FP1 [] ly' S' W' (unpoison U' mem') md' k1
    HJ HJc ltac:(unfold LLVMF_STK; lia) ltac:(lia) HF). }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ4) | split; [exact OK' | exact PO']]).
assert (Hcore' : fe_regs_core cx (Ereg regs' (fe_extra cx ++ [])))
  by exact (fe8_core_after cx E ssR (w_H W) msR regs' [] Hcore HS Hregs HP).
pose proof HJ4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
destruct (al_frames _ _ LAWS lyc Sc W _ mdc 0 (c_fpos cx) HARc Hfin) as (_ & Happ & _).
rewrite EF in Happ. change (fs_frame_bytes 0) with 64 in Happ.
split; [exact HJ4|]. split; [exact HARU'|]. split; [exact Hcore'|].
apply (fe8_rebuild cx E W (ms_mem msR) ly' S' U' W' mem' md' regs' [] r Hbase HE Hcore' HARU').
- rewrite Hfrs4. left. reflexivity.
- destruct Hly4 as (_ & _ & _ & _ & _ & EF4 & _). exact EF4.
- intros a Ha. apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' a HARU'); [unfold LLVMF_STK in *; fe8_lia|].
  apply Hpres4. unfold LLVMF_STK in *. fe8_lia.
- exact Hsv.
- intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU') by (unfold LLVMF_STK in *; fe8_lia).
  rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W (ms_mem msR) mdc a HARU) by (unfold LLVMF_STK in *; fe8_lia).
  apply G1; unfold LLVMF_STK in *; fe8_lia.
- rewrite (rdword_ext (aview tfibsegs (w_H W) (ms_mem msR)) (aview tfibsegs (w_H W') mem')); [exact Hflag|].
  intros q Hq.
  pose proof (in_app_addr (fe_F cx) 64 (fe_F cx + 56 + q) Happ ltac:(fe8_lia)) as Ha. unfold app_addr, ASAN_CEIL in Ha.
  rewrite <- (fe8_aview_unp ly' S' U' W' mem' md' _ HARU') by (unfold kLowShadowBeg, SHADOW_OFF in *; fe8_lia).
  rewrite <- (fe8_aview_unp lyc Sc Uc W (ms_mem msR) mdc _ HARU) by (unfold kLowShadowBeg, SHADOW_OFF in *; fe8_lia).
  apply (G4 0 (c_fpos cx) _ Hfin).
  + left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. fe8_lia.
  + apply HnF. fe8_lia.
Qed.


(* ---- the boundary after check_reject_clean_starved returns (0x81100): the body (if any) and the text are the walk's
   blocks, U = the body's head, the body a reader block of dec_size bytes ---- *)
Definition INV8_S : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body cnt,
  U3 = fe_body_U body /\
  Permutation (ablocks B ly3 S3) (fe_body_blocks cx body ++ (text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  (body <> 0 -> fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) body (dec_size (fe_tb cx))) /\
  0 <= k <= KB7 /\ fe_regs_core cx E /\ ew E 21 = Z_to_bv 64 text /\ ew E 22 = Z_to_bv 64 body /\
  fs_stat tfibsegs W3 (ms_mem ms3) (fe_live6 cx body) cnt /\ c_cnt cx <= cnt <= c_cnt cx + FE_CNT_MAX.

(* ---- fuzz_free(body) at 0x81104 (ra 0x81108): FsEntryFns' en_free; on return the body's block and
   its head are gone (U = []) and g_live is back at the entry's ---- *)
Lemma fe8_ff : forall POST, fe_from B FS_PSTAT_FP POST (fe_ss RA_fuzz_free []) INV8_F ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_starved []) INV8_S.
Proof.
intros POST HNEXT cx E k ly3 S3 U3 W3 ms3 md3 Hbase HE HJ HARU HINV HS.
destruct HINV as (text & body & cnt & EU & HPerm & Hrb & Hk & Hcore & E21 & E22 & Hstat & Hcnt). subst U3.
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hbase as (HPRE & Hstat0 & Hc0 & Hcmax & Hlive0).
pose proof HPRE as (Hafn0 & Hra0 & Hp0 & Hn0 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hbb0 & Hro0 & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & Hio3 & Hfrs3 & Hnev3 & Hk3 & _).
assert (ELY3 : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Hfin3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY3; reflexivity).
assert (Hdec : 3 <= dec_size (fe_tb cx)) by (unfold dec_size; pose proof (Z.div_pos (Z.of_nat (length (fe_tb cx))) 4); lia).
assert (Hlive00 : 0 <= c_live cx) by (destruct Hstat0 as (pk & (_ & _ & _ & _ & R0 & _)); lia).
assert (HBB : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3) /\
   ~ In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hb. unfold fe_body_blocks in HPerm. rewrite (proj2 (Z.eqb_neq body 0) Hb) in HPerm. split.
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity].
  - intros Hx. exact (fe8_perm_twice ly3 S3 W3 _ md3 [(body - HEAD, dec_size (fe_tb cx) + HEAD); (text, fe_n cx + 1)]
      (ablocks B (c_ly cx) (c_S cx)) _ HAR3 HPerm ltac:(left; reflexivity) Hx). }
(* read-only state, then the run to fuzz_free *)
assert (HS0 : st_ok tfibsegs E (mkSS RA_starved sr_atoms (fe8_ro_regions []) None (ss_facts (fe_ss RA_starved [])))
  (restrict (w_H W3) ms3))
  by exact (st_ok_submem tfibsegs E (fe_ss RA_starved []) _ (fe8_ro_regions []) HS (fe8_ro_sub []) eq_refl).
clear HS.
fsw_aj_runU entry_tbl_ok HS0 HJ HARU.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with HF0 : frame_of _ _ (ms_mem ms3) (ms_mem ?m) |- _ => rename m into msR; rename HF0 into HFR end.
assert (Hmem : forall x, ms_mem msR x = ms_mem ms3 x) by (apply (frame_of_ro E (fe8_ro_regions [])); [reflexivity | exact HFR]).
assert (Hsb : same_below (ms_mem ms3) (ms_mem msR) alloc_ceiling) by (intros x _; apply Hmem).
pose proof (fe8_reg _ _ _ _ 10%bv 22 HS0 eq_refl) as R10.
pose proof (fsw_reg_lit _ _ _ _ 1%bv 528648 HS0 eq_refl ltac:(lia)) as R1.
destruct (fe8_fpre cx E ly3 S3 (fe_body_U body) W3 msR _ k _ [] STK_fuzz_free 528648 Hbase HE Hcore HJ HARU HS0 eq_refl
  eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) eq_refl ltac:(unfold STK_fuzz_free; vm_compute; split; discriminate))
  as (HFP & Era & Esp).
destruct Hstat as (peak & Hg).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ msR HS0 eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (en_free ly3 S3 (fe_body_U body) W3 (ms_regs msR) (ms_mem msR) _ (fe8_ch cx) body (dec_size (fe_tb cx))
    (fe_live6 cx body) peak cnt SIZE_MAXZ).
  - rewrite R10, E22. reflexivity.
  - exact (fs_glob_below W3 _ _ _ _ _ _ Hsb Hg).
  - intros rr Hrr. unfold fe_body_U in Hrr. destruct (Z.eqb_spec body 0) as [Hb0 | Hb0]; [destruct Hrr|].
    destruct Hrr as [<- | []]. split; [reflexivity|]. exists (dec_size (fe_tb cx) + HEAD).
    split; [exact (proj1 (HBB Hb0))|]. pose proof (req_size_pos (dec_size (fe_tb cx) + HEAD) ltac:(unfold HEAD; lia)).
    unfold HEAD in *. lia.
  - destruct (Z.eqb_spec body 0) as [Hb0 | Hb0]; [left; split; [exact Hb0 | exact HFP] | right; split; [exact Hb0|]].
    exists [], []. split; [unfold fe_body_U; rewrite (proj2 (Z.eqb_neq body 0) Hb0); reflexivity|].
    split; [exact HFP|]. split.
    + exact (fs_rblock_below B ly3 S3 W3 _ md3 _ _ body _ HAR3 Hsb (Hrb Hb0)).
    + unfold fe_live6. rewrite (proj2 (Z.eqb_neq body 0) Hb0). lia.
  - unfold KB7, EV_check_no_overread, EV_preset_base64_decode, EV_check_as_written, EV_check_round_trip, EV_LIB, EV_MAX in *.
    lia. }
cbv beta. intros W4 c4 Hwle4 [(Hb0 & Hpost) | (Hb0 & U1 & U2 & EU12 & Hpost)].
- (* body = 0: nothing freed *)
  subst body.
  destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Ebl4 & _ & Hg4)).
  rewrite Esp in HJc. rewrite R1.
  destruct (fe8_after_pcall cx E ly3 S3 (fe_body_U 0) W3 msR _ k _ [] STK_fuzz_free [] ly4 S4 (fe_body_U 0) W4 mem4 md4 0
    regs4 RA_fuzz_free Hbase HE Hcore HJ HARU HS0 eq_refl ltac:(repeat split; reflexivity) HJc OK4 PO4 HP4
    ltac:(unfold STK_fuzz_free; vm_compute; split; discriminate)
    ltac:(intros a (rr & [] & _)) ltac:(intros a _ (rr & [] & _)))
    as (HJ4 & HARU4 & Hcore4 & HS4).
  apply (HNEXT cx (Ereg regs4 (fe_extra cx ++ [])) (k + 0) ly4 S4 (fe_body_U 0) W4
    (YK11.mkst regs4 (Z_to_bv 64 528648) mem4 (YK11.seg_rom tfibsegs)) md4 Hbase (fe_E_Ereg cx regs4 []) HJ4 HARU4);
    [|exact HS4].
  exists text, cnt. split; [reflexivity|]. split; [rewrite Ebl4; exact HPerm|].
  split; [unfold KB7 in *; lia|]. split; [exact Hcore4|].
  split; [rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl), (fe8_kept _ _ _ msR regs4 21%bv 21 HS0 eq_refl HP4 ltac:(fe8_cs));
    exact E21|].
  split; [|exact Hcnt]. exists peak. unfold fe_live6 in Hg4. cbn [Z.eqb] in Hg4. rewrite Z.add_0_r in Hg4. exact Hg4.
- (* body <> 0: its block and head are released *)
  assert (EUb : fe_body_U body = [(body - HEAD, HEAD)]) by (unfold fe_body_U; rewrite (proj2 (Z.eqb_neq body 0) Hb0); reflexivity).
  rewrite EUb in EU12.
  assert (EU0 : U1 = [] /\ U2 = []).
  { destruct U1 as [|x U1]; cbn in EU12.
    - injection EU12 as EU2. split; [reflexivity | symmetry; exact EU2].
    - injection EU12 as _ EU1. destruct U1; discriminate EU1. }
  destruct EU0 as (-> & ->).
  destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & ((l1 & l2 & Ebl3 & Ebl4) & _ & Hg4)).
  rewrite Esp in HJc. rewrite R1.
  destruct (HBB Hb0) as (Hbb3 & HbbE).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbb3) as (_ & Hb4096 & _).
  pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ md3 _ _ 0 (c_fpos cx) HAR3 Hbb3 Hfin3) as HdBF.
  unfold zdisjoint in HdBF; cbn [fst snd] in HdBF; change (fs_frame_bytes 0) with 64 in HdBF; rewrite EF3 in HdBF.
  destruct (fe8_after_pcall cx E ly3 S3 (fe_body_U body) W3 msR _ k _ [] STK_fuzz_free
    (FS_PSTAT_FP ++ ablocks_fp [(body - HEAD, dec_size (fe_tb cx) + HEAD)]) ly4 S4 ([] ++ []) W4 mem4 md4 1
    regs4 RA_fuzz_free Hbase HE Hcore HJ HARU HS0 eq_refl ltac:(repeat split; reflexivity) HJc OK4 PO4 HP4
    ltac:(unfold STK_fuzz_free; vm_compute; split; discriminate)) as (HJ4 & HARU4 & Hcore4 & HS4).
  + intros a (rr & Hrr & Hra). apply in_app_iff in Hrr as [Hrr | Hrr].
    * right. right. left. split; [exists rr; split; [exact Hrr | exact Hra]|]. apply fe8_pstat_img. exists rr. auto.
    * right. left. destruct (inFP_ablocks_fp_inv _ a (ex_intro _ rr (conj Hrr Hra))) as (p' & n' & [Hpn' | []] & Hr).
      injection Hpn' as <- <-. exists (body - HEAD), (dec_size (fe_tb cx) + HEAD). auto.
  + intros a Ha (rr & Hrr & Hra). apply in_app_iff in Hrr as [Hrr | Hrr].
    * apply (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 0 (c_fpos cx) a HAR3 Hfin3).
      { rewrite EF3. change (fs_frame_bytes 0) with 64. lia. }
      apply fe8_pstat_img. exists rr. auto.
    * destruct (inFP_ablocks_fp_inv _ a (ex_intro _ rr (conj Hrr Hra))) as (p' & n' & [Hpn' | []] & Hr).
      injection Hpn' as <- <-. lia.
  + apply (HNEXT cx (Ereg regs4 (fe_extra cx ++ [])) (k + 1) ly4 S4 [] W4
      (YK11.mkst regs4 (Z_to_bv 64 528648) mem4 (YK11.seg_rom tfibsegs)) md4 Hbase (fe_E_Ereg cx regs4 []) HJ4 HARU4);
      [|exact HS4].
    exists text, cnt. split; [reflexivity|].
    split.
    { rewrite Ebl4. apply (@Permutation_app_inv _ l1 l2 [] _ (body - HEAD, dec_size (fe_tb cx) + HEAD)). cbn [app].
      rewrite <- Ebl3. unfold fe_body_blocks in HPerm. rewrite (proj2 (Z.eqb_neq body 0) Hb0) in HPerm. exact HPerm. }
    split; [unfold KB7 in *; lia|]. split; [exact Hcore4|].
    split; [rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl), (fe8_kept _ _ _ msR regs4 21%bv 21 HS0 eq_refl HP4 ltac:(fe8_cs));
      exact E21|].
    split; [|exact Hcnt]. exists peak. unfold fe_live6 in Hg4. rewrite (proj2 (Z.eqb_neq body 0) Hb0) in Hg4.
    replace (c_live cx + dec_size (fe_tb cx) - dec_size (fe_tb cx)) with (c_live cx) in Hg4 by lia. exact Hg4.
Qed.


(* ---- the data premises of the starved check across a read-only run and across the check ---- *)
Lemma fe8_src_rd_below : forall (W : world tfibsegs) m m' p l,
  same_below m m' alloc_ceiling -> src_rd tfibsegs W m p l -> src_rd tfibsegs W m' p l.
Proof.
intros W m m' p l Hs (Hg & H4096 & Hcl & Ham & Hra & Hhv).
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; exact (aview_below (w_H W) m m' alloc_ceiling a Hs Ha)).
split; [|split; [exact H4096|]; split; [exact Hcl|]; split; [exact Ham|]; split].
- unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ p l Hg). intros a Ha.
  apply (mbyte_below _ m m' alloc_ceiling a Hs). lia.
- intros x Hx. destruct (Hra x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
  rewrite AV; [exact Hs1|]. unfold shadow_of_addr, SHADOW_OFF. lia.
- intros Hlt s Hsr. rewrite AV; [exact (Hhv Hlt s Hsr)|]. unfold shadow_addr, SHADOW_OFF in Hsr. lia.
Qed.
Lemma fe8_caw_below : forall ly S U (W : world tfibsegs) mx md m m' tb bd l,
  AR tfibsegs B ly S W mx md -> same_below m m' alloc_ceiling ->
  caw_answerA tfibsegs B ly S U W m tb bd l -> caw_answerA tfibsegs B ly S U W m' tb bd l.
Proof.
intros ly S U W mx md m m' tb bd l HAR Hs [H | (bs & mm & Hd & Hbd & Hl & Hsrc & Hrb & Hlm & HU)]; [left; exact H|].
right. exists bs, mm. split; [exact Hd|]. split; [exact Hbd|]. split; [exact Hl|].
split; [exact (fe8_src_rd_below W m m' bd bs Hs Hsrc)|].
split; [exact (fs_rblock_below B ly S W mx md m m' bd mm HAR Hs Hrb)|]. split; [exact Hlm | exact HU].
Qed.
(* a reader block's head word across a callee journal that keeps the block and does not write its head *)
Lemma fe8_rblock_keep : forall STK1 sp1 FP1 lyc Sc U (W : world tfibsegs) mem mdc ly' S' U' W' mem' md' k1 p n,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison U mem) mdc [] ly' S' W' (unpoison U' mem') md' k1 ->
  ARU tfibsegs B lyc Sc U W mem mdc -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  In (p - HEAD, n + HEAD) (ablocks B ly' S') ->
  (forall i, 0 <= i < 8 -> ~ inFP FP1 (p - HEAD + i)) ->
  fs_rblock tfibsegs B lyc Sc W mem p n -> fs_rblock tfibsegs B ly' S' W' mem' p n.
Proof.
intros STK1 sp1 FP1 lyc Sc U W mem mdc ly' S' U' W' mem' md' k1 p n HJc HARU HARU' Hin' Hnf (Hin & Hal & Hn & Hv).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
pose proof (ARU_AR tfibsegs B lyc Sc U W mem mdc HARU) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & Happ & _).
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD in *; lia)) as (_ & Hrq).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact Hin'|]. split; [exact Hal|]. split; [exact Hn|].
intros q Hq. rewrite <- (Hv q Hq). apply (mbyte_of_aview tfibsegs).
pose proof (in_app_addr _ _ (p - HEAD + Z.of_nat q) Happ ltac:(unfold HEAD in *; lia)) as Ha.
unfold app_addr, ASAN_CEIL in Ha.
rewrite <- (fe8_aview_unp ly' S' U' W' mem' md' _ HARU') by (unfold kLowShadowBeg, SHADOW_OFF in *; lia).
rewrite <- (fe8_aview_unp lyc Sc U W mem mdc _ HARU) by (unfold kLowShadowBeg, SHADOW_OFF in *; lia).
apply (G2 (p - HEAD) (n + HEAD) (Z.of_nat q) Hin Hin'); [unfold HEAD in *; lia|]. apply Hnf. lia.
Qed.

(* the text's length and bytes *)
Lemma fe8_n_nonneg : forall cx, 0 <= c_n cx -> 0 <= fe_n cx.
Proof. intros cx H. unfold fe_n. destruct (zfind 0 (fe_bytes cx)); lia. Qed.
Lemma fe8_tb_len : forall cx, 0 <= fe_n cx -> Z.of_nat (length (fe_tb cx)) <= fe_n cx.
Proof. intros cx H. unfold fe_tb. rewrite length_firstn. lia. Qed.
Lemma fe8_tb_bytes : forall cx, Forall (fun b => 0 <= b < 256) (fe_tb cx).
Proof.
intros cx. assert (H : Forall (fun b => 0 <= b < 256) (fe_bytes cx)).
{ unfold fe_bytes. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (x & <- & _).
  pose proof (bv_unsigned_in_range 8 x) as Hq. change (bv_modulus 8) with 256 in Hq. exact Hq. }
unfold fe_tb. rewrite <- (firstn_skipn (Z.to_nat (fe_n cx)) (fe_bytes cx)) in H.
apply Forall_app in H. exact (proj1 H).
Qed.

(* ---- check_reject_clean_starved(text, body, len) at 0x810fc (ra 0x81100): `ld a2, 0(s4)` reads len (s4 = frame + 32,
   re-expressed as SOff 24 32), then FsEntryFns' en_starved; on return blocks and heads are as
   before and g_count grew by 1 (body = 0) or 2 ---- *)
Lemma fe8_st : forall POST, fe_from B FS_PSTAT_FP POST (fe_ss RA_starved []) INV8_S ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_crc [fe_len_atom 46]) (INV_C7 B).
Proof.
intros POST HNEXT cx E k ly3 S3 U3 W3 ms3 md3 Hbase HE HJ HARU HINV HS.
destruct HINV as (text & body & l & Hdec & Hcommon & (cnt7 & Hstat & Hcnt7)).
destruct Hdec as (EU & HPerm & Hcaw & Hcore & Hn3 & E19 & E20 & E21 & E22 & E23 & E46 & Hcstr). subst U3.
destruct Hcommon as (Hk & Hio & Hpay & Hbb).
pose proof (fe8_nums cx Hbase) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hbase as (HPRE & Hstat0 & Hc0 & Hcmax & Hlive0).
pose proof HPRE as (Hafn0 & Hra0 & Hp0 & Hn0 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hbb0 & Hro0 & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & Hio3 & Hfrs3 & Hnev3 & Hk3 & _).
assert (ELY3 : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (Hfin3 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF3 : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY3; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 _ md3 0 (c_fpos cx) HAR3 Hfin3) as (Hf0 & Hfc & _).
rewrite EF3 in Hf0, Hfc. change (fs_frame_bytes 0) with 64 in Hfc.
assert (Hcn : 0 <= c_n cx) by (destruct Hpn as [(-> & _) | (Hq & _)]; lia).
pose proof (fe8_n_nonneg cx Hcn) as Hfn.
pose proof (fe8_tb_len cx Hfn) as Htbl.
assert (Hdec : 3 <= dec_size (fe_tb cx) <= 3 * 2 ^ 20) by (unfold dec_size; Z.div_mod_to_equations; lia).
assert (Hlive00 : 0 <= c_live cx) by (destruct Hstat0 as (pk & (_ & _ & _ & _ & R0 & _)); lia).
assert (Htxt3 : In (text, fe_n cx + 1) (ablocks B ly3 S3)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. left. reflexivity. }
assert (HBB : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3) /\
   (body - HEAD, dec_size (fe_tb cx) + HEAD) <> (text, fe_n cx + 1)).
{ intros Hb. unfold fe_body_blocks in HPerm. rewrite (proj2 (Z.eqb_neq body 0) Hb) in HPerm. split.
  - eapply Permutation_in; [apply Permutation_sym; exact HPerm | left; reflexivity].
  - intros Hx. exact (fe8_perm_twice ly3 S3 W3 _ md3 [(body - HEAD, dec_size (fe_tb cx) + HEAD)]
      ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) _ HAR3 HPerm ltac:(left; reflexivity)
      ltac:(rewrite Hx; left; reflexivity)). }
(* decode's block is the body's: its size is dec_size, and len is at most it *)
assert (HcawB : body <> 0 -> fs_rblock tfibsegs B ly3 S3 W3 (ms_mem ms3) body (dec_size (fe_tb cx)) /\
  0 <= l <= dec_size (fe_tb cx)).
{ intros Hb. destruct Hcaw as [(_ & Hb0 & _) | (bs & mm & _ & _ & Hl & _ & Hrb & Hlm & _)]; [exact (False_ind _ (Hb Hb0))|].
  destruct (HBB Hb) as (Hbb3 & _).
  assert (Em : mm = dec_size (fe_tb cx)).
  { destruct (Z.eq_dec mm (dec_size (fe_tb cx))) as [Em | Ne]; [exact Em|]. exfalso.
    pose proof Hrb as (Hin & _ & Hmm & _).
    assert (Hne : (body - HEAD, mm + HEAD) <> (body - HEAD, dec_size (fe_tb cx) + HEAD)) by (intros Hq; injection Hq; lia).
    pose proof (sep_blocks tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hin Hbb3 Hne) as Hd.
    pose proof (req_size_pos (mm + HEAD) ltac:(unfold HEAD; lia)).
    pose proof (req_size_pos (dec_size (fe_tb cx) + HEAD) ltac:(unfold HEAD; lia)).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  subst mm. split; [exact Hrb | lia]. }
(* the text avoids the body's head, the only range of U *)
destruct (al_blocks _ _ LAWS _ _ _ _ _ text (fe_n cx + 1) HAR3 Htxt3) as (_ & Ht4096 & _).
assert (HUd : forall rr, In rr (fe_body_U body) ->
  text + Z.of_nat (length (fe_tb cx)) + 1 <= fst rr \/ fst rr + snd rr <= text).
{ intros rr Hrr. unfold fe_body_U in Hrr. destruct (Z.eqb_spec body 0) as [Hb0 | Hb0]; [destruct Hrr|].
  destruct Hrr as [<- | []]. cbn [fst snd]. destruct (HBB Hb0) as (Hbb3 & Hne).
  pose proof (sep_blocks tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR3 Htxt3 Hbb3 (fun Hq => Hne (eq_sym Hq))) as Hd.
  pose proof (req_size_pos (fe_n cx + 1) ltac:(lia)).
  pose proof (req_size_pos (dec_size (fe_tb cx) + HEAD) ltac:(unfold HEAD; lia)).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold HEAD in *. lia. }
assert (Etop3 : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _); exact ET).
(* s4 := frame + 32, then the read-only state and the run to the check *)
pose proof Hcore as (H8 & H9 & H2 & H18 & H24 & H25 & H3 & H4 & H26 & H27).
assert (R20 : YK11.getr (ms_regs (restrict (w_H W3) ms3)) 20%bv = sv_denot E (SOff 24 32)).
{ cbn [ms_regs restrict]. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms3 20%bv HS).
  change (sr_get (ss_regs (fe_ss RA_crc [fe_len_atom 46])) 20%bv) with (SOff 20 0). rewrite fsw_SOff0, E20.
  apply bv_eq. rewrite denot_SOff, H24, (unsigned_lit_small (fe_F cx)) by lia.
  rewrite zcanon_id by (unfold M64; lia). apply unsigned_lit_small. lia. }
pose proof (st_ok_set_reg tfibsegs E (fe_ss RA_crc [fe_len_atom 46]) _ 20%bv (SOff 24 32) HS
  ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate) R20) as HS1.
pose proof (st_ok_submem tfibsegs E _ _ (fe8_ro_regions [fe_len_atom 46]) HS1 (fe8_ro_sub [fe_len_atom 46]) eq_refl) as HS0.
clear HS HS1 R20.
fsw_aj_runU entry_tbl_ok HS0 HJ HARU.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with HF0 : frame_of _ _ (ms_mem ms3) (ms_mem ?m) |- _ => rename m into msR; rename HF0 into HFR end.
assert (Hmem : forall x, ms_mem msR x = ms_mem ms3 x)
  by (apply (frame_of_ro E (fe8_ro_regions [fe_len_atom 46])); [reflexivity | exact HFR]).
assert (Hsb : same_below (ms_mem ms3) (ms_mem msR) alloc_ceiling) by (intros x _; apply Hmem).
pose proof (fe8_reg _ _ _ _ 10%bv 21 HS0 eq_refl) as R10.
pose proof (fe8_reg _ _ _ _ 11%bv 22 HS0 eq_refl) as R11.
pose proof (fe8_reg _ _ _ _ 12%bv 46 HS0 eq_refl) as R12.
pose proof (fsw_reg_lit _ _ _ _ 1%bv 528640 HS0 eq_refl ltac:(lia)) as R1.
destruct (fe8_fpre cx E ly3 S3 (fe_body_U body) W3 msR _ k _ [fe_len_atom 46] STK_check_reject_clean_starved 528640
  Hbase HE Hcore HJ HARU HS0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) eq_refl
  ltac:(unfold STK_check_reject_clean_starved; vm_compute; split; discriminate)) as (HFP & Era & Esp).
destruct Hstat as (peak & Hg).
assert (Hfrl : Z.of_nat (length (frames S3)) <= FRL_CHECK) by (rewrite Hfrs3, Hfr0; cbn; unfold FRL_CHECK; lia).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ msR HS0 eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (en_starved ly3 S3 (fe_body_U body) W3 (ms_regs msR) (ms_mem msR) _ (fe8_ch cx) text body l (fe_tb cx)
    (fe_live6 cx body) peak cnt7).
  - exact HFP.
  - intros rr Hrr. unfold fe_body_U in Hrr. destruct (Z.eqb_spec body 0) as [Hb0 | Hb0]; [destruct Hrr|].
    destruct Hrr as [<- | []]. split; [reflexivity|]. exists (dec_size (fe_tb cx) + HEAD).
    split; [exact (proj1 (HBB Hb0))|]. pose proof (req_size_pos (dec_size (fe_tb cx) + HEAD) ltac:(unfold HEAD; lia)).
    unfold HEAD in *. lia.
  - rewrite Esp, Etop3. lia.
  - exact Hfrl.
  - rewrite R10, E21. reflexivity.
  - rewrite R11, E22. reflexivity.
  - rewrite R12, E46. reflexivity.
  - exact (cstr_ok_below W3 _ _ text (fe_tb cx) Hsb Hcstr).
  - left. exists text, (fe_n cx + 1). split; [exact Htxt3|]. split; [lia|]. split; [lia|]. exact HUd.
  - exact (fe8_tb_bytes cx).
  - right. right. left. exists text, (fe_n cx + 1).
    split; [unfold HEAD; lia|]. split; [exact Htxt3|]. split; [lia|].
    rewrite length_app. cbn [length]. split; [lia|].
    intros rr Hrr. destruct (HUd rr Hrr) as [Hq | Hq]; [right | left]; lia.
  - unfold PRESET_FILE_MAX_BYTES. lia.
  - exact (fe8_caw_below ly3 S3 _ W3 _ md3 _ _ (fe_tb cx) body l HAR3 Hsb Hcaw).
  - exact (fs_glob_below W3 _ _ _ _ _ _ Hsb Hg).
  - split; [reflexivity|]. split; [lia|]. destruct (body =? 0); unfold FE_CNT_MAX, CRT_ALLOCS, FS_CNT_LIB in *; lia.
  - unfold FSH_Fn_writer.dec_ev. destruct (WriterSpec.b64_dec (fe_tb cx));
      unfold KB7, EV_check_no_overread, EV_preset_base64_decode, EV_preset_base64_encode, EV_check_as_written,
      EV_check_round_trip, EV_fuzz_malloc, EV_LIB, EV_MAX in *; lia.
  - unfold LIVE_MAX, ACfn.LIVE_LIB, HEAD in *. lia.
  - unfold fe_live6. unfold ACfn.LIVE_LIB in Hlive0. destruct (body =? 0); lia.
  - intros Hb0. destruct (HcawB Hb0) as (_ & Hl0). unfold fe_live6. rewrite (proj2 (Z.eqb_neq body 0) Hb0).
    unfold FSH_Fn_writer.enc_size. unfold LIVE_MAX, HEAD, ACfn.LIVE_LIB in *.
    assert (Henc : (l + 2) / 3 * 4 <= 2 * l + 4) by (clear - Hl0; Z.div_mod_to_equations; lia).
    split; fe8_lia. }
cbv beta. intros W4 c4 Hwle4 Hpost.
destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Ebl4 & Hg4)).
rewrite Esp in HJc. rewrite R1.
destruct (fe8_after_pcall cx E ly3 S3 (fe_body_U body) W3 msR _ k _ [fe_len_atom 46] STK_check_reject_clean_starved
  FS_PSTAT_FP ly4 S4 (fe_body_U body) W4 mem4 md4 EV_check_reject_clean_starved regs4 RA_starved
  Hbase HE Hcore HJ HARU HS0 eq_refl ltac:(repeat split; reflexivity) HJc OK4 PO4 HP4
  ltac:(unfold STK_check_reject_clean_starved; vm_compute; split; discriminate)) as (HJ4 & HARU4 & Hcore4 & HS4).
- intros a Ha. right. right. left. split; [exact Ha | exact (fe8_pstat_img a Ha)].
- intros a Ha Hp. apply (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 0 (c_fpos cx) a HAR3 Hfin3).
  { rewrite EF3. change (fs_frame_bytes 0) with 64. lia. }
  exact (fe8_pstat_img a Hp).
- apply (HNEXT cx (Ereg regs4 (fe_extra cx ++ [])) (k + EV_check_reject_clean_starved) ly4 S4 (fe_body_U body) W4
    (YK11.mkst regs4 (Z_to_bv 64 528640) mem4 (YK11.seg_rom tfibsegs)) md4 Hbase (fe_E_Ereg cx regs4 []) HJ4 HARU4);
    [|exact HS4].
  exists text, body, (if body =? 0 then cnt7 + 1 else cnt7 + 2).
  split; [reflexivity|]. split; [rewrite Ebl4; exact HPerm|].
  split.
  { intros Hb0. destruct (HBB Hb0) as (Hbb3 & _).
    apply (fe8_rblock_keep _ _ _ ly3 S3 (fe_body_U body) W3 (ms_mem msR) _ ly4 S4 (fe_body_U body) W4 mem4 md4 _ body
      (dec_size (fe_tb cx)) HJc HARU HARU4).
    - rewrite Ebl4. exact Hbb3.
    - intros i Hi Hp. apply (blk_img tfibsegs B LAWS _ _ _ _ _ _ _ (body - HEAD + i) HAR3 Hbb3).
      + pose proof (req_size_pos (dec_size (fe_tb cx) + HEAD) ltac:(unfold HEAD; lia)). unfold HEAD in *. lia.
      + exact (fe8_pstat_img _ Hp).
    - exact (fs_rblock_below B ly3 S3 W3 _ md3 _ _ body _ HAR3 Hsb (proj1 (HcawB Hb0))). }
  split; [unfold KB7, EV_check_reject_clean_starved in *; lia|]. split; [exact Hcore4|].
  split; [rewrite (ew_Ereg_nat regs4 _ 21 21%bv eq_refl), (fe8_kept _ _ _ msR regs4 21%bv 21 HS0 eq_refl HP4 ltac:(fe8_cs));
    exact E21|].
  split; [rewrite (ew_Ereg_nat regs4 _ 22 22%bv eq_refl), (fe8_kept _ _ _ msR regs4 22%bv 22 HS0 eq_refl HP4 ltac:(fe8_cs));
    exact E22|].
  split; [exists peak; exact Hg4|].
  destruct (body =? 0); unfold FE_CNT_MAX, CRT_ALLOCS in *; lia.
Qed.

(* ---- S8 (0x810f0-0x8110c) ---- *)
Lemma fe_seg8 : forall POST, fe_from B FS_PSTAT_FP POST (fe_ss PC_epi []) (INV_C9 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_crc [fe_len_atom 46]) (INV_C7 B).
Proof. intros POST H. exact (fe8_st POST (fe8_ff POST (fe8_free POST H))). Qed.

End s.

