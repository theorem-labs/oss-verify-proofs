(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfGvfi0.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 5 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMupoison -> lib.A.Rt; FMH_Base -> lib.A.Rt.SnprintfFmh. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: __interceptor_vfprintf of fm.asan (0x457ec, frame 0x30, entered from musl vsnprintf
   through __wrap_vfprintf) ported from A/AE35.v's walk: the entry state with the read-only image cells in vpA_rodata's
   form, TryAsanInitFromRtl and the common_flags ()->check_printf test run through, REAL (vfprintf) read from 0x9b740,
   the epilogue and ret as in tfib_vprintf_icpt_E; the inline printf_common run is replaced by a kcall of the
   printf_common contract (apcommon_realizesU), musl vfprintf by a kcall of avfp_realizes; the vprintf entry part
   (tfib_vprintf_icpt_A) is not used; stated as FMsnprintfGI's avfpi_realizes over FMsnprintfI's snk_frame. *)
(* Modified by Theorem Labs, 2026-10: the walk's window-free helpers (vfi_rodata, vfi_rodata_chk, vfi_facts, ro_far,
   CS_REGS, regs_kept, st_ok_first, ro_far_sound, vfi_ro_low, vfi_ro_region_low, sv_atom, vfi_preserved) moved here
   unchanged from FMsnprintfGvfi.v, which Require Exports this file; this file reaches no stack band. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison SnprintfFmh FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfGk0 FMsnprintfGt0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the read-only image cells of the walk: icpt_rodata (TryAsanInitFromRtl's asan_inited) and the common_flags
   pointer, check_printf and REAL (vfprintf); the entry sp's facts; the shapes the proof reads off the states ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition vfi_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x98ea8, 8, [(0, 8%N, 0x132aa8)]); (0x132afc, 1, [(0, 1%N, 1)]); (0x9ac20, 8, [(0, 8%N, 0x8e9c0)])].
Lemma vfi_rodata_chk : forall ly, rodata_chk ly vfi_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition vfi_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] [].
Definition ro_far (r : YP09.region) : bool :=
match YP09.r_base r with
| None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 2 ^ 40) && (YP09.r_whi r <=? YP09.r_wlo r)
| Some _ => false
end.
Definition CS_REGS : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_kept (ss : sstate) : bool :=
forallb (fun r => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) CS_REGS.
End r.

(* ---- general lemmas of the walk ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* keep the first region (the stack) only *)
Lemma st_ok_first : forall E ss ms r0 rest, st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest ->
  st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
Lemma ro_far_sound : forall E rs r a, forallb ro_far rs = true -> In r rs ->
  (base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 40) /\
  ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r).
Proof.
intros E rs r a Hf Hin. rewrite forallb_forall in Hf. specialize (Hf r Hin). unfold ro_far in Hf.
destruct (YP09.r_base r); [discriminate|]. cbn [base_val].
apply andb_prop in Hf as [Hf H3]. apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. split; lia.
Qed.
(* The image constants are cells below SHADOW_OFF, where `unpoison U mem` reads `mem` (the proof of a Theorem Labs
   lane's ro_region_low). *)
Definition vfi_ro_low (l : list (Z * Z * list (Z * BinNums.N * Z))) : bool :=
forallb (fun r => forallb (fun c => (0 <=? fst (fst r) + fst (fst c)) &&
(fst (fst r) + fst (fst c) + Z.of_N (snd (fst c)) <=? SHADOW_OFF)) (snd r)) l.
Lemma vfi_ro_region_low : forall l E (m m' : word -> option byte), vfi_ro_low l = true ->
(forall w : word, bv_unsigned w < SHADOW_OFF -> m' w = m w) ->
Forall (region_ok tfibsegs E m) (map ro_region l) -> Forall (region_ok tfibsegs E m') (map ro_region l).
Proof.
intros l E m m' Hl Hm HF. unfold vfi_ro_low in Hl. rewrite forallb_forall in Hl.
rewrite Forall_forall in HF. apply Forall_map. rewrite Forall_forall. intros [[base sz] cs] Hin.
specialize (Hl _ Hin). specialize (HF _ (in_map ro_region _ _ Hin)). cbn [fst snd] in Hl. rewrite forallb_forall in Hl.
destruct HF as (B1 & B2 & Hw & Hc).
unfold ro_region, region_ok in *. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; exfalso; lia|].
rewrite Forall_forall in Hc. apply Forall_map. rewrite Forall_forall. intros [[off n] v] Hc'.
specialize (Hl _ Hc'). specialize (Hc _ (in_map (ro_chunk base) _ _ Hc')). cbn [fst snd] in Hl. apply andb_prop in Hl as [L1 L2].
apply Z.leb_le in L1. apply Z.leb_le in L2.
intros i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
unfold ro_chunk, c_len in *. cbn [YP09.c_off YP09.c_val cv_len fst snd] in *.
unfold mbyte in *. rewrite Hm; [exact Hb2|]. unfold SHADOW_OFF in *. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma sv_atom : forall E n (regs : bvmap 5 word) (r : bv 5), ew E n = getr regs r -> sv_denot E (SOff n 0) = getr regs r.
Proof. intros E n regs r He. cbn [sv_denot]. rewrite Z.add_0_r, He, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* the callee-saved registers of a final state that holds them as the entry atoms *)
Lemma vfi_preserved : forall (Hd : word -> bool) E ss ms (regs : bvmap 5 word),
  st_ok tfibsegs E ss (restrict Hd ms) -> regs_kept ss = true ->
  (forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew E i = getr regs r) ->
  aregs_preserved regs (ms_regs ms).
Proof.
intros Hd E ss ms regs HS Hk HE r Hr.
assert (Hin : In r CS_REGS) by (unfold acallee_saved in Hr; unfold CS_REGS; cbn [In]; lia).
assert (Hr32 : 0 <= r < 32) by (unfold CS_REGS in Hin; cbn [In] in Hin; lia).
unfold regs_kept in Hk. rewrite forallb_forall in Hk. specialize (Hk r Hin). apply sv_eqb_eq in Hk.
rewrite (st_ok_reg_denot Hd E ss ms _ HS), Hk. apply sv_atom. apply HE; [|lia].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
rewrite Z.mod_small by lia. reflexivity.
Qed.
End h.
