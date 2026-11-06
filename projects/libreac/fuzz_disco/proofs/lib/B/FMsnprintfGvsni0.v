(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsni0.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 6 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv); names: A-core -> Y-core (lib.Reusable): AB1v->YB1v, AE20->YE20, AE2y->YE2y, AE34->YE34, AF0l->YF0l, AF0m->YF0m, AF0x->YF0x. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* Modified by Theorem Labs, 2026-10: the window-free part of FMsnprintfGvsni.v moved here unchanged (vsni_rodata,
   vsni_rodata_chk, RUNTO, RUN, AC, SAVED, epi_chunks, ss_epi, epi_e, r_epi, stk_chunks, st_ok_head, den_atom, bvu5,
   ra_xfer, hull_xfer, EOK_havoc_lt, ro_low, saved_range); it reaches no file that fixes fm's stack bands
   (FMsnprintfImg / Gk0 / Gt0 in place of I / GI / Gk / Gt, no FMH_Rt). FMsnprintfGvsni.v re-exports it. *)
(* fm's snprintf glue, the vsnprintf interceptor level, window-free part: the image cells the walk reads, the runner,
   the epilogue state and its run, and the general facts of FMsnprintfGvsni.v's walk. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require Import FMsnprintfGk0 FMsnprintfGt0.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the image cells the walk reads: asan_inited, the common_flags pointer, check_printf, REAL (vsnprintf) *)
Definition vsni_rodata : list (Z * Z * list (Z * N * Z)) :=
  [(0xaa158, 1, [(0, 1%N, 1)]); (0xa08a0, 8, [(0, 8%N, 0x13afa8)]); (0x13affc, 1, [(0, 1%N, 1)]);
   (0xa2618, 8, [(0, 8%N, 0x99478)])].
Lemma vsni_rodata_chk : forall ly, rodata_chk ly vsni_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* the epilogue from the check's return: the saved ra, s0..s7 as atoms 32..40, at sp + 0x868 - 8 j (sp = sp0 + 0x160) *)
Definition SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
Definition epi_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (0x868 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 9).
Definition ss_epi : sstate :=
  mkSS WRC_END sr_atoms [YP09.mkRegion (Some 2%nat) 0x828 0x870 0x828 0x828 epi_chunks] None
    (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.

Definition stk_chunks (ss : sstate) : list YP09.chunk :=
  match ss_mem ss with r :: _ => YP09.r_chunks r | [] => [] end.

(* ---- general facts ---- *)
Lemma st_ok_head : forall E ss ms r0 rest,
  st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest -> st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
Lemma den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma bvu5 : forall r, 0 <= r < 32 -> bv_unsigned (Z_to_bv 5 r) = r.
Proof.
intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hr.
Qed.
Lemma ra_xfer : forall (rd rd' : Z -> option Z) x n, range_addressable rd SHADOW_OFF x n ->
  (forall y, x <= y < x + n -> rd' (SHADOW_OFF + y / 8) = rd (SHADOW_OFF + y / 8)) ->
  range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Hra Heq y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (Heq y Hy). exact Hs.
Qed.
Lemma hull_xfer : forall (rd rd' : Z -> option Z) x n, shadow_hull_vis rd x n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Hh Heq s Hs. rewrite (Heq s Hs). exact (Hh s Hs). Qed.
Lemma EOK_havoc_lt : forall E k ws i, (i < k)%nat -> ew (havoc E k ws) i = ew E i.
Proof. intros E k ws i Hi. unfold havoc. cbn [ew]. rewrite (proj2 (Nat.ltb_lt i k) Hi). reflexivity. Qed.
Lemma ro_low : forall r, In r (map ro_region vsni_rodata) ->
  region_wf r = true /\ YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 0x140000 /\
  YP09.r_wlo r = YP09.r_whi r.
Proof.
intros r Hr. unfold vsni_rodata in Hr. cbn [map] in Hr.
repeat destruct Hr as [<-|Hr]; try destruct Hr;
repeat split; vm_compute; first [reflexivity | intros Hc; discriminate].
Qed.
Lemma saved_range : forall j, (j < 9)%nat -> 0 <= nth j SAVED 0 < 32.
Proof. intros j Hj. do 9 (destruct j as [|j]; [cbn; lia|]). lia. Qed.

End v.
