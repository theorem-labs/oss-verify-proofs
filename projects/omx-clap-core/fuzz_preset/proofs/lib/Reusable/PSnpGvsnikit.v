(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* fm's snprintf glue, the vsnprintf interceptor level: avsni_realizes (FMsnprintfGI.v) for fm.asan's
   __interceptor_vsnprintf 0x458a0, from printf_common's contract (apcommon_realizesU), musl vsnprintf's (avsn_realizes)
   and the WRITE_RANGE (str, res + 1) check (FMsnprintfGwrc.v vsn_wr_check_srrU).
   The walk (MEASURED: the symbolic runs below; disassembly, the internal file 0x458a0.s):
     entry sp = sp0 + 0x9d0 (atom 2); the prologue saves ra, s0..s7 at entry - 8 .. entry - 0x48 and the va pointer P at
       entry - 0x58 and entry - 0x60, sp = entry - 0x870 = sp0 + 0x160; TryAsanInitFromRtl 0x59a78 returns 1 (it reads
       asan_inited 0xa2a58 = 1); check_printf (0x999a0 -> 0x1338a8, byte 0x1338fc) = 1;
     printf_common (ctx 0x17890, format, P) returns to 0x45918: a kcall, its band [sp - STK_PCOM, sp);
     REAL (vsnprintf) = 0x91f0c from 0x9b748, entered with (D, N, format, P), returns to 0x45934: a kcall, its band
       [sp0 - SNK_STK, sp0 + 0x160) and the destination [D, D + M);
     res >= 0 (bltz not taken), size >= res + 1 (bgeu taken): 0x45a14 mv s1, a1, then the check at 0x45a18 with
       s1 = res + 1, s2 = str, s3 = size, a0 = res; it returns at 0x4599c;
     the epilogue reloads ra, s0..s7 from the saved slots (a symbolic state built from them, as A/AE35.v builds its
       ss_epi) and returns. *)
(* Modified by Theorem Labs, 2026-10: the image-free half of origin/cold/port-fm-rtprintf-param 7e395de08f5
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsni.v for the snprintf chain restated over ARx (route (a),
   c-omx-hpreset 10:51Z): only the items the four roots' closure reaches, AC (:58), SAVED / epi_chunks (:80-82),
   stk_chunks (:97-98), st_ok_head, den_atom, bvu5, ra_xfer, hull_xfer (:101-127), EOK_havoc_lt (:156-157),
   saved_range (:166-167), with `tfibsegs` an implicit Section variable segs. The header's addresses above are
   fm's (the source's comment). 0x868 is a frame offset of __interceptor_vsnprintf, the same at every image of this
   code. vsni_rodata, the runs and ss_epi are image-bearing and live in lib/A/PSnpGvsni.v. The walk of the vsnprintf
   interceptor and avsni_ok (the HarnessDesign route) are not reached and not ported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpGkit.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* the epilogue's saved ra, s0..s7 as atoms 32..40, at sp + 0x868 - 8 j (sp = the entry sp - 0x870) *)
Definition SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
Definition epi_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (0x868 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 9).
Definition stk_chunks (ss : sstate) : list YP09.chunk :=
  match ss_mem ss with r :: _ => YP09.r_chunks r | [] => [] end.

(* ---- general facts ---- *)
Lemma st_ok_head : forall E ss ms r0 rest,
  st_ok segs E ss ms -> ss_mem ss = r0 :: rest -> st_ok segs E (set_mem ss [r0]) ms.
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
Lemma saved_range : forall j, (j < 9)%nat -> 0 <= nth j SAVED 0 < 32.
Proof. intros j Hj. do 9 (destruct j as [|j]; [cbn; lia|]). lia. Qed.
End v.
