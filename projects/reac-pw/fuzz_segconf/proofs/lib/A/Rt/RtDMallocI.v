(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtDMallocI.v (donor image sha256 c0661b96b5bd), with its module paths changed. *)
(* The register file the relocated malloc chain (lib/A/AF*.v) is stated on, from asan_malloc's own register file
   (lib/A/Rt/RtDDefs.v amalloc_inner_realizes): sp raised by the interceptor body's frame IFRAME = 2,128, so the
   chain's atom 2 keeps the value it had when the chain started at the trampoline. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AF0x AFhy.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Open Scope Z_scope.
(* The chain's register file regs0: asan_malloc's register file with sp raised by IFRAME to the interceptor's sp0, so that
   atom 2 keeps the meaning it had when the chain started at the trampoline. *)
Definition regs0_of (regs : bvmap 5 word) : bvmap 5 word := regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2) + IFRAME)).
Lemma regs0_of_facts : forall (regs : bvmap 5 word),
bv_unsigned (getr regs 2) + IFRAME < 2 ^ 64 ->
bv_unsigned (getr (regs0_of regs) 2) = bv_unsigned (getr regs 2) + IFRAME /\
(forall r : bv 5, r <> 2%bv -> getr regs r = getr (regs0_of regs) r) /\
getr regs 2 = Z_to_bv 64 (bv_unsigned (getr (regs0_of regs) 2) - IFRAME).
Proof.
intros regs Hlt. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as U. change (bv_modulus 64) with (2 ^ 64) in U.
assert (E2 : bv_unsigned (getr (regs0_of regs) 2) = bv_unsigned (getr regs 2) + IFRAME).
{ unfold regs0_of. rewrite getr_same by (intros X; discriminate X). rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. unfold IFRAME in *. lia. }
split; [exact E2|]. split.
- intros r Hr. unfold regs0_of. rewrite getr_other by exact Hr. reflexivity.
- rewrite E2. replace (bv_unsigned (getr regs 2) + IFRAME - IFRAME) with (bv_unsigned (getr regs 2)) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The premises of amalloc_inner_realizes on asan_malloc's register file regsI give the chain's stack and trace
   hypotheses (lib/A/AFis.v Hsp, Hch) on regs0 = regs0_of regsI, and the two facts that tie regsI to regs0. *)
Lemma inner_chain_facts : forall (regsI : bvmap 5 word) (lo hi p : Z) (W : world tfibsegs) (mem : word -> option byte) (ch : list Z),
hi < 2 ^ 64 ->
bv_unsigned (getr regsI 2) mod 16 = 0 -> lo + MALLOC_ASAN_STK <= bv_unsigned (getr regsI 2) ->
bv_unsigned (getr regsI 2) + IFRAME <= hi ->
getr regsI 11 = Z_to_bv 64 p -> bv_unsigned (getr regsI 2) <= p -> p mod 8 = 0 -> p + 16 + 8 * 30 <= hi ->
astrace_at tfibsegs W mem p ch -> (1 <= length ch)%nat -> (length ch <= 30)%nat ->
(lo + MALLOC_IN_STK <= bv_unsigned (getr (regs0_of regsI) 2) /\
 bv_unsigned (getr (regs0_of regsI) 2) - IFRAME <= bv_unsigned (getr (regs0_of regsI) 11) /\
 bv_unsigned (getr (regs0_of regsI) 2) <= hi /\ bv_unsigned (getr (regs0_of regsI) 2) mod 16 = 0) /\
((1 <= length ch <= 30)%nat /\ bv_unsigned (getr (regs0_of regsI) 11) mod 8 = 0 /\
 bv_unsigned (getr (regs0_of regsI) 11) + 16 + 8 * 30 <= hi /\ astrace_at tfibsegs W mem (bv_unsigned (getr (regs0_of regsI) 11)) ch) /\
(forall r : bv 5, r <> 2%bv -> getr regsI r = getr (regs0_of regsI) r) /\
getr regsI 2 = Z_to_bv 64 (bv_unsigned (getr (regs0_of regsI) 2) - IFRAME) /\
bv_unsigned (getr (regs0_of regsI) 2) = bv_unsigned (getr regsI 2) + IFRAME.
Proof.
intros regsI lo hi p W mem ch Hhi Hal Hlo Htop Hp Hpl Hp8 Hpt Hast L1 L30.
pose proof (bv_unsigned_in_range 64 (getr regsI 2)) as U. change (bv_modulus 64) with (2 ^ 64) in U.
destruct (regs0_of_facts regsI ltac:(unfold IFRAME in *; lia)) as (E2 & EO & E2I).
assert (P11 : bv_unsigned (getr (regs0_of regsI) 11) = p).
{ rewrite <- (EO 11%bv ltac:(intros X; discriminate X)), Hp. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
rewrite P11, E2. unfold MALLOC_IN_STK, MALLOC_ASAN_STK, IFRAME in *.
split; [|split; [|split; [exact EO | split; [rewrite E2 in E2I; exact E2I | reflexivity]]]].
- split; [lia|]. split; [lia|]. split; [lia|].
replace (bv_unsigned (getr regsI 2) + 2128) with (bv_unsigned (getr regsI 2) + 133 * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- split; [lia|]. split; [exact Hp8|]. split; [lia | exact Hast].
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The premises of amalloc_inner_realizes (lib/A/Rt/RtDDefs.v) in one proposition, for the relocated chain's tops. *)
Definition ipre (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (regsI : bvmap 5 word) (mem : word -> option byte) (md : Model)
(n p : Z) (tr : list Z) : Prop :=
AR tfibsegs B ly S W mem md /\ aregime S /\ YK0s.ret_ok (getr regsI 1) /\
spZ regsI mod 16 = 0 /\ ly_stk_lo ly + MALLOC_ASAN_STK <= spZ regsI /\ spZ regsI + 2128 <= ly_stk_hi ly /\
(forall a, spZ regsI - MALLOC_ASAN_STK <= a < spZ regsI -> apresent (w_H W) mem a) /\
getr regsI 3 = w64 (as_gp B) /\ getr regsI 4 = w64 (as_tp B) /\ qmeter S /\
getr regsI 10 = w64 n /\ getr regsI 11 = w64 p /\
spZ regsI <= p /\ p mod 8 = 0 /\ p + 16 + 8 * 30 <= ly_stk_hi ly /\
astrace_at tfibsegs W mem p tr /\ (1 <= length tr)%nat /\ (length tr <= kUnwindMax)%nat.
(* What the chain's sections assume of regs0 = regs0_of regsI (lib/A/AFis.v and the other sections' copies). *)
Lemma ipre_chain : forall B ly S W regsI mem md n p tr, ipre B ly S W regsI mem md n p tr ->
let regs0 := regs0_of regsI in let sp0 := bv_unsigned (getr regs0 2) in let pT := bv_unsigned (getr regs0 11) in
AR tfibsegs B ly S W mem md /\ aregime S /\ YK0s.ret_ok (getr regs0 1) /\
getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\ qmeter S /\ getr regs0 10 = w64 n /\
(ly_stk_lo ly + MALLOC_IN_STK <= sp0 /\ sp0 - IFRAME <= pT /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) /\
((1 <= length tr <= 30)%nat /\ pT mod 8 = 0 /\ pT + 16 + 8 * 30 <= ly_stk_hi ly /\ astrace_at tfibsegs W mem pT tr) /\
(forall a, sp0 - MALLOC_IN_STK <= a < sp0 - IFRAME -> apresent (w_H W) mem a) /\
(forall r : bv 5, r <> 2%bv -> getr regsI r = getr regs0 r) /\ getr regsI 2 = w64 (sp0 - IFRAME).
Proof.
intros B ly S W regsI mem md n p tr (HAR & Hev & Hra & Hal & Hlo & Hhi & Hpres & Hgp & Htp & HQT & Hn & Hp & Hpl & Hp8 & Hpt & Hast & L1 & L30).
pose proof (lo_top ly (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & LHI & _ & _ & _). unfold kHighMemEnd in LHI.
unfold spZ in *.
destruct (inner_chain_facts regsI (ly_stk_lo ly) (ly_stk_hi ly) p W mem tr ltac:(lia) Hal Hlo ltac:(unfold IFRAME; lia) Hp Hpl Hp8 Hpt Hast L1
ltac:(unfold kUnwindMax in L30; lia)) as (Hsp & Hch & RIo & RI2 & SP0).
cbv zeta.
assert (G : forall r : bv 5, r <> 2%bv -> getr (regs0_of regsI) r = getr regsI r) by (intros r Hr; symmetry; exact (RIo r Hr)).
split; [exact HAR|]. split; [exact Hev|].
split; [rewrite (G 1%bv ltac:(intros X; discriminate X)); exact Hra|].
split; [rewrite (G 3%bv ltac:(intros X; discriminate X)); exact Hgp|].
split; [rewrite (G 4%bv ltac:(intros X; discriminate X)); exact Htp|].
split; [exact HQT|].
split; [rewrite (G 10%bv ltac:(intros X; discriminate X)); exact Hn|].
split; [exact Hsp|]. split; [exact Hch|].
split; [intros a Ha; apply Hpres; rewrite SP0 in Ha; unfold MALLOC_IN_STK, MALLOC_ASAN_STK, IFRAME in *; lia|].
split; [exact RIo | exact RI2].
Qed.
End i.
