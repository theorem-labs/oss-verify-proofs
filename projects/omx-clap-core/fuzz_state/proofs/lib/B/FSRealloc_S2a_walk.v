(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fuzz_state image B (projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan-ubsan,
   sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204): the MACHINE WALK of realloc's
   thin segment S2a, from Allocate's return 0x32a04 to the `jalr a3` 0x32a78 that enters musl memcpy 0x98f3c.
   No allocator invariant appears here: register/memory facts in, register/memory facts out.

   The B twin of lib/A/FSRealloc_S2a_walk.v (a working branch 98113525978), which is the
   template: the same 30 instructions at +0x70, word for word except the pc-relative lo12 of the GOT load
   (A 0x329d8 d4453503 `ld a0, -0x2bc(a0)`, B 0x32a48 1f453503 `ld a0, 0x1f4(a0)`), so the same proof script
   over B's addresses (fs-addr-map.tsv's fs_asan_ubsan column, rows 10, 11, 15, 17, 18).  A's file is a port of
   the released donor proofs/cgif/cgif_rgb_fuzzer/lib/YF67.v (`R_HDR` :24-25, `F_C1` :26, `SM1` :27,
   `denot_by_zev` :151-155, `c1_copy` :156-261).  Bespoke template (L12): ricptC of the pre-ruling AZ line
   (a working branch lib/AZ/AsanW/F_arealloc_pre.v), not cut at the jalr.

   Rule 24 (released-proof lookup): proof-index by NAME and by the B addresses 0x530e8 / 0x534e4, unpiped,
   2026-10-29 03:50-03:56Z (internal path, 0x534e4.txt): 0 named, 0 by
   address, 0 related, 0 lemmas; named cold branches (r24/1029/cold-search.md, 725 refs): the only other holder
   is fs's pre-ruling bespoke line, a template only (owner ruling a Theorem Labs lane 04:50Z).

   CLOSURE: no lib/A file that names an image or holds a per-image address is Required (only lib/B and
   lib/Reusable).

   THE CODE WALKED (python3 + capstone 5.0.7 over the pinned B image, CS_ARCH_RISCV / CS_MODE_RISCV64, no
   compressed instructions; 30 instructions, 0x32a04 .. 0x32a78 inclusive, which is what tfib_s2a_tbl below
   tabulates; capstone prints branch / jal immediates as offsets, the target follows in []):
     0x32a04 00050a13 mv s4, a0            s4 := q
     0x32a08 08050863 beqz a0, 0x90        [0x32a98] NOT taken (a0 = q, atom fact 4096 <= q <= 2 ^ 47 on x10)
     0x32a0c ff048503 lb a0, -0x10(s1)     chunk state byte at p-16 = 2 (CHUNK_ALLOCATED)
     0x32a10 00200593 addi a1, zero, 2
     0x32a14 0230000f fence r, rw
     0x32a18 02b50663 beq a0, a1, 0x2c     [0x32a44] TAKEN; the ReportDoubleFree / ReportInvalidFree arms
                                           0x32a1c-0x32a40 are UNTAKEN and never executed
     0x32a1c 0ff57513 andi a0, a0, 0xff    ) the untaken arms
     0x32a20 00300593 addi a1, zero, 3     )
     0x32a24 00b51a63 bne a0, a1, 0x14     ) [0x32a38]
     0x32a28 00048513 mv a0, s1            )
     0x32a2c 00040593 mv a1, s0            )
     0x32a30 3f5230ef jal 0x23bf4          ) [0x56624]
     0x32a34 0100006f j 0x10               ) [0x32a44]
     0x32a38 00048513 mv a0, s1            )
     0x32a3c 00040593 mv a1, s0            )
     0x32a40 0f0240ef jal 0x240f0          ) [0x56b30]
     0x32a44 0006d517 auipc a0, 0x6d       ) a0 := 0x32a44 + 0x6d000 = 0x9fa44
     0x32a48 1f453503 ld a0, 0x1f4(a0)     ) GOT slot 0x9fa44 + 0x1f4 = 0x9fc38, holding 0xa1a88
     0x32a4c 00053683 ld a3, 0(a0)         a3 := [0xa1a88] = musl memcpy 0x98f3c
     0x32a50 08068663 beqz a3, 0x8c        [0x32adc] NOT taken (a3 = 0x98f3c)
     0x32a54 ff24d503 lhu a0, -0xe(s1)     UsedSize high half at p-14 = 0
     0x32a58 ff44e583 lwu a1, -0xc(s1)     UsedSize low word at p-12 = nold
     0x32a5c 02051513 slli a0, a0, 0x20
     0x32a60 00b56533 or a0, a0, a1        a0 = nold
     0x32a64 00a9e463 bltu s3, a0, 8       [0x32a6c] the two arms below: n < nold skips the `mv`, else takes it
     0x32a68 00050993 mv s3, a0            s3 := nold
     0x32a6c 000a0513 mv a0, s4            a0 := q
     0x32a70 00048593 mv a1, s1            a1 := p
     0x32a74 00098613 mv a2, s3            a2 := Z.min n nold
     0x32a78 000680e7 jalr a3              ra := 0x32a7c (FS_RA_COPY, `addi a5, zero, 1` 00100793),
                                          pc := 0x98f3c (tfib_A_memcpy, musl's memcpy, `andi a3, a1, 3` 0035f693)
   No store executes anywhere in the walk, and x2 x3 x4 x8 x9 x18 x21..x27 x29 x30 x31 are untouched.
   The image bytes (LE u64) at 0x9fc38 are 0xa1a88 and at 0xa1a88 are 0x98f3c (read from the pinned image).

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w YF0l YF0m YF0x YFeq FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* ------------------------------------------------------------------------------------------------------- *)
(* The code table of the segment: the 30 instructions 0x32a04 .. 0x32a78 read out of the pinned B image.
   0x98f3c (the `jalr a3` target) need not be tabulated: the run stops there.                               *)
Definition tfib_s2a_tbl_build : ctable := build_table tfibsegs 0x32a04 30%nat TEmpty.
Definition tfib_s2a_tbl : ctable := Eval vm_compute in tfib_s2a_tbl_build.
Lemma tfib_s2a_tbl_eq : tfib_s2a_tbl = tfib_s2a_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable tfib_s2a_tbl). Qed.
Lemma tfib_s2a_tbl_ok : table_ok tfibsegs tfib_s2a_tbl.
Proof. rewrite tfib_s2a_tbl_eq. unfold tfib_s2a_tbl_build. apply build_table_ok0. cbv. discriminate. Qed.

(* ------------------------------------------------------------------------------------------------------- *)
(* The symbolic entry state (donor YF67.v:24-27).
   R_HDR  : the 8 header bytes below the old block, based on x9 = s1 = p.  The three chunks are the three
            fields the walk reads: the state byte at p-16 (`lb a0, -0x10(s1)` 0x32a0c), the UsedSize high
            half at p-14 (`lhu a0, -0xe(s1)` 0x32a54) and the UsedSize low word at p-12
            (`lwu a1, -0xc(s1)` 0x32a58).  No write window (0 0): the walk stores nothing.
   R_GOT  : the GOT slot 0x9fc38 (`auipc a0, 0x6d` 0x32a44 + `ld a0, 0x1f4(a0)` 0x32a48), holding 0xa1a88.
   R_CELL : the cell 0xa1a88 (`ld a3, 0(a0)` 0x32a4c), holding musl memcpy 0x98f3c.
   F_S2A  : the two atom bounds the engine needs -- x10 = q in [4096, 2 ^ 47] so that `beqz a0` 0x32a08 is
            decided NOT taken, and the extra slot 32 (= nold) in [0, 2 ^ 32 - 1].                           *)
Definition R_HDR : YP09.region := YP09.mkRegion (Some 9%nat) (-16) (-8) 0 0
[YP09.mkChunk (-16) (CVal 1 (SLit 2)); YP09.mkChunk (-14) (CVal 2 (SLit 0)); YP09.mkChunk (-12) (CVal 4 (SOff 32 0))].
Definition R_GOT : YP09.region := flit8 0x9fc38 0xa1a88.
Definition R_CELL : YP09.region := flit8 0xa1a88 0x98f3c.
Definition F_S2A : facts := mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition SS_S2A : sstate := mkSS FS_RA_ALLOC sr_atoms [R_HDR; R_GOT; R_CELL] None F_S2A.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* donor YF67.v:151-155 *)
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v ->
sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (YF0x.U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
symmetry. apply Z.mod_small. exact Hv.
Qed.
End H.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable W : world tfibsegs.
Variable md : Model.

Definition s2a_post (regs2 : bvmap 5 word) (mem2 : word -> option byte) (qa pa len : Z)
  (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsM memM mat,
c' = cfg_at tfibsegs tfib_A_memcpy regsM memM (with_vm_backing (m_vm_lazy md) mat md) /\
(forall x : word, memM x = mem2 x) /\
getr regsM 1 = w64 FS_RA_COPY /\ getr regsM 10 = w64 qa /\ getr regsM 11 = w64 pa /\
getr regsM 12 = w64 len /\ getr regsM 20 = w64 qa /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv ->
   getr regsM r = getr regs2 r).

Lemma s2a_walk : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (qa pa n nold : Z),
getr regs2 9 = w64 pa -> getr regs2 10 = w64 qa -> getr regs2 19 = w64 n ->
4096 <= qa < 2 ^ 47 -> 0 <= n < 2 ^ 32 -> 0 <= nold < 2 ^ 32 ->
YF0x.zone3 (pa - 16) 16 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (pa - 16) 1 2 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (pa - 14) 2 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) (pa - 12) 4 nold ->
val_mem tfibsegs (mrestrict (w_H W) mem2) 0x9fc38 8 0xa1a88 ->
val_mem tfibsegs (mrestrict (w_H W) mem2) 0xa1a88 8 0x98f3c ->
SRr tfibsegs W (cfg_at tfibsegs FS_RA_ALLOC regs2 mem2 md) (s2a_post regs2 mem2 qa pa (Z.min n nold)).
Proof.
intros regs2 mem2 qa pa n nold G9 G10 G19 Hq Hn Hnold HZ V0 V2 V4 VC1 VC2.
pose proof YF0x.Hwx_tfa as Hwx.
pose proof (@ASAN_CEIL_range rc) as [CR _].
destruct HZ as (Z0 & Z1 & Z2).
unfold YF0x.zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in Z2.
assert (Hpa : 4112 <= pa <= 0x7fffff800000) by lia.
(* the environment: the 32 architectural registers of regs2, plus one extra slot (index 32) holding nold *)
assert (E9 : ew (Ereg regs2 [w64 nold]) 9 = w64 pa)
  by exact (eq_trans (ew_Ereg_nat regs2 [w64 nold] 9 9%bv eq_refl) G9).
assert (E10 : ew (Ereg regs2 [w64 nold]) 10 = w64 qa)
  by exact (eq_trans (ew_Ereg_nat regs2 [w64 nold] 10 10%bv eq_refl) G10).
assert (E19 : ew (Ereg regs2 [w64 nold]) 19 = w64 n)
  by exact (eq_trans (ew_Ereg_nat regs2 [w64 nold] 19 19%bv eq_refl) G19).
assert (E32 : ew (Ereg regs2 [w64 nold]) 32 = w64 nold)
  by exact (ew_Ereg_extra regs2 [w64 nold] 0).
assert (B9 : bv_unsigned (ew (Ereg regs2 [w64 nold]) 9) = pa)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (B10 : bv_unsigned (ew (Ereg regs2 [w64 nold]) 10) = qa)
  by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (R19 : rho_of (Ereg regs2 [w64 nold]) 19%nat = n)
  by (unfold rho_of; rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (R32 : rho_of (Ereg regs2 [w64 nold]) 32%nat = nold)
  by (unfold rho_of; rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* the entry state is sound (donor YF67.v:170-192) *)
assert (HS : st_ok tfibsegs (Ereg regs2 [w64 nold]) SS_S2A
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 FS_RA_ALLOC) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SS_S2A. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, R_HDR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite B9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * eapply (chunk_ok_val tfibsegs _ _ _ (-16) 1 (SLit 2) 2);
        [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact V0 | lia]].
      * eapply (chunk_ok_val tfibsegs _ _ _ (-14) 2 (SLit 0) 0);
        [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact V2 | lia]].
      * eapply (chunk_ok_val tfibsegs _ _ _ (-12) 4 (SOff 32%nat 0) nold);
        [cbn [sv_denot]; rewrite E32; unfold w64; rewrite Zbv_add_unsigned, Z.add_0_r; reflexivity
        | cbn; lia | cbn; lia | eapply val_mem_addr; [exact V4 | lia]].
    + unfold region_ok, R_GOT, flit8.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val tfibsegs _ _ _ 0x9fc38 8 (SLit 0xa1a88) 0xa1a88);
      [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VC1].
    + unfold region_ok, R_CELL, flit8.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val tfibsegs _ _ _ 0xa1a88 8 (SLit 0x98f3c) 0x98f3c);
      [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VC2].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_HDR, R_GOT, R_CELL, flit8.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !B9. repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms F_S2A atoms_ok].
    split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite B10. split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
    + rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
(* nothing in the segment has a write window, so the frame pins every byte (donor YF67.v:194-196) *)
assert (NOWR : forall (rs : smem) (ma mb : word -> option byte),
  frame_of (Ereg regs2 [w64 nold]) rs ma mb -> windows rs = windows (ss_mem SS_S2A) -> forall x, mb x = ma x).
{ intros rs ma mb HFx Hwin x. apply HFx. intros Hw.
  destruct (in_wrange_windows (Ereg regs2 [w64 nold]) rs (bv_unsigned x) Hw) as (b & lo & hi & Hin & Hrg).
  rewrite Hwin in Hin. vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
unfold cfg_at. change (w64 FS_RA_ALLOC) with (Z_to_bv 64 FS_RA_ALLOC).
srr_run_sh tfib_s2a_tbl_ok HS.
pose proof (NOWR _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ1. clear HF HFr.
srr_branch_sh tfib_s2a_tbl_ok HS.
-
(* `bltu s3, a0` 0x32a64 taken: n < nold, the `mv s3, a0` 0x32a68 is skipped, so a2 = s3 = n *)
assert (LT : n < nold).
{ rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc. rewrite !YF0x.U_zev by reflexivity.
  cbn [zev zalu_raw]. rewrite R19, R32. rewrite !Z.add_0_r.
  change (zcanon 0) with 0. change (Z.of_N 32) with 32.
  rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite ?(Z.mod_small nold) by lia.
  rewrite Z.lor_0_l. rewrite ?(zcanon_id nold), ?(zcanon_id n) by (unfold M64; lia). lia. }
srr_run_to_sh tfib_s2a_tbl_ok HS tfib_A_memcpy.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ2 : forall x, ms_mem msA x = mem2 x)
  by (intros x; rewrite (NOWR _ _ _ HF ltac:(vm_compute; reflexivity) x); apply MEQ1).
clear HF HFr.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hsh; cbn [ss_pc] in Hsh.
rewrite (Z.min_l n nold) by lia.
apply SRr_ret.
lazymatch goal with |- context [with_vm_backing _ ?mt _] =>
  unfold s2a_post; split; [reflexivity|]; exists (ms_regs msA), (ms_mem msA), mt end.
split. { unfold cfg_at. rewrite Hsh at 1. unfold w64, tfib_A_memcpy. reflexivity. }
split; [exact MEQ2|].
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11.
rreg HS (12%bv : bv 5) Q12. rreg HS (20%bv : bv 5) Q20.
split. { rewrite Q1. unfold w64, FS_RA_COPY. reflexivity. }
split. { rewrite Q10. exact E10. }
split. { rewrite Q11. exact E9. }
split. { rewrite Q12. exact E19. }
split. { rewrite Q20. exact E10. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr];
  [ lazymatch goal with |- getr _ ?rr = _ =>
      let R := fresh "R" in rreg HS (rr : bv 5) R; rewrite R;
      let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
      exact (ew_Ereg_nat regs2 [w64 nold] k rr eq_refl) end |]).
destruct Hr.
-
(* `bltu s3, a0` 0x32a64 not taken: nold <= n, `mv s3, a0` 0x32a68 runs, so a2 = s3 = nold *)
assert (GE : nold <= n).
{ rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc. revert Hc. rewrite !YF0x.U_zev by reflexivity.
  cbn [zev zalu_raw]. rewrite R19, R32. rewrite !Z.add_0_r.
  change (zcanon 0) with 0. change (Z.of_N 32) with 32.
  rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite ?(Z.mod_small nold) by lia.
  rewrite Z.lor_0_l. rewrite ?(zcanon_id nold), ?(zcanon_id n) by (unfold M64; lia). lia. }
srr_run_to_sh tfib_s2a_tbl_ok HS tfib_A_memcpy.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ2 : forall x, ms_mem msA x = mem2 x)
  by (intros x; rewrite (NOWR _ _ _ HF ltac:(vm_compute; reflexivity) x); apply MEQ1).
clear HF HFr.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hsh; cbn [ss_pc] in Hsh.
rewrite (Z.min_r n nold) by lia.
(* a2 = `or (slli (lhu p-14) 32) (lwu p-12)` = nold (donor YF67.v:238-247) *)
assert (DN : forall t, svpure t = true -> zev (rho_of (Ereg regs2 [w64 nold])) t = nold ->
  sv_denot (Ereg regs2 [w64 nold]) t = w64 nold)
  by (intros t Ht Hz; unfold w64; apply denot_by_zev; [exact Ht | lia | exact Hz]).
apply SRr_ret.
lazymatch goal with |- context [with_vm_backing _ ?mt _] =>
  unfold s2a_post; split; [reflexivity|]; exists (ms_regs msA), (ms_mem msA), mt end.
split. { unfold cfg_at. rewrite Hsh at 1. unfold w64, tfib_A_memcpy. reflexivity. }
split; [exact MEQ2|].
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11.
rreg HS (20%bv : bv 5) Q20.
split. { rewrite Q1. unfold w64, FS_RA_COPY. reflexivity. }
split. { rewrite Q10. exact E10. }
split. { rewrite Q11. exact E9. }
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) (Ereg regs2 [w64 nold]) _ msA 12%bv HS).
  lazymatch goal with |- context [sr_get ?sr ?r] =>
    let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end.
  apply DN; [reflexivity|]. cbn [zev zalu_raw]. rewrite R32. rewrite !Z.add_0_r.
  change (zcanon 0) with 0. change (Z.of_N 32) with 32.
  rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite ?(Z.mod_small nold) by lia.
  rewrite Z.lor_0_l. rewrite ?(zcanon_id nold) by (unfold M64; lia). reflexivity. }
split. { rewrite Q20. exact E10. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr];
  [ lazymatch goal with |- getr _ ?rr = _ =>
      let R := fresh "R" in rreg HS (rr : bv 5) R; rewrite R;
      let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in
      exact (ew_Ereg_nat regs2 [w64 nold] k rr eq_refl) end |]).
destruct Hr.
Qed.
End W.
