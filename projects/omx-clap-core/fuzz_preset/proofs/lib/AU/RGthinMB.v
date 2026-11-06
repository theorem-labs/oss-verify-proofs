(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFfi.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/AFfi.v, with its module paths and module names changed; 392 of its 466 lines of code are new or changed and 398 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S4.v, with its module paths, addresses and numbers changed; 151 of its 201 lines of code are new or changed and 416 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinM.v (hub 66a127cb11e, blob 8b4e2d34d15a) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), module paths and every image numeral moved by symbol + offset; record, the internal file A5.md. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGthinM.v (hub 96e1d2182ec6, blob 6c09cb5eddca), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1h YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RGthinKB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition flit8 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SLit v))].
Definition c8 (o : Z) (e : sv) : YP09.chunk := YP09.mkChunk o (CVal 8 e).

Definition R_HDR : YP09.region := YP09.mkRegion (Some 9%nat) (-16) (-8) 0 0
[YP09.mkChunk (-16) (CVal 1 (SLit 2)); YP09.mkChunk (-14) (CVal 2 (SLit 0)); YP09.mkChunk (-12) (CVal 4 (SOff 32 0))].
Definition F2A : facts := mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition S2A : sstate := mkSS RT_RA_A sr_atoms [R_HDR; flit8 RT_GOT_M RT_REAL_M; flit8 RT_REAL_M RT_PCM] None F2A.
Definition S2B : sstate := mkSS RT_RA_M sr_atoms [] None (mkFacts [] [] []).

Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma apresent_wr : forall (H : word -> bool) (mem : word -> option byte) a,
apresent H mem a -> writable_at tfibsegs (mrestrict H mem) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma rw_wr : forall (m : word -> option byte) a, 0xa2000 <= a < 0x601000 -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at. rewrite <- tsegs_tfasegs. apply tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
Section W.
Variable W : world tfibsegs.
Variable md : Model.
Local Notation H := (w_H W).

Definition m2a_post (regs : bvmap 5 word) (mem : word -> option byte) (p q len : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsM memM mat,
c' = mkCfg (mkst regsM (w64 RT_PCM) memM (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall x, memM x = mem x) /\
getr regsM 1 = w64 RT_RA_M /\ getr regsM 10 = w64 q /\ getr regsM 11 = w64 p /\ getr regsM 12 = w64 len /\
getr regsM 19 = w64 len /\ getr regsM 20 = w64 q /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsM r = getr regs r).

Ltac reg_ent HS r k :=
let R := fresh "R" in rreg HS r R; rewrite R; exact (ew_Ereg_nat _ _ k r eq_refl).

Lemma m2a : forall (regs : bvmap 5 word) (mem : word -> option byte) (p q n nold : Z),
getr regs 9 = w64 p -> getr regs 10 = w64 q -> getr regs 19 = w64 n ->
16 <= p < 2 ^ 63 -> (p <= 0x10000 \/ 0x601000 + 16 <= p) -> 4096 <= q <= 2 ^ 47 -> 0 <= n < 2 ^ 32 -> 0 <= nold < 2 ^ 32 ->
val_mem tfibsegs (mrestrict H mem) (p - 16) 1 2 -> val_mem tfibsegs (mrestrict H mem) (p - 14) 2 0 ->
val_mem tfibsegs (mrestrict H mem) (p - 12) 4 nold ->
val_mem tfibsegs (mrestrict H mem) RT_GOT_M 8 RT_REAL_M -> val_mem tfibsegs (mrestrict H mem) RT_REAL_M 8 RT_PCM ->
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_A) mem (seg_rom tfibsegs)) md) (m2a_post regs mem p q (Z.min n nold)).
Proof.
intros regs mem p q n nold G9 G10 G19 Hp HPI Hq Hn Hnold V0 V2 V4 VC1 VC2.
pose proof Hwx_tfa as Hwx.
assert (E9 : bv_unsigned (ew (Ereg regs [w64 nold]) 9) = p).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), G9. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs [w64 nold]) 32 = w64 nold) by exact (ew_Ereg_extra regs [w64 nold] 0).
assert (E10 : ew (Ereg regs [w64 nold]) 10 = w64 q) by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (R19 : rho_of (Ereg regs [w64 nold]) 19%nat = n).
{ unfold rho_of. rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), G19. unfold w64. apply unsigned_lit_small. lia. }
assert (R32 : rho_of (Ereg regs [w64 nold]) 32%nat = nold).
{ unfold rho_of. rewrite E32. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok tfibsegs (Ereg regs [w64 nold]) S2A (restrict (w_H W) (mkst regs (w64 RT_RA_A) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S2A. change (w64 RT_RA_A) with (Z_to_bv 64 RT_RA_A). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold region_ok, R_HDR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val tfibsegs _ _ _ (-16) 1 (SLit 2) 2); [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact V0 | lia]].
      * apply (chunk_ok_val tfibsegs _ _ _ (-14) 2 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact V2 | lia]].
      * apply (chunk_ok_val tfibsegs _ _ _ (-12) 4 (SOff 32 0) nold); [| cbn; lia | cbn; lia | eapply val_mem_addr; [exact V4 | lia]].
        cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. f_equal; lia.
    + unfold region_ok, flit8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold RT_GOT_M, RT_REAL_M in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ _ 0xa2878 8 (SLit 0xa46c8) 0xa46c8); [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact VC1 | lia]].
    + unfold region_ok, flit8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      unfold RT_REAL_M, RT_PCM in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ _ 0xa46c8 8 (SLit 0x9bb04) 0x9bb04); [reflexivity | cbn; lia | cbn; lia | eapply val_mem_addr; [exact VC2 | lia]].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_HDR, flit8.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite !E9. unfold RT_GOT_M, RT_REAL_M. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms F2A atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E32. unfold w64. rewrite !unsigned_lit_small by lia.
    split; [split; [lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|].
    split; [split; [lia | split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]]|]. exact I. }
change (w64 RT_RA_A) with (Z_to_bv 64 RT_RA_A) in HS |- *.
assert (NOWR : forall (ma mb : word -> option byte), frame_of (Ereg regs [w64 nold]) (ss_mem S2A) ma mb -> forall x, mb x = ma x).
{ intros ma mb HFx x. apply HFx. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [fst snd] in Hrg; lia|]). destruct Hin. }
srr_run_sh rt_tbl_ok HS.
pose proof (NOWR _ _ HF) as MEQ1. clear HF HFr.
srr_branch_sh rt_tbl_ok HS.
-
  assert (LT : n < nold).
  { rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc. rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. rewrite R19, R32.
    rewrite !Z.add_0_r. change (zcanon 0) with 0. rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite ?(zcanon_id n) by (unfold M64; lia).
    rewrite Z.lor_0_l. rewrite ?(zcanon_id nold) by (unfold M64; lia). lia. }
  srr_run_to_sh rt_tbl_ok HS RT_PCM.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
  assert (MEQ2 : forall x, ms_mem msA x = mem x) by (intros x; rewrite (NOWR _ _ HF x); apply MEQ1). clear HF HFr.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hsh. cbn [ss_pc] in Hsh. rewrite Hsh.
  rewrite (Z.min_l n nold) by lia.
  apply SRr_ret. split; [reflexivity|]. exists (ms_regs msA), (ms_mem msA). eexists.
  split; [reflexivity|]. split; [exact MEQ2|].
  split. { let R := fresh "R" in rreg HS (1%bv : bv 5) R; rewrite R; reflexivity. }
  split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E10. }
  split. { let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R, (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact G9. }
  split. { let R := fresh "R" in rreg HS (12%bv : bv 5) R; rewrite R, (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact G19. }
  split. { let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R, (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact G19. }
  split. { let R := fresh "R" in rreg HS (20%bv : bv 5) R; rewrite R; exact E10. }
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
  destruct Hr.
-
  assert (GE : nold <= n).
  { rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc. revert Hc. rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. rewrite R19, R32.
    rewrite !Z.add_0_r. change (zcanon 0) with 0. rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite ?(zcanon_id n) by (unfold M64; lia).
    rewrite Z.lor_0_l. rewrite ?(zcanon_id nold) by (unfold M64; lia). lia. }
  srr_run_to_sh rt_tbl_ok HS RT_PCM.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
  assert (MEQ2 : forall x, ms_mem msA x = mem x) by (intros x; rewrite (NOWR _ _ HF x); apply MEQ1). clear HF HFr.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hsh. cbn [ss_pc] in Hsh. rewrite Hsh.
  rewrite (Z.min_r n nold) by lia.
  assert (ZN : forall t, svpure t = true -> zev (rho_of (Ereg regs [w64 nold])) t = nold -> sv_denot (Ereg regs [w64 nold]) t = w64 nold)
    by (intros t Ht Hz; apply denot_by_zev; [exact Ht | lia | exact Hz]).
  apply SRr_ret. split; [reflexivity|]. exists (ms_regs msA), (ms_mem msA). eexists.
  split; [reflexivity|]. split; [exact MEQ2|].
  split. { let R := fresh "R" in rreg HS (1%bv : bv 5) R; rewrite R; reflexivity. }
  split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact E10. }
  split. { let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R, (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact G9. }
  split.
  { rewrite (st_ok_reg_denot (w_H W) _ _ msA 12%bv HS).
    lazymatch goal with |- context [sr_get ?sr ?r] => let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end.
    apply ZN; [reflexivity|]. cbn [zev zalu_raw]. rewrite R32. change (zcanon 0) with 0. rewrite !Z.add_0_r.
    rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite Z.lor_0_l. rewrite ?Z.add_0_r. rewrite !(zcanon_id nold) by (unfold M64; lia). reflexivity. }
  split.
  { rewrite (st_ok_reg_denot (w_H W) _ _ msA 19%bv HS).
    lazymatch goal with |- context [sr_get ?sr ?r] => let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end.
    apply ZN; [reflexivity|]. cbn [zev zalu_raw]. rewrite R32. change (zcanon 0) with 0. rewrite !Z.add_0_r.
    rewrite ?(zcanon_id nold) by (unfold M64; lia). rewrite Z.lor_0_l. rewrite ?Z.add_0_r. rewrite !(zcanon_id nold) by (unfold M64; lia). reflexivity. }
  split. { let R := fresh "R" in rreg HS (20%bv : bv 5) R; rewrite R; exact E10. }
  intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
  destruct Hr.
Qed.

Definition m2b_post (regs : bvmap 5 word) (mem : word -> option byte) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD mat,
c' = mkCfg (mkst regsD (w64 RT_PCD) memD (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall x, memD x = mem x) /\
getr regsD 1 = w64 RT_RA_D /\ getr regsD 10 = getr regs 18 /\ getr regsD 11 = getr regs 9 /\
getr regsD 12 = w64 0 /\ getr regsD 13 = w64 0 /\ getr regsD 14 = getr regs 8 /\ getr regsD 15 = w64 1 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsD r = getr regs r).

Lemma m2b : forall (regs : bvmap 5 word) (mem : word -> option byte),
SRr tfibsegs W (mkCfg (mkst regs (w64 RT_RA_M) mem (seg_rom tfibsegs)) md) (m2b_post regs mem).
Proof.
intros regs mem. pose proof Hwx_tfa as Hwx.
assert (HS : st_ok tfibsegs (Ereg regs []) S2B (restrict (w_H W) (mkst regs (w64 RT_RA_M) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold S2B. change (w64 RT_RA_M) with (Z_to_bv 64 RT_RA_M). apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
change (w64 RT_RA_M) with (Z_to_bv 64 RT_RA_M) in HS |- *.
srr_run_to_sh rt_tbl_ok HS RT_PCD.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ : forall x, ms_mem msA x = mem x).
{ intros x. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & _). destruct Hin. }
clear HF HFr.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS eq_refl) as Hsh. cbn [ss_pc] in Hsh. rewrite Hsh.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs msA), (ms_mem msA). eexists.
split; [reflexivity|]. split; [exact MEQ|].
split. { let R := fresh "R" in rreg HS (1%bv : bv 5) R; rewrite R; reflexivity. }
split. { let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; exact (ew_Ereg_nat _ _ 18 18%bv eq_refl). }
split. { let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; exact (ew_Ereg_nat _ _ 9 9%bv eq_refl). }
split. { let R := fresh "R" in rreg HS (12%bv : bv 5) R; rewrite R; reflexivity. }
split. { let R := fresh "R" in rreg HS (13%bv : bv 5) R; rewrite R; reflexivity. }
split. { let R := fresh "R" in rreg HS (14%bv : bv 5) R; rewrite R; exact (ew_Ereg_nat _ _ 8 8%bv eq_refl). }
split. { let R := fresh "R" in rreg HS (15%bv : bv 5) R; rewrite R; reflexivity. }
intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ lazymatch goal with |- getr _ ?rr = _ =>
  let k := eval vm_compute in (Z.to_nat (bv_unsigned rr)) in reg_ent HS rr k end |]).
destruct Hr.
Qed.
End W.
End c.
