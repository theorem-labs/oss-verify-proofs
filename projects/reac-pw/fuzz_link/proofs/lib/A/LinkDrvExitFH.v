(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths, module names and addresses changed; 190 of its 244 lines of code are new or changed and 1621 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE20 AE7f AE22.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE3e AE3f AE3g AE6g AE2p AE3i AE3h AE3m AE23 AE36 AE37.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1u AD1w AD1o AD1k.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile LinkExitFile LinkDrvExitF LinkDrvExitFT.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The exit walk before __stdio_exit's open-file loop: A_EXIT 0x90688 (jal exit) to 0x9688c, where the
   open-file head has just been read into s0 and the loop's branch is about to be taken because on link that
   head is the memory FILE f, not 0.

   The regions are AE23.v's exit regions with the open-file head carried as the atom 36, and with stdout's
   and stderr's FILE write windows emptied: the walk does not write either FILE before the loop, and with the
   windows empty the frame of each run keeps their bytes, which is what carries the caller's stdout clause
   and the stderr cells of exf_mid across the walk without putting their fields in the state. *)

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition exf_hregions : smem := Eval vm_compute in
  map (fun r => if Z.eqb (YP09.r_lo r) F_STDOUT
                then YP09.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT F_STDOUT []
                else if Z.eqb (YP09.r_lo r) F_STDERR
                then YP09.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR F_STDERR []
                else r) (exf_regions []).

Definition ssf_H : sstate := mkSS A_EXIT sr_atoms exf_hregions None ex_facts0.

(* the phases are AE23.v's, with the havoc bases moved up by one because the atom 36 is the open-file head *)
Definition hH_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ssf_H).
Definition hH_st1c : sstate := Eval vm_compute in
  YP06.add_cond hH_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0))).
Definition hH_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL hH_st1c).
Definition hH_af2 : sstate := Eval vm_compute in vf_after_icpt 37 hH_st2 X1_RA OSP_X1 0 [].
Definition hH_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL hH_af2).
Definition hH_af3 : sstate := Eval vm_compute in vf_after_icpt 53 hH_st3 X23_RA OSP_X23 0 [].
Definition hH_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL hH_af3).
Definition hH_af4 : sstate := Eval vm_compute in vf_after_icpt 69 hH_st4 X23_RA OSP_X23 0 [].
Definition hH_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL hH_af4).

(* The five phases, measured. They are the released walk's: the thread-id branch at 0x90dbc, then the three
   intercepted calls 0x7178c (X1), 0x31328 (X3) and 0x8864c (X2, the module destructor that unregisters the
   globals and keeps no AR), and then the run that ends at 0x9688c on the open-file branch. That last stop is
   the one thing this walk does not share with AE23.v: there the head reads 0 and the branch is decided, here
   it reads the atom 36, so the run stops with the branch open and the caller supplies s0 = f. *)
Lemma hH_run1 : sym_runN tfibsegs tfibmusl_tbl FUEL ssf_H =
  (hH_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))).
Proof. vm_compute. reflexivity. Qed.
Lemma hH_run2 : sym_runN tfibsegs tfibmusl_tbl FUEL hH_st1c = (hH_st2, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma hH_run3 : sym_runN tfibsegs tfibmusl_tbl FUEL hH_af2 = (hH_st3, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma hH_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL hH_af3 = (hH_st4, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Lemma hH_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL hH_af4 =
  (hH_st5, RS_stopped (SR_branch BC_NE (SOff 36 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.

(* the three calls are the released ones, and the walk ends where the loop begins *)
Lemma hH_pc2 : ss_pc hH_st2 = X1_PC. Proof. vm_compute. reflexivity. Qed.
Lemma hH_pc3 : ss_pc hH_st3 = X3_PC. Proof. vm_compute. reflexivity. Qed.
Lemma hH_pc4 : ss_pc hH_st4 = X2_PC. Proof. vm_compute. reflexivity. Qed.
Lemma hH_pc5 : ss_pc hH_st5 = A_SX_LOOP. Proof. vm_compute. reflexivity. Qed.

(* the first region and the rest at each call site, for vf_icpt_xcall *)
Definition hH_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem hH_st2).
Definition hH_rest2 : smem := Eval vm_compute in tl (ss_mem hH_st2).
Definition hH_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem hH_st3).
Definition hH_rest3 : smem := Eval vm_compute in tl (ss_mem hH_st3).
Definition hH_r04 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem hH_st4).
Definition hH_rest4 : smem := Eval vm_compute in tl (ss_mem hH_st4).

(* AE23's three facts about the regions after the first, for this walk's skeleton. It differs from AE23's in
   the two write windows this walk empties, and those are the arms that close by exfalso. *)
Definition exf_hrest : smem := Eval vm_compute in tl exf_hregions.

Lemma exf_hrest_ok : forall E (rest : smem) tp,
skeleton rest = skeleton exf_hrest -> bv_unsigned (ew E 4) = tp -> 168 <= tp -> tp <= 2 ^ 43 ->
forall r, In r rest -> exists bz, base_val E (YP09.r_base r) = bz /\ 0 <= bz + YP09.r_lo r /\ bz + YP09.r_hi r <= 2 ^ 43.
Proof.
intros E rest tp Hsk H4 Htp1 Htp2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold exf_hrest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi].
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val]; rewrite ?H4; eexists; split; [reflexivity|];
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; lia |]).
destruct Hin.
Qed.

Lemma exf_hrest_w : forall E (rest : smem), skeleton rest = skeleton exf_hrest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold exf_hrest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha;
first [ apply (wseg_writable m 0x651c60 0x130 a wz_atexit); lia
| apply (wseg_writable m 0x651e80 4 a wz_exitlock); lia
| exfalso; unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; lia ] |]).
destruct Hin.
Qed.

Lemma exf_hrest_range : forall E (rest : smem) tp,
skeleton rest = skeleton exf_hrest -> bv_unsigned (ew E 4) = tp ->
forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
(is_canary_region r = true /\ A_GOT_canary <= a < A_GOT_canary + 8) \/ ex_cell_range tp a.
Proof.
intros E rest tp Hsk H4 r a Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold exf_hrest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. unfold ex_cell_range, vo_file, vf_file.
repeat (destruct Hin as [Hq|Hin]; [symmetry in Hq; injection Hq; intros; subst; cbn [base_val] in Ha; rewrite ?H4 in Ha;
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *;
first [ left; split; [vm_compute; reflexivity | lia] | right; lia ] |]).
destruct Hin.
Qed.

Ltac exf_pc HC a n v := pose proof (exf_cell _ a n v HC ltac:(vm_compute; reflexivity)).

Ltac exf_cells HC :=
  exf_pc HC 0xa2688 8%N 0xa1370; exf_pc HC 0xa2690 8%N 0xa1360;
  exf_pc HC 0xa1360 8%N 0x8864c; exf_pc HC 0xa1368 8%N 0x31328;
  exf_pc HC 0xa19a0 8%N 0x90c6c; exf_pc HC 0xa19a8 8%N 0;
  exf_pc HC 0xa6088 8%N 0xa5fa0; exf_pc HC 0xa6178 8%N 0xa6090; exf_pc HC 0xa6268 8%N 0xa6180;
  exf_pc HC 0x651c64 4%N 0; exf_pc HC 0x651c78 8%N 0;
  exf_pc HC 0x651c80 8%N 0x90d34; exf_pc HC 0x651c88 8%N 0x90d34;
  exf_pc HC 0x651d80 8%N 0x7178c; exf_pc HC 0x651d88 8%N 0x82154;
  exf_pc HC 0x5dca94 1%N 0; exf_pc HC 0x651ea3 1%N 0; exf_pc HC 0x652300 4%N 0;
  exf_pc HC 0xa6188 8%N 0; exf_pc HC 0xa6190 8%N 0; exf_pc HC 0xa61a8 8%N 0; exf_pc HC 0xa61b8 8%N 0;
  exf_pc HC 0xa620c 4%N 0xffffffff;
  exf_pc HC 0xa5fa8 8%N 0; exf_pc HC 0xa5fb0 8%N 0; exf_pc HC 0xa602c 4%N 0xffffffff.

Local Ltac WSEG := first
[ apply (wseg_writable _ 0x651c60 0x130); [exact wz_atexit | lia | lia | lia | lia]
| apply (wseg_writable _ 0x651e80 4); [exact wz_exitlock | lia | lia | lia | lia] ].
Local Ltac CELL :=
  (eapply (chunk_ok_val tfibsegs _ _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; assumption]).

(* the state at A_EXIT, from the facts the exit leaf carries *)
Lemma exf_entryH : forall (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (usp code f tid cval sew wp : Z),
spZ regs = usp - 48 -> usp mod 16 = 0 -> sp_window_lo <= usp <= sp_window_hi ->
getr regs 4%bv = w64 TFIB_TPX ->
(forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
cells_are exf_consts (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_TPX - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x652308 8 f -> 0 <= f < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x651c60 1 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x651c68 4 2 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x651c70 8 0x651c78 ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0x651e80 4 0 ->
st_ok tfibsegs (exf_env regs tid cval wp sew f code) ssf_H
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_EXIT) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem usp code f tid cval sew wp Hsp U16 [Ulo Uhi] H4 Hpres HC Mtid Rtid Mgot Mcan Rcan Mofl Rf
  Mx1 Mx2 Mx3 Mx4.
unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
assert (HVF : VF_STK = 9104) by reflexivity.
exf_cells HC.
unfold F_STDOUT, F_STDERR, FILE_SZ, A_GOT_canary, A_canary, TFIB_TPX in *.
rewrite restrict_mkst_fx. unfold ssf_H, exf_hregions.
set (E := exf_env regs tid cval wp sew f code) in *.
assert (E2 : bv_unsigned (ew E 2) = usp - 48)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
assert (E4 : bv_unsigned (ew E 4) = 0x631c10)
  by (subst E; unfold exf_env; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 1)).
assert (E36 : ew E 36 = Z_to_bv 64 f) by (subst E; unfold exf_env; exact (ew_Ereg_extra regs _ 4)).
apply (entry_st_ok_full tfibsegs);
change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew; Z_to_bv 64 f; Z_to_bv 64 code]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (region_ok_stack tfibsegs E _ 2 (usp - 48) (- VF_STK)); [exact E2 | lia | lia |].
    intros a Ha. apply AE2y.apresent_writable. apply Hpres. lia.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_nil.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_nil.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | zside | zside | rewrite Z.add_0_l; exact Mgot].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
     rewrite Z.add_0_l; exact Mcan].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; WSEG |].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil; CELL.
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    first [ CELL
          | eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ f);
            [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
             rewrite Z.add_0_l; exact Mofl] ].
  + unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E4. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    constructor; [|constructor].
    eapply (chunk_ok_val tfibsegs E _ 0x631c10 (-168) 4 _ tid);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mtid].
- apply pairwise_disjoint_of_extents. unfold exf_hregions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. repeat split; try lia.
Qed.
End p.
