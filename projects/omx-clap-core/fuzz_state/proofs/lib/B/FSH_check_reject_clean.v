(* check_reject_clean, image B: fs.asan-ubsan (sha256 5ac5ce0954f8...) entry 0x81b5c (lib/B/FSH_Base.v
   A_check_reject_clean; fs.c:188-202), 16 words over lib/B/YB1w.v's range 0x81b5c .. 0x81b9c (MEASURED, capstone):
   `addi sp, sp, -16; sd ra, 8(sp); sd s0, 0(sp); bnez a0, 0x81b90; addi a0, zero, -1; bne a1, a0, 0x81b90; mv s0, a2;
   jal fuzz_alloc_live; bne a0, s0, 0x81b90; ld ra, 8(sp); ld s0, 0(sp); addi sp, sp, 16; ret`, then the abort path
   `jal 0x5a1ec` (__asan_handle_no_return, the A twin's 0x5a17c) and `jal 0x8cca8` (abort, YB1w
   tfib_A_abort), and the padding word `unimp` at 0x81b98. The same code as
   image A's 0x81a60, moved by +0xfc.
   fuzz_alloc_live 0x82eec (lib/B/FSH_Base.v A_fuzz_alloc_live; alloc.c:118-121) is walked inline, 3 words:
   `auipc a0, 0x558; ld a0, -0x42c(a0); ret`, a0 := the 8 bytes at 0x5daac0 = lib/B/FSH_Base.v G_LIVE.
   UBSan: NO __ubsan_handle_* call in either range (every jal in them is listed above; the function only compares, and
   fuzz_alloc_live only loads). The three branches out of the straight line go to the abort path 0x81b90 and are ruled out
   by the premises: `bnez a0` (0x81b68) by a0 = 0, `bne a1, a0` (0x81b70) by a1 = SIZE_MAX, `bne a0, s0` (0x81b7c) by
   a2 = live and fs_glob's G_LIVE cell holding live.
   With a0 = 0, a1 = SIZE_MAX, a2 = live and the 8 bytes at G_LIVE = live (fs_glob), the engine decides all three
   branches not taken in one run (a0 and a1 enter as literals, the G_LIVE cell holds the atom of a2), and the function
   returns at 0x81b8c with memory changed only in its 16-byte stack window.
   The decode tables are lib/B/FSW_check_reject_clean_tbl.v and lib/B/FSW_fuzz_alloc_live_tbl.v.
   Ported from: lib/A/FSH_check_reject_clean.v (a working branch 3694074f8f1), the same walk over lib/B's walk
   kit lib/B/FSW_K.v (same lemma names) and lib/B's image files (YB1v, YB1w, FSH_Base, FSH_Rt, FSH_Fn_checks). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSH_Fn_checks FSW_K.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSW_check_reject_clean_tbl FSW_fuzz_alloc_live_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the code the walk runs: check_reject_clean's 16 words and fuzz_alloc_live's 3 *)
Definition crc_walk_tbl : ctable := Eval vm_compute in fal_tbl_on crc_tbl.
Lemma crc_walk_tbl_ok : table_ok tfibsegs crc_walk_tbl.
Proof.
assert (E : crc_walk_tbl = fal_tbl_on crc_tbl) by (vm_cast_no_check (eq_refl crc_walk_tbl)).
rewrite E. exact (fal_tbl_on_ok crc_tbl crc_tbl_ok).
Qed.

(* an 8-byte cell the walk reads at the absolute address a (base None, no write window), its value the env atom n
   (a Theorem Labs lane's FMW_fuzz_alloc_base.v fm_rcell / region_ok_fm_rcell; the A twin's fs_rcell) *)
Definition fs_rcell (a : Z) (n : nat) : YP09.region :=
  YP09.mkRegion None a (a + 8) 0 0 [YP09.mkChunk a (CVal 8 (SOff n 0))].
Lemma region_ok_fs_rcell : forall E (m : word -> option byte) a k v,
  val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  region_ok tfibsegs E m (fs_rcell a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, fs_rcell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.
(* a run whose write windows all lie at or above lo leaves memory below lo unchanged *)
Lemma same_below_wr : forall E rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a) -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E rs m m' lo HF Hw H64 x Hx. apply HF. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (Hw _ Hin). lia.
Qed.

(* the entry state: the 16-byte frame, the G_LIVE cell (B: 0x5daac0) holding a2's atom, a0 = 0 and a1 = SIZE_MAX as
   literals *)
Definition crc_ss0 : sstate :=
  mkSS A_check_reject_clean (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 11%bv (SLit SIZE_MAXZ))
    [fstk 16; fs_rcell G_LIVE 12] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* FSH_Fn_checks.v Section c's image facts; the walk does not use them *)
Hypothesis IMG : fs_img_facts tfibsegs B.

(* SK is generic: the walk never reaches the sink, so the theorem holds at B's sink FSH_Base.fsB_sink_head too *)
Theorem check_reject_clean_proof : @check_reject_clean_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch live peak cnt fail HPRE _ Hglob H10 H11 H12.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
destruct HPRE as [HAPU _].
pose proof (fsw_sp B _ ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HAPU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _ & _ & _ & _ & Hpres & _).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HAPU) as HARU.
pose proof Hglob as (GL & _ & _ & _ & Hlp & Hp64 & _).
assert (FS : STK_check_reject_clean = 16) by reflexivity. rewrite FS in Hceil, Hpres.
assert (Usp0 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 live) by (rewrite (ew_Ereg_nat regs [] 12 12%bv eq_refl); exact H12).
assert (HS : st_ok tfibsegs (Ereg regs []) crc_ss0
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_check_reject_clean) mem (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold crc_ss0. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H10; reflexivity]
    | intros Hx; discriminate Hx | rewrite H11; reflexivity].
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (region_ok_stack tfibsegs (Ereg regs []) _ 2 (spZ regs) (- 16)); [exact Usp0 | lia | lia |].
      intros a Ha. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly S U W mem md a HARU); [lia|]. apply Hpres. lia.
    + apply (region_ok_fs_rcell (Ereg regs []) _ G_LIVE 12 live); [exact GL | exact E12 | lia | unfold G_LIVE; lia
      | unfold G_LIVE; lia].
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, fstk, fs_rcell. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp0.
    right. unfold G_LIVE. lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp0.
    change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]]. }
pose proof (ajournal_init tfibsegs B STK_check_reject_clean [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by exact Usp0.
unfold cfg_at. change (w64 A_check_reject_clean) with (Z_to_bv 64 A_check_reject_clean).
(* ---- 0x81b5c .. fuzz_alloc_live 0x82eec .. 0x82ef4 .. the return at 0x81b8c: one run; the three branches to the
   abort path 0x81b90 (0x81b68, 0x81b70, 0x81b7c) are decided not taken by the engine ---- *)
fsw_aj_runU crc_walk_tbl_ok HS HJ HARU.
{ awr_ok_tac. exact Usp. }
assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
{ apply (same_below_wr E (ss_mem crc_ss0) mem (ms_mem ms) alloc_ceiling HF); [|lia].
  intros a (r & Hin & Hr). unfold crc_ss0 in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [fstk fs_rcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr | ]; lia. }
pose proof (fsw_reg_atom _ regs [] _ ms 1%bv 1%bv 1 HS ltac:(vm_compute; reflexivity) eq_refl) as R1.
eapply (SRr_ret_at tfibsegs crc_walk_tbl crc_walk_tbl_ok fs_wx); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2.
assert (Hpc : v_jalr (YK11.getr (ms_regs ms) 1) 0 = YK11.getr regs 1) by (rewrite R1; exact Hra).
rewrite Hpc. unfold fpostU.
do 5 eexists. split; [reflexivity|].
split; [apply (ajournal_materialize tfibsegs B LAWS HSL); exact HJ|].
split; [exact (proj1 (proj2 HARU))|].
split; [exact (proj2 (proj2 HARU))|].
split; [eapply (aregs_preserved_of_st_ok tfibsegs _ E _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
exact (fs_glob_below W mem (ms_mem ms) live peak cnt fail SB Hglob).
Qed.
End W.
