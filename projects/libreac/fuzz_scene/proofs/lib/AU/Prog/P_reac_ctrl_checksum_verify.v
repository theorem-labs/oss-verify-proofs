(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/CtrlChecksumVerify.v. *)
(* reac_ctrl_checksum_verify (fuzz_scene.asan-ubsan 0x839e8, 34 instructions): the contract of the ASan+UBSan
   build's code. It sums the 32 control-block bytes frame[18..50) of the caller's 50-byte frame
   object and returns 0 when the sum is 0 mod 256, else -1. Model: RcModel.blocksum
   (lib/Prog/RcModel.v:12). The walk pb_ctrl_checksum_verify is at the end of Section h, with a note on what it
   changes from the asan walk and how it closes the two UBSan checks.
   The asan-ubsan twin of lib/A/Prog/P_reac_ctrl_checksum_verify.v (at d9e17010c56):
   the module paths are lib.AU.Prog and every number below is re-measured in this image; the statement text is
   the asan one (the two UBSan checks below need no premise the asan statement does not have).
   The core module YCbq is Required from lib.AU (its asan-ubsan copy: it differs between scene's two images);
   every other core module from lib.Reusable, as in the asan file. U_NotTrap is lib/AU/U_NotTrap.v.
   Numbers: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f
   (projects/libreac/fuzz_scene/harness.yaml at c8557374ad2e); symbols from the .symtab of
   unstripped/fuzz_scene/fuzz_scene.asan-ubsan, whose bytes at 0x839e8..0x83a70 equal the pinned image's.
   - reac_ctrl_checksum_verify = 0x839e8, st_size 136 = 34 instructions (no compressed instruction).
   - LLVMFuzzerTestOneInput = 0x828a4 = the listing's base (SceneAddr.v:16 scene_text), so
     AF_reac_ctrl_checksum_verify = 0x839e8 - 0x828a4 = 0x1144 (SceneList.v:18; slots
     SceneList.v:1131-1164).
   - frame: addi sp,sp,-16 @0x839e8 (sd ra,8(sp) @0x839ec; ld ra,8(sp) @0x83a60; addi sp,sp,16 @0x83a64), so
     TCKV_STK = 16. The one call, jal __asan_report_load1 (0x5ab08) @0x83a50, is the error path, never taken.
   - the bytes it reads: addi a4,a0,18 @0x83a08 (REAC_CTRL_BLOCK_OFF), li a5,18 @0x83a0c and li a6,50 @0x83a10,
     the 32-turn loop 0x83a18..0x83a40 (lbu a7,0(a4) @0x83a2c; addi a5,a5,1 @0x83a30; bne a5,a6 @0x83a40 back to
     0x83a18): frame[18..50).
     50 = the caller's object, uint8_t frame[50] (projects/libreac/fuzz_scene/source/fuzz_scene.c:140,
     check_step; frame description "2 32 50 9 frame:140 128 36 5 p:143" at .rodata 0x14ef7), passed in s6 at
     the jal @0x836cc, return site 0x836d0; the statement takes any return address (afn_pre), so no return site
     is named.
   - the ASan check in the loop: srli a7,a0,3 @0x83a1c; add a7,a7,a2 @0x83a20; lb a7,0(a7) @0x83a24;
     bnez a7 @0x83a28 -> 0x83a48 (andi t0,a0,7; blt t0,a7 @0x83a4c back to 0x83a2c; else
     jal __asan_report_load1 @0x83a50). a2 is the shadow base: auipc a2 @0x839f8 (hi 0x9b9f8, the
     listing's hi 18), ld a2,72(a2) @0x839fc reads the GOT word 0x9ba40 (object 1), which holds
     0xa3af8 = __asan_shadow_memory_dynamic_address (object 16, the shadow-base cell, in .bss),
     ld a2,0(a2) @0x83a00 reads the cell.
   - the UBSan checks of frame + i (trap mode: each branches to the unimp 0xc0001073 @0x83a6c; there is no
     __ubsan_handle_* call):
     (1) beqz a0 @0x839f0 -> 0x83a6c (reac_ctrlblk.c:47): traps when f = 0.
     (2) not a3,a0 @0x83a04, then in each turn bltu a3,a5 @0x83a18 -> 0x83a6c (reac_ctrlblk.c:50, frame[i]):
         traps when 2^64 - 1 - f <u 18 + i (a5 = 18 + i, i = 0..31), that is when f + 18 + i >= 2^64.
     The premises exclude both: afobj puts [f, f + 50) in a live frame (frame_addr <= f and
     f + 50 <= frame_addr + fs_frame_bytes), and the core's frames_bounds, under the AR of afn_pre and the
     walk's AR_laws hypothesis, gives 4096 <= frame_addr and frame_addr + fs_frame_bytes <= alloc_ceiling,
     with alloc_ceiling <= 0x7fffff800000 (asan_consts). So 4096 <= f (no trap at (1)) and
     f + 49 < 2^47 < 2^64 (no trap at (2) in any turn).
   - the result: andi a0,a1,255 @0x83a54; seqz @0x83a58; addi a0,a0,-1 @0x83a5c. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase YC1h.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import U_NotTrap.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Fixpoint ckv_zsum (BS : list Z) (k : nat) : Z :=
match k with O => 0 | S k' => ckv_zsum BS k' + nth k' BS 0 end.
Lemma ckv_zsum_range : forall BS k, (forall j, (j < k)%nat -> 0 <= nth j BS 0 < 256) ->
0 <= ckv_zsum BS k <= 255 * Z.of_nat k.
Proof.
intros BS k. induction k as [|k IH]; intros H; cbn [ckv_zsum]; [lia|].
pose proof (H k ltac:(lia)). pose proof (IH ltac:(intros j Hj; apply H; lia)). lia.
Qed.
Lemma ckv_psum_map : forall BS k, (forall j, (j < k)%nat -> 0 <= nth j BS 0 < 256) ->
psum (map (Z_to_bv 8) BS) k = ckv_zsum BS k.
Proof.
intros BS k. induction k as [|k IH]; intros H; cbn [psum ckv_zsum]; [reflexivity|].
rewrite IH by (intros j Hj; apply H; lia). f_equal.
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. apply H. lia.
Qed.
Lemma ckv_fin : forall s, 0 <= s < 2 ^ 64 ->
alu64 ALU_ADD (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 s) (Z_to_bv 64 255)) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)) =
w64 (if s mod 256 =? 0 then 0 else -1).
Proof.
intros s Hs. unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small s) by lia. change (255 mod 2 ^ 64) with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
pose proof (Z.mod_pos_bound s 256 ltac:(lia)) as M.
rewrite (Z.mod_small (s mod 256)) by lia. change (1 mod 2 ^ 64) with 1. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
destruct (Z.eqb_spec (s mod 256) 0) as [E|E].
- rewrite E. reflexivity.
- replace (s mod 256 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Definition A_ctrl_checksum_verifyP : Z := BASE + AF_reac_ctrl_checksum_verify.
Definition TCKV_STK : Z := 16.
(* The shadow base: the model's SHADOW_OFF (lib/Reusable/YG0f.v), not an image number. *)
Definition CKV_SB : Z := SHADOW_OFF.
Section h.
Variable B : asyms.
Definition tctrl_checksum_verify_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (f : Z) (BS : list Z),
afn_pre SEGS B TCKV_STK ly S W regs mem md ch ->
getr regs 10 = w64 f ->
afobj SEGS B ly S W mem f 50 ->
garr8 SEGS (mrestrict (w_H W) mem) (f + 18) BS -> length BS = 32%nat ->
SRr SEGS W (cfg_at SEGS A_ctrl_checksum_verifyP regs mem md)
(apost_base SEGS B TCKV_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
getr regs' 10 = w64 (if blocksum (map (Z_to_bv 8) BS) =? 0 then 0 else -1))).
(* The walk: the asan walk of lib/A/Prog/P_reac_ctrl_checksum_verify.v (at 61afd7acb1d) over
   this listing. RET takes this listing's PL_scene (lib/AU/Prog/ScenePa.v:36); the shadow-base cell is object 16 and its
   GOT word object 1 (ScenePaLib.v pal_got_shadow / pal_cell, got_regionP / bcell_regionP); the stack region is 16 and
   the chunks are frame[18..50), as in the asan walk. The loop counts a5 up from 18 to 50 (bne a5,a6 @0x83a40); `go`
   unrolls it with the counter a literal in each turn. ra comes back from the stack (ld ra,8(sp) @0x83a60).
   The UBSan trap branches split the `go` loop with the taken side at the unimp @0x83a6c; `ckv_kill` refutes that side
   and `go` walks the other:
   (1) beqz a0 @0x839f0: branch_eq_U and U_atom on atom 10 (E10) turn the taken side into f = 0, against
       HR0 : 4096 <= f (afobj: frame_addr <= f; frames_bounds: 4096 <= frame_addr).
   (2) bltu a3,a5 @0x83a18, a3 = ~a0, a5 = 18 + i in turn i: kill_not_trap E10 HR of lib/AU/U_NotTrap.v
       (at bcd4b91d8d9), HR : 0 <= f /\ f + 49 < 2 ^ 64 (afobj: f + 50 <= frame end;
       frames_bounds: frame end <= alloc_ceiling; asan_consts: alloc_ceiling <= 0x7fffff800000).
   The engine decides (1) itself from the fact on atom 10 (lower bound 4096), so the walk stops only at (2), once per turn;
   the branch on (1) in `ckv_kill` covers the case where it stops there too. The false side's branch hypothesis is
   cleared (the state keeps the condition). The asan walk runs once; this one runs 33 times, so after each run it also
   rewrites wvb_collapse in the journal hypothesis (srr_norm_model rewrites only the goal): without that, the
   journal's model term doubles in each turn. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).
(* The symbolic state at the first slot: atoms 32..63 are the bytes frame[18..50),
   atom 64 the shadow base. *)
Definition CBx : sv := SOff 64 0.
Definition CBspan : Z * Z := (CKV_SB, CKV_SB + 2 ^ 44 - 1).
Definition ckv_chunk (j : nat) : YP09.chunk := YP09.mkChunk (18 + Z.of_nat j) (CVal 1 (SOff (32 + j) 0)).
Definition ckv_regions : smem :=
[ stack_region 16; got_regionP; bcell_regionP 64;
YP09.mkRegion (Some 10%nat) 0 50 0 0 (map ckv_chunk (seq 0 32)) ].
(* The bounds on sp (atom 2) and on a0 (atom 10, the frame object, below alloc_ceiling <= 0x7fffff800000 of
   asan_consts) are the model's, not image numbers. *)
Definition ckv_facts : facts :=
mkFacts ((2%nat, mkAF (2^46) (2^47) 4) :: (10%nat, mkAF 4096 140737479966720 3) ::
map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 32) ++ [(64%nat, mkAF CKV_SB CKV_SB 0)]) [] [].
Definition ss_ckv : sstate := mkSS AF_reac_ctrl_checksum_verify sr_atoms ckv_regions None ckv_facts.
Definition ckv_SH : list shent := [ mkSHE 10 0 50 ].
Definition ckv_extra (BS : list Z) : list word := map (Z_to_bv 64) (BS ++ [CKV_SB]).
Definition EC (regs : bvmap 5 word) (BS : list Z) : env := Eimg (Ereg regs (ckv_extra BS)).
Lemma afact_byte : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> afact_ok E n (mkAF 0 255 0).
Proof.
intros E n v H Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma ckv_ew : forall regs BS, length BS = 32%nat ->
(forall n, (32 <= n < 64)%nat -> ew (EC regs BS) n = Z_to_bv 64 (nth (n - 32) BS 0)) /\
ew (EC regs BS) 64 = Z_to_bv 64 CKV_SB.
Proof.
intros regs BS HL. unfold EC. split.
- intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
replace n with (32 + (n - 32))%nat at 1 by lia. rewrite ew_Ereg_extra. unfold ckv_extra.
rewrite map_nth. rewrite app_nth1 by lia. reflexivity.
- rewrite Eimg_low by (unfold A_TEXT; lia).
replace 64%nat with (32 + 32)%nat by lia. rewrite ew_Ereg_extra. unfold ckv_extra.
rewrite map_nth. rewrite app_nth2 by lia. rewrite HL. reflexivity.
Qed.
Lemma ckv_entry : forall ly S W (regs : bvmap 5 word) mem md ch (f : Z) (BS : list Z),
afn_pre SEGS B TCKV_STK ly S W regs mem md ch -> getr regs 10 = w64 f ->
afobj SEGS B ly S W mem f 50 -> garr8 SEGS (mrestrict (w_H W) mem) (f + 18) BS -> length BS = 32%nat ->
st_ok_pi SEGS VAL (EC regs BS) ss_ckv
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_ctrl_checksum_verifyP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ckv_SH (EC regs BS) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hf8 & HRA).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCKV_STK = 16) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hfin) as Hfimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 16 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (GB : forall j, (j < 32)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (f + 18 + Z.of_nat j) 1 (nth j BS 0) /\ 0 <= nth j BS 0 < 256)
by (intros j Hj; apply HBS; lia).
rewrite restrict_mkst_fx.
destruct (ckv_ew regs BS HLEN) as [EX E64].
set (E := EC regs BS) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ckv_extra BS)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Eo16 : ew E (A_OBJ 16) = Z_to_bv 64 (VAL (A_OBJ 16))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
change (fs_frame_bytes cid) with (fs_frame_bytes cid) in *.
split.
- unfold ss_ckv, A_ctrl_checksum_verifyP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ckv_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
[cbn [sv_denot]; rewrite Eo16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Eo16) by (pose proof (pa_val_range (A_OBJ 16)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 8 CBx CKV_SB);
[cbn [sv_denot CBx]; rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold CKV_SB, SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat f E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold ckv_chunk. destruct (GB j ltac:(lia)) as [Gv Gr].
apply (chunk_ok_val SEGS E _ f (18 + Z.of_nat j) 1 (SOff (32 + j) 0) (nth j BS 0)).
-- cbn [sv_denot]. rewrite (EX (32 + j)%nat) by lia. replace (32 + j - 32)%nat with j by lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-- zside.
-- zside.
-- rewrite Z.add_assoc. exact Gv.
+ apply pairwise_disjoint_of_extents. unfold ckv_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat f E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 16) (VAL (A_OBJ 16)) Eo16) by (pose proof (pa_val_range (A_OBJ 16)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hf4096 Hfceil Hflo Hfhi Hfimg C1 C3 WS Hstk0 HcellR HgcD HgotR. clear. unfold off_img. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ckv_facts f_atoms atoms_ok map seq app Nat.add].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia; change (2 ^ 3) with 8;
revert Hf4096 Hfceil Hflo Hfhi Hf8 C1; clear; intros; repeat split; lia|].
repeat match goal with
| |- afact_ok _ ?n (mkAF 0 255 0) /\ _ =>
split; [apply (afact_byte E n (nth (n - 32) BS 0)); [apply EX; lia | apply GB; lia] |]
end.
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E64, unsigned_lit_small by (unfold CKV_SB, SHADOW_OFF; lia).
rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, ckv_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 f 50 f 0 50 HRA).
+ unfold U, CBx. cbn [sv_denot]. rewrite E64, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold CKV_SB, SHADOW_OFF; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. revert Happ Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Theorem pb_ctrl_checksum_verify : tctrl_checksum_verify_spec.
Proof.
unfold tctrl_checksum_verify_spec.
intros ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ckv_entry ly S W regs mem md ch f BS HPRE H10 HFO HBS HLEN) as [HS SHOK].
pose proof (ajournal_init SEGS B TCKV_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hf8 & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Happ).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
(* The UBSan premises: HR0 for beqz a0 @0x839f0, HR for bltu a3,a5 @0x83a18 (f + 18 + i < 2 ^ 64 for i <= 31). *)
assert (HR0 : 4096 <= f) by (revert Hf4096 Hflo; clear; intros; lia).
assert (HR : 0 <= f /\ f + 49 < 2 ^ 64) by (revert Hf4096 Hfceil Hflo Hfhi C1; clear; intros; split; lia).
clear Hcid Hfal Hflo Hfhi Hf8 HRA Hf4096 Hfceil Happ C1 C2 C3 C4 C5.
assert (GB : forall j, (j < 32)%nat -> 0 <= nth j BS 0 < 256) by (intros j Hj; apply HBS; lia).
destruct (ckv_ew regs BS HLEN) as [EX E64].
remember (EC regs BS) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ckv_extra BS)) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ckv_extra BS)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
clear HE EL.
unfold cfg_at. change (w64 A_ctrl_checksum_verifyP) with (Z_to_bv 64 A_ctrl_checksum_verifyP).
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold apost_base; eexists ly, S, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ckv_extra BS) HS);
[eapply env_agree_trans; [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
| vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
cbn [ms_regs]; rewrite R10;
repeat (rewrite EX by lia); cbn [Nat.sub]; rewrite !alu64_add_lit;
lazymatch goal with |- context [alu64 ALU_AND (Z_to_bv 64 ?s) _] =>
replace s with (ckv_zsum BS 32) by (cbn [ckv_zsum]; lia) end;
rewrite ckv_fin by (pose proof (ckv_zsum_range BS 32 GB); lia);
unfold blocksum; rewrite (ckv_psum_map BS 32 GB); reflexivity
end in
let ckv_kill := idtac;
first
[ kill_not_trap E10 HR
| lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff 10 0)) (sv_denot _ (SLit 0)) = true |- _ =>
  exfalso; rewrite branch_eq_U in Hc; rewrite (U_atom Ex 10 f) in Hc;
  [ rewrite U_lit in Hc by (clear; lia); apply Z.eqb_eq in Hc; clear - Hc HR0; lia
  | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E10
  | clear - HR; lia ] end ] in
let clear_hc := idtac; repeat match goal with H : branch_taken _ _ _ = _ |- _ => clear H end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CBspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat rewrite wvb_collapse in HJ' end; srr_norm_model;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM CBx ckv_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K CBx CBspan ckv_SH (start K CBx CBspan ckv_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' CBspan; [first [ckv_kill | clear_hc; go] | first [ckv_kill | clear_hc; go]]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in
go.
Qed.
End h.
End f.
End d.
