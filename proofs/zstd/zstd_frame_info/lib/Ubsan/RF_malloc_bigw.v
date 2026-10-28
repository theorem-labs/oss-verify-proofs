(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp F_malloc_bigw.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMalloc_fp RF_enframe RMallocKit_A2.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac raw_store_finishR A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rzeros_bytes_at : forall m x k, 0 <= x -> x + Z.of_nat k <= 2^64 ->
  (forall o, 0 <= o < Z.of_nat k -> bytes_at usegs m (x + o) [b8 0]) -> bytes_at usegs m x (zeros k).
Proof.
  intros m x k X0 XK H. Local Ltac2 Set LiaHints.tbl := fun () => "0040>22362493461.7 33234766905.9 55686273877.1056087383078.7 00000400800<00@S2XKS2HiS2HiS2X0".
split; [lia|]. split; [unfold zeros; rewrite repeat_length; lia|].
  intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  destruct (H (Z.of_nat i) ltac:(lia)) as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB.
  rewrite Z.add_0_r in HB. exact HB.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma lor_land_2048_4064 x : 0 <= x -> Z.lor (Z.land x 18446744073709549568) 4064 = Z.lor (Z.land x 18446744073709547520) 4064.
Proof.
  intros Hx. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec, !Z.land_spec.
  change 18446744073709549568 with (Z.ldiff (Z.ones 64) (Z.ones 11)). change 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)).
  Local Ltac2 Set LiaHints.tbl := fun () => "0070>16131084811.1117210504373.5 24928565326.9 29317573413.5 35497642613.5 6160747397.5  64522633523.1100000700800D00E00F00G00NS2H12H3SS2H12H22Hi1HSSSS2H12H2".
rewrite !Z.ldiff_spec, !Z.testbit_ones by lia.
  assert (T4064 : Z.testbit 4064 i = ((5 <=? i) && (i <? 12))).
  { change 4064 with (Z.ldiff (Z.ones 12) (Z.ones 5)). rewrite Z.ldiff_spec, !Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 12); destruct (Z.ltb_spec i 5); destruct (Z.leb_spec 5 i); cbn; try reflexivity; lia. }
  rewrite T4064.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i 64); destruct (Z.ltb_spec i 11); destruct (Z.ltb_spec i 12); destruct (Z.leb_spec 5 i); cbn;
    rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rbig_word_eq rid n : 0 <= n < 2^32 ->
  Z.lor (Z.land (n + 4064 + 51) 18446744073709549568) 4064 = meta_word (big_meta rid n).
Proof.
  intros Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0090=27293495702.733581900583.436644237772.452952359618.455269914620.459197466707.559891952086.663681228783.78850913373.7 00000100200600:00>00?00@00C00FSSS2HnS2HnS2HnSSS1HS1H".
rewrite lor_land_2048_4064 by lia. rewrite land_m4096 by lia.
  unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  replace (n + 4064 + 51) with (n + 4115) by lia.
  assert (D : Z.land (n + 4115 - (n + 4115) mod 4096) 4064 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    replace (n + 4115 - (n + 4115) mod 4096) with (4096 * ((n + 4115) / 4096)) by (OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    destruct (Z.lt_ge_cases i 12).
    - rewrite Z.mul_comm. change 4096 with (2 ^ 12). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit 4064 i) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma le4_sxv_succ c : 0 <= c -> le4 (Z_to_bv 64 (bv_unsigned (wz (sxv c)) + 1)) = le4 (wz (u32 (c + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite (wz_unsigned (sxv c)) by apply sxv_range.
  rewrite unsigned_lit_wrap. Local Ltac2 Set LiaHints.tbl := fun () => "0030=2589537086.3 38715782554.38929208055.3 000001002003SSS".
rewrite (wz_unsigned (u32 (c + 1))) by (unfold u32; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  unfold u32. rewrite (MallocRep.mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma le4_swrap_succ c0 : 0 <= c0 < 2^32 -> le4 (Z_to_bv 64 (bv_swrap 32 c0 + 1)) = le4 (wz (u32 (c0 + 1))).
Proof.
  intros Hc. apply le4_congr. rewrite unsigned_lit_wrap. Local Ltac2 Set LiaHints.tbl := fun () => "0020=54426810295.38929208055.3 000001002SS".
rewrite (wz_unsigned (u32 (c0 + 1))) by (unfold u32; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  unfold u32, bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rbig_fail1_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom usegs)
                        /\ stk usegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14efc) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. Local Ltac2 Set LiaHints.tbl := fun () => "0080>1800609155.54 24638473347.5227900861085.4538446806799.5143988483203.5351711223320.4454243526019.5264997134979.5500000100200600700800900:00;SSS2LOSSSSS".
step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rbig_fail2b_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw s1w rav s0v s1v s2v s3v s4v : word) F fc (m : mem) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> 48 <= bv_unsigned sp ->
  evt usegs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc rav) fc None m (seg_rom usegs)
                        /\ stk usegs m lo (bv_unsigned sp))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw s1w a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x150c8) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros FR ST LO SP48.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. Local Ltac2 Set LiaHints.tbl := fun () => "0080>1800609155.54 24638473347.5427904922626.4738446806799.5343988483203.5351711223320.4654243526019.5464997134979.5500000100200600700800900:00;SSS2LOSSSSS".
step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split; [reflexivity| exact ST].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rbig_fail2a_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw ndw : word) F fc (m : mem),
  rw_cells usegs m RMLOCK [C4 (wz 0)] ->
  evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x150c8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) xw ndw a2 a3 a4 a5 a6 a7
                                     s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs))
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK) (wz 0) a1 a2 a3 a4 a5 a6 a7
               s2 ndw xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14ff0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros LK. unfold RMLOCK in *.
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  step. step. step.
  eapply evt_cut. { Local Ltac2 Set LiaHints.tbl := fun () => "0020>22223415567.3522811687183.35000001002SS".
eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x150bc)) with (Z_to_bv 64 0x150bc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  step. step. step. apply evt_done. unfold rmunmap_entry. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition rseq_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (st' : mstate) (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 : word) m',
    ms' = MS (mkR (Z_to_bv 64 0x14ff0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
                  a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 ralloc_meta_entry) fc None m' (seg_rom usegs)
    /\ munch [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
    /\ rmrep st' m'.

(* [comment removed for export] *)
#[using="Type"] Lemma rbig_seq_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw xw rav s0v s1v s2v s3v s4v : word) F fc (m : mem)
    (lo n : Z) (st : mstate),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 ->
  bv_unsigned xw <> 2^64 - 1 ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> ATOP <= lo -> mem_inv usegs m ->
  evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (step_seq st) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 RMLOCK)
               xw a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14efc) fc None m (seg_rom usegs)).
Proof.
  intros until st. intros MR SEQ XNE FR ST LO ILO MI.
  pose proof (munch_refl [(RCTX + 848, RCTX + 880); (RCTX + 912, RCTX + 913)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ xw) as XR. change (bv_modulus 64) with (2^64) in XR.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & (_ & NL & _) & _).
  unfold RNEED_LOCKS, RCTX, RMLOCK, ralloc_meta_entry in *. atop_facts. unfold ctx_tail_cells in C6.
  replace (320304 + 912) with 321216 in C6 by reflexivity. replace (320304 + 848) with 321152 in US by reflexivity.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. apply XNE. rewrite K0. reflexivity. } clear K0.
  (* [comment removed for export] *)
  step. step. step. Local Ltac2 Set LiaHints.tbl := fun () => "00Q0>10308184993.5612465847128.6115494856263.7116075584200.581729782251.70 1729782251.71 18938345076.7018938345076.7121104699736.6122989694608.7022989694608.7123070080297.6125069450385.7125071629079.7025071629079.7129930806393.612994607484.70 31672124482.7134324860840.6145415804306.7147283939617.6152616299944.6153144248697.5853913289783.715472508760.61 5634884155.63 57013851305.575741606312.61 57994080753.7059308628304.5861665771703.606338163021.61 66947646621.6100000500600D00I00W00e00f00g00h00i00j00k00l00m00n00o01301401501601701801G01H01I01Q01R01S01T01X01c01d01eS3SEQSS2LO3ILO5ATOPRS3SEQS2LO3ILO5ATOPRS2LO3ILO5ATOPRSSSSSSSSSSS2NSSSSSSS3SEQ3XNE2XR2K2SSS3SEQ2K2SSSS2K1S3XNE2XR2K2SS".
rewrite ?zxb_b8 by lia. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. } clear K1 NL.
  (* [comment removed for export] *)
  step. rewrite ?zxb_b8 by lia. step.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1' : word) (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st ->
    rw_cells usegs mj (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
    stk usegs mj lo (bv_unsigned sp + -48) -> mem_inv usegs mj ->
    munch [(320304 + 848, 320304 + 880); (320304 + 912, 320304 + 913)]%Z m mj -> wmono usegs m mj ->
    evt usegs (rseq_post sp gp tp s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 nw xw rav s0v s1v s2v s3v s4v F fc lo (upd_ctx (set_seq ns) stj) m n)
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 320296)
               (Z_to_bv 64 ns) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 (n + 20)) xw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14fe8) fc None mj (seg_rom usegs))).
  { intros a1' mj stj ns NS MRj CTj FRj STj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (320304 + 912) with 321216 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 321216) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    raw_store_finishR (320304 + 912) [b8 ns] FRj STj MUj WMj SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. unfold rseq_post, RCTX, RMLOCK, ralloc_meta_entry. do 3 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption|]. split; [assumption|]. split; [exact FRj|]. exact MR1. }
  step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (c_seq (ctx st))) by lia.
    eapply evt_mono; [eapply (TAIL _ m st (c_seq (ctx st) + 1)); [lia| exact MR| reflexivity| exact FR| exact ST| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    assert (UZ : u8arr usegs m1 321152 (zeros 32)).
    { apply (u8arr_of_rw_cells usegs m1 321152 32). apply (rw_cells_congr usegs m1 321152 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact USC]. }
    clear USC.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    lazymatch goal with MUc : munch _ m m1, WMc : wmono usegs m m1 |- _ =>
    assert (MRz : rmrep stz m1);
    [ eapply (rmrep_ctx_frameW st stz _ m1 _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold RCTX; replace (320304 + 912) with 321216 by reflexivity;
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; unfold brk_word, ctx in C6; exact C6 ] |] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX, FRc : rw_cells usegs ?mX (bv_unsigned sp + -48) _, STc : stk usegs ?mX _ _, MIc : mem_inv usegs ?mX |- _ =>
      eapply evt_mono; [eapply (TAIL _ mX stz 1); [lia| exact MRz| reflexivity| exact FRc| exact STc| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : ATOP <= lo.

#[using="MR TK G0 MSL RR GN AN SHN HC CR NR CLO"] Lemma rbig_succ_walk :
  forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' gw s0v s1v s2v s3v s4v rav : word) F fc,
  bv_unsigned gw = G ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk usegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a0' a1' : word) m',
      ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
                   a0' a1' a2 a3 a4 a5 a6 a7 gw (wz 0) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x15188) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]
      /\ rmrep (big_st st g rid n (u32 (c + 1))) m' /\ ticks_ok (big_st st g rid n (u32 (c + 1))))
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
             gw a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (n + 20)) (wz x) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ff0) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros HG FR ST LO MI. unfold MMAP_THRESHOLD in NR. unfold IB, UNIT in RR.
  set (r0 := mkRegion RKGroup x (n + 4 + 16)) in RR.
  pose proof (munch_refl [(G, G + 40); (x, x + 8); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (CX1 & _) & _ & AR & GRP & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & GRG & (rid0 & rg0 & Hrg0 & Krg0 & GL0 & GH0)).
  fold G in CH, Gpos, GC, GI1, GI2, GRG, GL0, GH0. rewrite G0 in CH. unfold meta_cells in CH. cbn [m_prev m_next m_mem m_avail m_freed meta0 pw oconc] in CH.
  change (meta_word meta0) with 0 in CH.
  destruct (WR rid r0 RR) as (X0 & _ & XL & XC & XRF). cbn [r_base r_len r0] in X0, XL, XC, XRF.
  pose proof (round_up_pg_ge (n + 4 + 16)) as XRU.
  Local Ltac2 Set LiaHints.tbl := fun () => "00n0?11899637627.11212359540257.98 12701517829.11212701517829.11512701517829.12112701517829.12212701536187.11513632414499.11515032598273.10816041792159.11316424833789.11518926678684.10823053809399.1152398094887.98  24685052112.11224685052112.12124685052112.12226406869192.98 26824225136.11830652567469.10832391122337.10835201770367.11536644302768.10937976199868.11540820226000.11240820226000.12140820226000.12246179500539.10047430315851.11247430315851.12147430315851.12247803475360.10947960615403.1154812602655.112 4812602655.121 4812602655.122 49234157850.11249234157850.12149234157850.12249702956586.11249702956586.12149702956586.12253076942904.11555347981555.11255850107689.10956095916220.98 56207990393.11556338360900.10857271765628.10858300317893.94 59309005136.11459309005265.11459309005398.11459309005527.11459309005652.11459309005781.11459314923118.10159314938599.12359314938599.12659873856898.11561395978059.1159303872007.115 00000400<00C00G00N00U00Z00o01001901:01;01@01Q02702]03C03D03H03P03T04:04>04B04f05J05n06906J06[06l07307707;07?07C07J07Q07X07\07`07d08>08B08C08G08N08R08S08[09809U0:20:O0;00;M0;X0;j0<R0<W0<X0<jS2CRS2NR3XRUS2HG2HBS2HBS2HG2HBS2HG2HBS3LENS2NR3CLO2LO2XC3XRU2HBSS3GI13GI2SSS3LENS2NR2XC3XRU5ATOPRS2NR2HG4Gpos3GI13GI23XRU3XI13XI22GX2HBS2NR2HG4Gpos3GI13GI23XRU3XI13XI22GX2HBS2NR2HG4Gpos3GI13GI23XRU3XI13XI22GX2HBSS2HaS2NR3XRUS2NRS2NR2HG4Gpos3GI13GI23XRU3XI13XI22GX2HBS2NRS2HBS2NR2HG3GI13GI22X03XRU3XI13XI22GX2HBS2NR2HG3GI13GI22X03XRU3XI13XI22GX2HBS2NR2HG3GI13GI22X03XRU3XI13XI22GX2HBS2NR3XRU2HoS3CLO2HG2LO2GC2HBS3CLO2HG2LO2GC2HBS3CLO2HG2LO2GC2HBS2NR2LRS2HBS2HBS2HBS2HBS2HG2HBS2HG2HBS2HG2HBS2HBS2HBS2HBS2NR3GI13GI23XRU3XI22GX2HBS2CRSS2X0S2X02HBS2NRSS2NR3XRUS2NR3GI13GI23XRU3XI22GX2Ha2R1S2NR3GI13GI23XRU3XI22GX2Ha2R2S2NR3GI13GI23XRU3XI22GX2Ha2R3S2NR3GI13GI23XRU3XI22GX2Ha2R4S2NR3GI13GI23XRU3XI13XI22GX2Ha2R5S2NR3GI13GI23XRU3XI22GX2Ha2R6S2HG4Gpos1KS2Ha2Rq1D2NR3XRU1HS2Ha3Rak2Ca3Sa11D2NR3XRU1H2Rb2Cb3Sb13Sb0S3LENSS3CLO2LO5ATOPR3LEN".
destruct (rreserved_disjoint2 _ _ XRF ltac:(lia)) as [XI1 XI2].
  (* [comment removed for export] *)
  destruct (SH rid r0 RR eq_refl) as [XW XB]. cbn [r_base r_len r0] in XW, XB.
  assert (HDR : rw_cells usegs m x [C8 (wz 0); C1 (b8 0)]).
  { apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| |].
    - cbn [cells_bytes cbytes app]. change (le8 (wz 0) ++ [b8 0]) with (zeros 9).
      apply rzeros_bytes_at; [lia| cbn; atop_facts; lia|].
      intros o Ho. cbn in Ho. refine (proj1 (XB o 0 ltac:(lia) _)).
      unfold get_shadow. rewrite SHN. apply cell_read_shadow0.
    - cbn. eapply wr_at_sub; [exact XW| lia| lia]. }
  (* [comment removed for export] *)
  pose proof (GRG rid r0 RR eq_refl) as GX. cbn [r_base r_len r0] in GX.
  rewrite <- HG in CH.
  unfold RCTX, RMLOCK in *. atop_facts.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia. { exfalso. lia. } clear K.
  (* [comment removed for export] *)
  unfold rctx_head_cells, rsecw in CX1. rewrite HC in CX1.
  pose proof (rw_cells_prefix usegs m _ [C8 (wz (SECRET * c_init_done (ctx st))); C4 (wz (c_init_done (ctx st))); C4 (wz c)] _ CX1) as CX3. clear CX1.
  assert (GW0 : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUa. pose proof (wmono_refl usegs m) as WMa.
  step.
  assert (PWX : pw st (Some (rid, 0)) = wz x).
  { unfold pw, oconc, conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. reflexivity. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHA : rw_cells usegs mX (conc st g) (meta_cells st (big_metaA rid)));
    [ unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_metaA]; rewrite PWX;
      change (meta_word (big_metaA rid)) with 0; change (pw st None) with (wz 0); fold G; rewrite <- HG; exact CH
    | pose proof (rmrep_put_meta_frame st m mX g (big_metaA rid) MR MSL MUa WMa CHA) as MRA ] end.
  clear MUa WMa CHA.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(x, x + 8)]%Z mX) as MUb; pose proof (wmono_refl usegs mX) as WMb end.
  cbv delta [wz]. step.
  set (stA := put_meta g (big_metaA rid) st) in MRA.
  destruct (rmrep_hdr_havoc stA _ (rid, 0) MRA TK) as [MRB0 TKB].
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB1 : rmrep (hdr_havoc (rid, 0) stA) mX) end.
  { eapply (rmrep_transport_unowned _ _ _ _ MRB0 MUb WMb).
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R5|R6]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (hdr_havoc (rid, 0) stA)) with (s_areas st) in Hak. change (conc (hdr_havoc (rid, 0) stA) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> rid) by (intros EQ; destruct ak as [ak1 ak2]; cbn in EQ; subst ak1; rewrite (AN ak2) in Hak; discriminate).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_groups (hdr_havoc (rid, 0) stA)) with (s_groups st) in Hb. change (conc (hdr_havoc (rid, 0) stA) b) with (conc st b) in Rb.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      assert (NE : fst b <> rid) by (intros EQ; destruct b as [b1 b2]; cbn in EQ; subst b1; rewrite (GN b2) in Hb; discriminate).
      pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - change (s_regions (hdr_havoc (rid, 0) stA)) with (s_regions st) in Hq.
      destruct (N.eq_dec q rid) as [->|NE].
      + rewrite RR in Hq. inversion Hq; subst rq. cbn [r_base r0] in Cq.
        destruct (cell_read_hdr_havoc_fresh stA (rid, 0) (a - x) SHN ltac:(reflexivity) ltac:(cbn; lia)) as [h Hh].
        cbn [fst snd] in Hh. rewrite Z.add_0_l in Hh. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq RR NE) as [D|D]; cbn [r_base r_len r0 lr_lo r_kind] in D; lia.
    - unfold RGOT_SSP in R5. lia.
    - unfold RSSP_GUARD in R6. lia. }
  clear MRB0 MUb WMb.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRB : rmrep (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) mX) end.
  { eapply (rmrep_put_group_new _ _ (rid, 0) g 0 r0 (b8 0) MRB1); [apply GN| exact RR| reflexivity| cbn; lia| cbn [snd r_len r0]; lia| reflexivity| |reflexivity].
    change (conc (hdr_havoc (rid, 0) stA) (rid, 0)) with (conc st (rid, 0)). change (pw (hdr_havoc (rid, 0) stA) (Some g)) with (wz G).
    unfold conc, get_region. cbn [fst snd]. rewrite RR. cbn [r_base r0]. rewrite Z.add_0_r. rewrite <- GW0. exact HDR. }
  clear MRB1.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4115)) by lia.
  assert (LR : 0 <= Z.land (n + 4115) 18446744073709549568 <= n + 4115) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]).
  rewrite (unsigned_lit (Z.land (n + 4115) 18446744073709549568)) by lia.
  replace (n + 4115) with (n + 4064 + 51) by lia. rewrite (rbig_word_eq rid n) by lia.
  pose proof (meta_word_big_range rid n ltac:(lia)) as MWR.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(G, G + 40)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  change (Z_to_bv 64 (meta_word (big_meta rid n))) with (wz (meta_word (big_meta rid n))).
  step. step. step.
  set (stB := put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) stA)) in MRB.
  lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned gw) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (CHC : rw_cells usegs mX (conc stB g) (meta_cells stB (big_meta rid n)));
    [ change (conc stB g) with G; rewrite <- HG; unfold meta_cells; cbn [m_prev m_next m_mem m_avail m_freed big_meta];
      change (pw stB (Some (rid, 0))) with (pw st (Some (rid, 0))); rewrite PWX; change (pw stB None) with (pw st None); exact H
    | pose proof (rmrep_put_meta_frame stB _ mX g (big_meta rid n) MRB MSL MUc WMc CHC) as MRC ] end.
  clear MUc WMc CHC MRB.
  (* [comment removed for export] *)
  step. rewrite (sx32_wz_sxv c) by lia. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells usegs ?mX 320304 _ |- _ =>
    pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 320316) H eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK;
    clear H end.
  st1. rewrite le4_swrap_succ by lia.
  set (stC := put_meta g (big_meta rid n) stB) in MRC.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_mmap_counter stC mX (u32 (c + 1)) MRC VR) as MRD; unfold RCTX in MRD end.
  clear MRC.
  raw_store_finishR (320304 + 12) (le4 (wz (u32 (c + 1)))) FR ST MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [exact MRD| exact TKB].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End SUCC.
End CANSEC1.
