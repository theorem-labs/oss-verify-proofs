(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B F_malloc_bigw.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W15.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.
Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.
#[using="SC"] Lemma rbounce_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16574) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x162c0) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl usegs m) as WM. unfold rseqW in MU.
unfold RCTX, RMLOCK in *. atop_facts.
assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
rmrep stX mX -> stX = account_bounce sc st -> mem_inv usegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
munch [(324152 + 848, 324152 + 913)]%Z m mX -> wmono usegs m mX ->
evt usegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 324144) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16574) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch [(324152 + 848, 324152 + 913)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (account_bounce sc st) m')
(MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 324144) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16570) fc None mX (seg_rom usegs))).
{ intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
pose proof (rmrep_seq_read stX mX (wa (324152 + 912)) MRX eq_refl) as RDS.
replace (wa (324152 + 912)) with (Z_to_bv 64 (324144 + 920)) in RDS by (unfold wa; f_equal; lia).
assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
{ rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite SQX in RDS.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>10312655142.5410312673963.5711803485471.561299243932.46 13955036913.5414942038703.4516075584073.5316621371614.5517147041815.5320391242227.5420391242485.5320395383233.5120661899160.4820661931540.5620664257561.5323829646278.5023835853032.5026477010937.4626478912973.4528260892468.5435495598355.4535497501479.4641514199938.5444259298716.4645915914790.5449702840724.5652071097948.5353142180217.555505074959.50 55329271914.5656403478386.4657005180258.5558089443790.5459308579414.1161979364722.4663585107023.4667231390032.557162705429.50 7436836962.44 9785858949.47 9785894462.54 9786316318.50 00000500:00@00C00L00M00R00V00\00a00g00l00m00n00o01401:01>01B01F01G01H01L01P01Q01U01[01c01d01h01l01m02702E02H02O02S02W02[02a02g02mS3SEQS3SEQS2SC1KS1KS4USR72K1FS3SEQS2K3S1K2G7S3BR7S4USR7S3BR7SSSS3BR7S4USR7S2SCS2SCS2K2SSS2K2S2L7SS2SCS1H2H0S3BR72K3SS2SCS2G7SS3SEQ4USR7S2SC1K2L71H2H0S1KS2SC2G7S2K3S2G7S2SCS1K2G7S1K2G7S1K2G7".
rewrite ?zxb_b8 by lia. clear RDS.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
step. rewrite ?(unsigned_lit sc) by lia. step.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{
assert (HO : sc_in_seq_range sc = false).
{ unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
- replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
step. step.
eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
- unfold account_bounce. rewrite HO. reflexivity.
- unfold is_bouncing. rewrite HO. reflexivity. }
rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
destruct (Z.lt_ge_cases sc 7) as [L7|G7].
{ exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
rewrite Z.mod_small in K by lia.
assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
step. rewrite ?(unsigned_lit (sc + -7)) by lia.
pose proof (rmrep_bounces_read st m (sc - 7) (wa (324152 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
replace (wa (324152 + 880 + (sc - 7))) with (Z_to_bv 64 (324144 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
step. rewrite ?zxb_b8 by lia. clear RDB.
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_read usegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (324144 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
step. rewrite ?zxb_b8 by lia. clear RDU.
step. step.
set (nos := 100 <=? bounces st (sc - 7)).
assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
{ rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
change (bv_wrap 64 100) with 100.
destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
rewrite A3. clear A3.
assert (AB : account_bounce sc st =
(if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
else st)) by (unfold account_bounce; rewrite IN; reflexivity).
step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
{ eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
pose proof (rmrep_seq_read st m (wa (324152 + 912)) MR eq_refl) as RDS.
replace (wa (324152 + 912)) with (Z_to_bv 64 (324144 + 920)) in RDS by (unfold wa; f_equal; lia).
step. rewrite ?zxb_b8 by lia. clear RDS.
step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
{
apply Z.ltb_lt in K2.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite Bool.andb_false_r. exact MR. }
apply Z.ltb_ge in K2.
assert (AB2 : account_bounce sc st =
(if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
{ rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
clear AB K1 K2.
pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
pose proof (u8arr_store_ok usegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (324144 + (sc + -7) + 888)) BA
ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
-
step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (324152 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. step. st1.
first [rewrite (le1_lit 150) by lia | change [Z_to_bv 8 150] with [b8 150]].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (324152 + 880 + (sc - 7)) [b8 150] MU WM SOK.
eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rseq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv usegs m ->
munch rseqW m0 m -> wmono usegs m0 m ->
evt usegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x165a0) fc None m' (seg_rom usegs)
/\ munch rseqW m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (step_seq st) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16574) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
set (q := c_seq (ctx st)) in *.
pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
unfold RCTX, RMLOCK in *. atop_facts. unfold ctx_tail_cells in C6.
replace (324152 + 912) with 325064 in C6 by reflexivity. replace (324152 + 848) with 325000 in US by reflexivity.
assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv usegs mj ->
munch [(324152 + 848, 324152 + 913)]%Z m0 mj -> wmono usegs m0 mj ->
evt usegs (fun ms' => exists (a6' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 324144) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x165a0) fc None m' (seg_rom usegs)
/\ munch [(324152 + 848, 324152 + 913)]%Z m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 324144) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16598) fc None mj (seg_rom usegs))).
{ intros mj stj ns NS MRj CTj MIj MUj WMj.
pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
replace (324152 + 912) with 325064 in C6j by reflexivity.
pose proof (rw_cells_store_ok_at usegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (324144 + 920)) C6j eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6j.
step. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>11478788696.5211803485471.5611805467289.5311805467289.5413456675485.5214129987602.5422246180696.522994607484.55 31981318009.5233427881304.523381681140.53 3381681140.54 35730727362.563943200600.52 434141041.53  44797605570.4847283939617.5056775176220.4656780260279.5656942704881.4600000100200300400500600700;00<00=00>00?00@00A00B00F00G00L00M00USSSSSSSS2NSSSSSSSSS2K2SS3SEQSS3SEQ2K2".
rraw_store_finish0 (324152 + 912) [b8 ns] MUj WMj SOK.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
-
step. rewrite (wz_unsigned q) by lia.
eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
-
pose proof (rw_cells_of_u8arr usegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
pose proof (munch_refl [(324152 + 848, 324152 + 880)]%Z m) as MUz. pose proof (wmono_refl usegs m) as WMz.
step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UZ : u8arr usegs mX 325000 (zeros 32));
[ apply (u8arr_of_rw_cells usegs mX 325000 32);
lazymatch goal with H : rw_cells usegs mX 325000 _ |- _ =>
apply (rw_cells_congr usegs mX 325000 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
lazymatch goal with MUc : munch _ m ?mX, WMc : wmono usegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRz : rmrep stz mX);
[ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
[ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
| right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
| right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
| clear MUc WMc ] end.
step. step.
lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono usegs m0 ?mX, MIc : mem_inv usegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SC"] Lemma rmm_seq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x165a0) fc None m' (seg_rom usegs)
/\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
/\ munch rseqW m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ rmrep (step_seq (account_bounce sc st)) m')
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x162c0) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR SEQ BR USR MI.
eapply evt_cut; [eapply rbounce_walk; eassumption|].
cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
{ unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
rewrite <- SEQ'.
eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
do 6 eexists. split; [reflexivity|]. subst a3'.
repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.
End CANSEC1.
