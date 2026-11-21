(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh run top1): the view's
   text, the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/U2cA (cure C36 / C43) moved to the combined image by
   tools/g2b.py.  Of the 20 conflicts, 8 keep the view's side (the combined image's constants and its depot-chain
   hypotheses UI0 / UINB), 12 take G's side (tools/resolve.py), then by hand (marked [U14B]): the combined registers
   (s3 = destLen, s5 = *destLen / left), the combined outbuf shadow end 2148276280, INIT's binder tr, UINB. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness CMonad CMonadX ProgAC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require HarnessC Client.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit CProto CProtoX.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2ABlob UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface U2BGlue U2BIfaceS InfBBase InfBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2cB_pre U2cB_loop U2cB_epi U2cB_inv U2cB_loopA U2cB_tail.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U1BGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section U2c.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB1 F := (mkABlock (ABFake 0) F 64).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Hypothesis SM2 : SM2_stmt AI fflag rng_fs.
Hypothesis INIT : inflateInit_stmtA AI.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis INF_W : inflate_stmtA AI rng_fs true.
Hypothesis INF_N : inflate_stmtA AI rng_fs false.
Hypothesis END : forall withwin, inflateEnd_stmtA AI withwin.

Section Body.
Variables (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (m : amem) (s : APS) (LB : list ablock) (D F1 lo n SPA : Z) (payload : list Z) (trc : list Z).
Notation SP := (bv_unsigned sp).
Variable SL : Z.
Hypothesis ESL : SL = SP + 8.
Notation DL := (SP + 16).
Notation OB := A_OUTBUF.

Hypothesis AH : AHEAP AI L RNG (aps_m s) LB m.
Hypothesis F1IN : In (FB1 F1) LB.
Hypothesis F1128 : F1 mod 64 = 0.
Hypothesis F1B : ablk F1 (F1 + 64).
Hypothesis LBH : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis NL0 : atmost1_c0 LB.
Hypothesis NL2 : no_live 2 LB.
Hypothesis DLC : rw_cells bsegs m DL [C8 (Z_to_bv 64 262144)].
Hypothesis SLC : rw_cells bsegs m SL [C8 (Z_to_bv 64 n)].
Hypothesis SHD : shadow_bytes m (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1) (fun _ => 0).
Hypothesis SHS : shadow_bytes m (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1) (fun _ => 0).
Hypothesis RF1 : rng RNG F1 64.
Hypothesis RSDL : rng RNG (Z.shiftr DL 3 + 2147450880) 1.
Hypothesis RSSL : rng RNG (Z.shiftr SL 3 + 2147450880) 1.
Hypothesis PAY : (exists pd, In (HB pd D n) LB /\ 0 < n) \/ (n = 0 /\ D = 0x60c1a0).
Hypothesis PBY : bytes_at bsegs m D (map (Z_to_bv 8) payload).
Hypothesis PFO : Forall (fun c => 0 <= c < 256) payload.
Hypothesis PLEN : Z.of_nat (length payload) = n.
Hypothesis D16 : D mod 16 = 0.
Hypothesis N26 : 0 <= n < 67108864.
Hypothesis UNP : unpoisoned m D (D + n).
Hypothesis RD : rng RNG D n.
Hypothesis RSD : rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1).
Hypothesis OBB : exists obr, rw_cells bsegs m OB [CB (Z.to_nat 262144) obr].
Hypothesis SHOB : shadow_bytes m 2148243512 2148276280 (fun _ => 0).
Hypothesis OBC : exists iv, In iv CI /\ fst iv <= OB /\ OB + 262144 <= snd iv.
Hypothesis ROB : rng RNG OB 262144.
Hypothesis RSOB : rng RNG 2148243512 32768.
Hypothesis VSH : ver_sh m.
Hypothesis TSH : u2_tabsh m.
Hypothesis VCL : exists iv, In iv CI /\ fst iv <= 141152 /\ 141160 <= snd iv.
Hypothesis TABC1 : exists iv, In iv CI /\ fst iv <= 141376 /\ 152288 <= snd iv.
Hypothesis TABC2 : exists iv, In iv CI /\ fst iv <= 149216 /\ 149568 <= snd iv.
Hypothesis ST : stk bsegs m lo SP.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - UC_STACK.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis SPTOP : SP + 48 < al_top L.
Hypothesis MI : mem_inv bsegs m.
Hypothesis TPE : tp = Z_to_bv 64 ATP.
Hypothesis ESPA : SPA = SP - 160 - SP mod 32.
Hypothesis RAOK : 4096 <= bv_unsigned ra /\ bv_unsigned ra <> AMALLOC_PC.
Hypothesis S0SP : bv_unsigned s0 <= SP.
Hypothesis UC : forall k, (2 <= k)%nat -> uchain m (al_top L) AMALLOC_PC SP (bv_unsigned s0) k trc.
Hypothesis TRL : (length trc <= 26)%nat.
Hypothesis UI0 : In [AMALLOC_PC; RA_INIT_ZALLOC] (al_U L).
Hypothesis UINB : In [AMALLOC_PC; RA_UW_ZALLOC] (al_U L).
Hypothesis UF1 : In [AFREE_PC; RA_END_ZFREE_W] (al_U L).
Hypothesis UF2 : In [AFREE_PC; RA_END_ZFREE_S] (al_U L).
Hypothesis RSTK : rng RNG lo (al_top L - lo).
Hypothesis RIMG : rng_aimg RNG.
Hypothesis RISH : rng_aimg_sh RNG.
Hypothesis RFS : rng_fs L RNG.
Hypothesis OK : aps_ok L s.

Notation UPF := (uc_PF AI sp LB SL).

Definition uset (a : Z) : Prop :=
     a = 2147468524 \/ 2147468552 <= a < 2147469916 \/ 2147469532 <= a < 2147469576 \/ 2148243512 <= a < 2148276280
  \/ OB <= a < OB + 262144 \/ D <= a < D + n.
Definition ustatics (m' : amem) : Prop :=
     ver_sh m' /\ u2_tabsh m' /\ (exists obr, rw_cells bsegs m' OB [CB (Z.to_nat 262144) obr])
  /\ shadow_bytes m' 2148243512 2148276280 (fun _ => 0) /\ bytes_at bsegs m' D (map (Z_to_bv 8) payload).

Lemma ustatics_agree : forall m1 m2, magree bsegs uset m1 m2 -> ustatics m1 -> ustatics m2.
Proof.
  intros m1 m2 AG (V & T & (obr & O) & SO & PB). unfold ustatics.
  split; [unfold ver_sh in *; eapply shadow_bytes_magree; [exact AG| exact V|]; intros a Ha; left; lia|].
  split.
  { unfold u2_tabsh in *. destruct T as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
    split; [eapply shadow_bytes_magree; [exact AG| exact T1|]; intros a Ha; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T2|]; intros a Ha; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T3|]; intros a Ha; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T4|]; intros a Ha; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T5|]; intros a Ha; right; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T6|]; intros a Ha; right; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T7|]; intros a Ha; right; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T8|]; intros a Ha; right; right; left; lia|].
    split; [eapply shadow_bytes_magree; [exact AG| exact T9|]; intros a Ha; right; right; left; lia|].
    eapply shadow_bytes_magree; [exact AG| exact T10|]; intros a Ha; right; right; left; lia. }
  split; [exists obr; eapply rw_cells_magree; [exact AG| exact O|]; cbn [cells_size csize Nat.add]; intros a Ha; do 4 right; left; lia|].
  split; [eapply shadow_bytes_magree; [exact AG| exact SO|]; intros a Ha; do 3 right; left; lia|].
  eapply bytes_at_magree; [exact AG| exact PB|]. rewrite length_map, PLEN. intros a Ha. do 5 right. lia.
Qed.

Lemma uset_client : forall LBx SPx a, (forall b, In b LB -> In b LBx) -> uset a -> aclient_addr CI LBx SPx a.
Proof.
  intros LBx SPx a SUB [->|[K|[K|[K|[K|K]]]]].
  - right. right. right. exists 141152. split; [| reflexivity]. right. left. destruct VCL as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
  - right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. right. left.
    destruct TABC1 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| unfold ASHOFF; lia].
  - right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. right. left.
    destruct TABC2 as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| unfold ASHOFF; lia].
  - right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. right. left.
    destruct OBC as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| unfold ASHOFF, A_OUTBUF in *; lia].
  - right. left. destruct OBC as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
  - right. right. left. destruct PAY as [(pd & PDI & _)|(N0 & _)]; [| exfalso; lia].
    exists (HB pd D n). split; [apply SUB; exact PDI| cbn [ab_addr ab_size]; lia].
Qed.

Lemma uset_below : forall a, uset a -> a < ATOP.
Proof.
  intros a U. atop_facts. destruct U as [->|[K|[K|[K|[K|K]]]]]; try (unfold A_OUTBUF in *; lia).
  destruct PAY as [(pd & PDI & _)|(N0 & _)]; [| exfalso; lia].
  pose proof (AI_block_bounds AI _ _ _ _ _ _ AH PDI) as (_ & _ & X). cbn [ab_addr ab_size] in X. lia.
Qed.

Lemma uset_outside_fake : forall RNGx stx LBx mx c F N a,
  AHEAP AI L RNGx stx LBx mx -> (forall b, In b LB -> In b LBx) -> In (mkABlock (ABFake c) F N) LBx -> ablk F (F + N) ->
  uset a -> ~ (F <= a < F + N).
Proof.
  intros RNGx stx LBx mx c F N a AHx SUB FIN FBK U. pose proof (ablk_lin _ _ FBK) as (K1 & K2 & K3 & K4). unfold AIMG_HI in K1.
  destruct U as [->|[K|[K|[K|[K|K]]]]].
  - apply (ablk_clear_band _ _ _ FBK). unfold KLS. lia.
  - apply (ablk_clear_band _ _ _ FBK). unfold KLS. lia.
  - apply (ablk_clear_band _ _ _ FBK). unfold KLS. lia.
  - apply (ablk_clear_band _ _ _ FBK). unfold KLS. lia.
  - unfold A_OUTBUF in *. lia.
  - destruct PAY as [(pd & PDI & _)|(N0 & _)]; [| exfalso; lia].
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pd D n) (mkABlock (ABFake c) F N) AHx (SUB _ PDI) FIN ltac:(discriminate)) as X.
    cbn [ab_addr ab_size] in X. lia.
Qed.

Lemma uset_outside_fsh : forall F N a, ablk F (F + N) -> F mod 8 = 0 -> 0 <= N -> N mod 8 = 0 ->
  uset a -> ~ (Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + N / 8).
Proof.
  intros F N a FBK F8 N0 N8 U. pose proof (ablk_lin _ _ FBK) as (K1 & K2 & K3 & K4). unfold AIMG_HI in K1.
  assert (SHB : 2148285096 <= Z.shiftr F 3 + 2147450880 /\ Z.shiftr F 3 + 2147450880 + N / 8 <= 0x10007fff8000).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  destruct U as [->|[K|[K|[K|[K|K]]]]]; try (unfold A_OUTBUF in *; lia).
  destruct PAY as [(pd & PDI & _)|(N0' & _)]; [| exfalso; lia].
  pose proof (LBH _ PDI) as PBK. cbn [ab_addr ab_size] in PBK. intros X. apply (ablk_clear_band _ _ a PBK); [unfold KLS; lia| lia].
Qed.

Lemma client_outside_stk : forall a lo', ATOP <= lo' -> aclient_addr CI LB SP a -> ~ (lo' <= a < SP).
Proof.
  intros a lo' LO' [H|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]]; atop_facts.
  - lia.
  - pose proof (AI_aci_img AI iv Hiv) as X. unfold AIMG_HI in X. lia.
  - pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb) as (_ & _ & X). lia.
  - assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb') as BX. cbn [ab_addr ab_size] in BX. unfold AIMG_HI in *. lia. }
    pose proof (shad_in_band a' A47) as SB. lia.
Qed.

Lemma uspa_f : SP - 176 <= SPA <= SP - 160 /\ SPA mod 32 = 0.
Proof. rewrite ESPA. Z.div_mod_to_equations. lia. Qed.

Lemma uc_head : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evtF bsegs RNG (fun ms3 => exists (Fu : Z) (m3 : amem) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (j8 j16 : list byte)
                                 (p1 ti no ao p2 to msg state dt p3 adler reserved : word),
      ms3 = MS (mkR (Z_to_bv 64 0x8cd34) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (Fu + 32)) (Z_to_bv 64 141152) (Z_to_bv 64 112)
                    (* [U14B] A2 2026-11-12: the COMBINED 1.4 image: s3 = destLen, s5 = *destLen (U2cB_pre's uc_hdr) *)
                    y13 y14 y15 y16 y17 (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL)
                    (Z_to_bv 64 262144) (Z_to_bv 64 D) (Z_to_bv 64 (Fu + 32))
                    (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) (Z_to_bv 64 n) y28 y29 y30 y31)
               FR (Z_to_bv 64 A_INFLATEINIT) fc None m3 (seg_rom bsegs)
      /\ Fu mod 256 = 0 /\ ablk Fu (Fu + 256) /\ rng RNG Fu 256 /\ rng RNG (Z.shiftr Fu 3 + 2147450880) 32
      /\ AHEAP AI L RNG (aps_m s) (FB2 Fu :: LB) m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 lo SPA
      /\ uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL j8 j16 n trc m3
      /\ rw_cells bsegs m3 (Fu + 32) (strm_cells (Z_to_bv 64 D) (Z_to_bv 64 0) ti no ao to msg state (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                                 dt adler reserved p1 p2 p3)
      /\ magree bsegs UPF m m3 /\ ustatics m3)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6341056) (Z_to_bv 64 DL) (Z_to_bv 64 D) (Z_to_bv 64 SL) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 A_UNCOMPRESS2) fc None m (seg_rom bsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof uspa_f as (SPAB & SPA32). pose proof LOS as LOS'. unfold UC_STACK in LOS'.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (ablk_lin _ _ F1B) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1.
  assert (SPT : SP + 48 < KEND) by (unfold KEND; lia).
  assert (RSTK' : rng RNG lo (SP - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (RSLC : rng RNG SL 8) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (RDLC : rng RNG DL 8) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (DNZ : 0 < D < 2^64).
  { destruct PAY as [(pd & PDI & _)|(_ & ->)]; [| lia].
    pose proof (AI_block_bounds AI _ _ _ _ _ _ AH PDI) as (X1 & _ & X3). cbn [ab_addr ab_size] in X1, X3. unfold AIMG_HI in X1. lia. }
  assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
  assert (G8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART. destruct ART as (_ & GOT & _ & _ & SHB & SUAR & _).
  eapply evtF_cut.
  { eapply (uc_pre ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc D F1 lo SPA RNG SL ESL LOS LOC SP16 SPT ESPA RSTK' RIMG);
      [exact ST| exact MI| exact GOT| exact SHB| exact (u2_img_of_aheap AI _ _ _ _ _ AH)| exact SUAR]. }
  cbv beta. intros ms1 (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU1 WM1). constructor; [cbn [fst snd]; apply acr_stack; lia| constructor]. }
  assert (AG1 : magree bsegs (fun a => outside [(SP - 176, SP)] a) m m1) by exact (magree_of_munch bsegs _ m m1 MU1 WM1).
  assert (DLC1 := DLC). eapply rw_cells_transport in DLC1; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (SLC1 := SLC). eapply rw_cells_transport in SLC1; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (BSD : 2147450880 <= Z.shiftr DL 3 + 2147450880 /\ Z.shiftr DL 3 + 2147450880 + 1 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (BSL : 2147450880 <= Z.shiftr SL 3 + 2147450880 /\ Z.shiftr SL 3 + 2147450880 + 1 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (SHD1 := SHD). eapply shadow_bytes_munch in SHD1; [| exact MU1| cbn [disjoint_from]; repeat split; try exact I; lia].
  assert (SHS1 := SHS). eapply shadow_bytes_munch in SHS1; [| exact MU1| cbn [disjoint_from]; repeat split; try exact I; lia].
  pose proof SM2 as SM2'. unfold SM2_stmt, sm_stmt in SM2'.
  eapply evtF_cut.
  { unfold ASM2. eapply SM2';
      [exact AH1| intros Fa na Fb nb X _; exfalso; exact (NL2 _ _ X)| exact MI1| rewrite USPA; exact STL1| exact LOC| rewrite USPA; unfold SM_STACK; lia| rewrite USPA; lia
      | exact TPE| exact RSTK| exact RIMG| exact RFS]. }
  cbv beta. unfold sm_post. rewrite USPA.
  intros ms2 (Fu & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & j0 & j1 & j2 & junk
              & -> & MI2 & STL2 & PRES & AH2 & F256 & FBK & FTOP & FF2 & FSH2 & RF & RSF).
  change (Z.to_nat (256 - 32)) with 224%nat in FF2. change (256 / 8) with 32 in RSF. rewrite shadE in RSF.
  pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (FIN2 : In (FB2 Fu) (FB2 Fu :: LB)) by (left; reflexivity).
  assert (SUB2 : forall b, In b LB -> In b (FB2 Fu :: LB)) by (intros b Hb; right; exact Hb).
  assert (FNI : ~ In (FB2 Fu) LB).
  { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as ND. inversion ND as [|x l NI0 N3]. exact NI0. }
  assert (SEPF : F1 + 64 <= Fu \/ Fu + 256 <= F1).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (FB2 Fu) (FB1 F1) AH2 FIN2 (SUB2 _ F1IN) ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
  assert (FRB2 : rw_cells bsegs m2 (SP + -104) (UFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FRB1|]. left. left. unfold UFRB. cbn [cells_size csize Nat.add]. lia. }
  assert (FRA2 : rw_cells bsegs m2 SPA [CB 56 jA]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact FRA1|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (STG2 : stk bsegs m2 (SPA + 56) (SP + -104)) by (eapply aheap_pres_stk; [exact PRES| exact STG1| lia| lia]).
  assert (DLC2 : rw_cells bsegs m2 DL [C8 (Z_to_bv 64 262144)]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact DLC1|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (SLC2 : rw_cells bsegs m2 SL [C8 (Z_to_bv 64 n)]).
  { eapply aheap_pres_rw_cells; [exact PRES| exact SLC1|]. left. left. cbn [cells_size csize Nat.add]. lia. }
  assert (SHD2 : shadow_bytes m2 (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1) (fun _ => 0)).
  { eapply (stk_sh_pres AI LB SPA m1 m2 DL 1); [exact PRES| Z.div_mod_to_equations; lia| lia| lia| exact SHD1]. }
  assert (SHS2 : shadow_bytes m2 (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1) (fun _ => 0)).
  { eapply (stk_sh_pres AI LB SPA m1 m2 SL 1); [exact PRES| Z.div_mod_to_equations; lia| lia| lia| exact SHS1]. }
  pose proof (AI_rtcells AI _ _ _ _ _ AH2) as ART2. unfold artcells in ART2.
  destruct ART2 as (_ & GOT2 & RIC2 & REAL2 & SHB2 & _ & INI2 & LAY2 & _).
  replace (ret_pc (Z_to_bv 64 0x8cbcc)) with (Z_to_bv 64 0x8cbcc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply evtF_mono.
  { eapply (uc_hdr ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc D F1 lo SPA RNG SL ESL LOS LOC SP16 SPT ESPA RSTK' RIMG
                   Fu (fflag L 2 Fu) F256 FBK RF RSF F1128 F1B RDLC RSDL RSSL RSLC SEPF);
      [exact STL2| exact MI2| exact GOT2| exact RIC2| exact SHB2| exact INI2| exact LAY2| exact REAL2| exact FRA2| exact FF2| exact FSH2
      | exact DLC2| exact SLC2| exact SHD2| exact SHS2| lia| exact DNZ]. }
  cbv beta.
  intros ms3 (m3 & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & j8 & j16 & p1 & ti & no & ao & p2 & to & msg & state & dt & p3 & adler & reserved
              & -> & MU3 & WM3 & MI3 & STL3 & FRA3 & FH3 & FFL3 & FSH3 & DLC3 & SLC3 & STRM3).
  unfold uc_hdrW in MU3.
  assert (BSF : 2148285096 <= Z.shiftr Fu 3 + 2147450880 /\ Z.shiftr Fu 3 + 2147450880 + 32 <= 17594333495296)
    by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (AG3 : magree bsegs (fun a => outside [(lo, SPA + 56); (Fu, Fu + 256); (Z.shiftr Fu 3 + 2147450880, Z.shiftr Fu 3 + 2147450912)] a) m2 m3)
    by exact (magree_of_munch bsegs _ m2 m3 MU3 WM3).
  assert (AH3 : AHEAP AI L RNG (aps_m s) (FB2 Fu :: LB) m3).
  { eapply (AI_frame AI _ _ _ _ m2 m3 _ AH2 MU3 WM3).
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 Fu 256); [exact FIN2| lia| lia]|].
    constructor; [cbn [fst snd]; replace (Z.shiftr Fu 3 + 2147450912) with (Z.shiftr Fu 3 + 2147450880 + 32) by lia;
                  apply (acr_fake_sh AI _ 2 Fu 256 Fu 32); [exact FIN2| exact F8| lia| lia| lia]| constructor]. }
  assert (FRB3 := FRB2). eapply rw_cells_transport in FRB3; [| exact MU3| exact WM3| unfold UFRB; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (STG3 : stk bsegs m3 (SPA + 56) (SP + -104)) by (eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| cbn [disjoint_from]; repeat split; try exact I; lia]).
  assert (SHD3 := SHD2). eapply shadow_bytes_munch in SHD3; [| exact MU3|].
  2:{ cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - SPT RSP SEPF FBK F1B F8 G8 LOC LOS' SPAB GL1 GL2 GL3 FL1 FL2 FL3 H. unfold KEND in SPT.
      unfold ablk, AIMG_HI, KLS in FBK, F1B. Z.div_mod_to_equations. lia. }
  assert (SHS3 := SHS2). eapply shadow_bytes_munch in SHS3; [| exact MU3|].
  2:{ cbn [disjoint_from]. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - ESL SPT RSP SEPF FBK F1B F8 G8 LOC LOS' SPAB GL1 GL2 GL3 FL1 FL2 FL3 H. unfold KEND in SPT.
      unfold ablk, AIMG_HI, KLS in FBK, F1B. Z.div_mod_to_equations. lia. }
  assert (UC3 : forall k, (2 <= k)%nat -> uchain m3 (al_top L) AMALLOC_PC SP (bv_unsigned s0) k trc).
  { intros k Hk. eapply uchain_low; [exact (UC k Hk)| exact S0SP]. }
  assert (US3 : ustatics m3).
  { eapply ustatics_agree; [| eapply ustatics_agree; [| eapply ustatics_agree; [| exact (conj VSH (conj TSH (conj OBB (conj SHOB PBY))))]]].
    - eapply magree_mono; [exact AG3|]. intros a U. cbn [outside]. pose proof (uset_below a U).
      pose proof (uset_outside_fake RNG _ (FB2 Fu :: LB) m2 2 Fu 256 a AH2 SUB2 FIN2 FBK U).
      pose proof (uset_outside_fsh Fu 256 a FBK F8 ltac:(lia) ltac:(reflexivity) U) as X. change (256 / 8) with 32 in X.
      pose proof (uset_outside_fake RNG _ LB m 0 F1 64 a AH ltac:(auto) F1IN F1B U).
      repeat split; try exact I; lia.
    - intros a Ha U. apply PRES; [exact Ha|]. apply uset_client; [auto| exact U].
    - eapply magree_mono; [exact AG1|]. intros a U. cbn [outside]. pose proof (uset_below a U). repeat split; try exact I; lia. }
  assert (PF3 : magree bsegs UPF m m3).
  { eapply magree_trans; [| eapply magree_trans].
    - eapply magree_mono; [exact AG1|]. intros a [HC _]. cbn [outside]. pose proof (client_outside_stk a (SP - 176) ltac:(lia) HC). repeat split; try exact I; lia.
    - intros a Ha [HC _]. apply PRES; [exact Ha|]. eapply aclient_addr_weaken; [| | exact HC]; [auto| lia].
    - eapply magree_mono; [exact AG3|]. intros a [HC NW]. cbn [outside].
      pose proof (client_outside_stk a lo ltac:(lia) HC).
      pose proof (client_outside_blk AI L RNG _ (FB2 Fu :: LB) LB m2 (FB2 Fu) SP a AH2 FIN2 FNI SUB2 FBK ltac:(lia) HC) as X1. cbn [ab_addr ab_size] in X1.
      pose proof (client_outside_fsh AI L RNG _ (FB2 Fu :: LB) LB m2 2 Fu 256 SP a AH2 FIN2 FNI SUB2 LBH FBK F8 ltac:(reflexivity) ltac:(lia) ltac:(lia) HC) as X2.
      change (256 / 8) with 32 in X2.
      assert (X3 : ~ (DL <= a < DL + 8)) by (intros X; apply NW; exists (DL, DL + 8); split; [right; left; reflexivity| exact X]).
      repeat split; try exact I; lia. }
  exists Fu, m3, y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31, j8, j16, p1, ti, no, ao, p2, to, msg, state, dt, p3, adler, reserved.
  split; [reflexivity|]. split; [exact F256|]. split; [exact FBK|]. split; [exact RF|]. split; [exact RSF|]. split; [exact AH3|]. split; [exact MI3|]. split; [exact STL3|].
  split; [| split; [exact STRM3| split; [exact PF3| exact US3]]].
  unfold uc_frame. split; [exact FRA3|]. split; [exact FRB3|]. split; [exact STG3|]. split; [exact FH3|]. split; [exact FFL3|].
  split; [exact FSH3|]. split; [exact DLC3|]. split; [exact SLC3|]. split; [exact SHD3|]. split; [exact SHS3| exact UC3].
Qed.

Section Start.
Variables (Fu : Z) (m3 : amem) (j8 j16 : list byte).
Notation Zs := (Fu + 32).
Notation SHF := (Z.shiftr Fu 3 + 2147450880).
Hypothesis F256 : Fu mod 256 = 0.
Hypothesis FBK : ablk Fu (Fu + 256).
Hypothesis RF : rng RNG Fu 256.
Hypothesis RSF : rng RNG SHF 32.
Hypothesis FRM3 : uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL j8 j16 n trc m3.
Hypothesis PF3 : magree bsegs UPF m m3.
Hypothesis US3 : ustatics m3.
Variables (RNG1 : footprint) (sA1 : APS) (p : AsanCtrl.aptr) (S : Z) (m4 : amem).
Variables (check len off ext lb db ncode nlen ndist have was pad no ao dt reserved p1 p2 p3 : word) (jarr : list byte).
Hypothesis FPL : fp_le RNG RNG1.
Hypothesis MI4 : mem_inv bsegs m4.
Hypothesis ST4 : stk bsegs m4 lo SPA.
Hypothesis RS1 : aps_rest sA1 = aps_rest s.
Hypothesis CA4 : client_agree AI (FB2 Fu :: LB) SPA [(Zs, Zs + 112)] m3 m4.
Hypothesis AH4 : AHEAP AI L RNG1 (aps_m sA1) (HB p S 7176 :: FB2 Fu :: LB) m4.
Hypothesis S16 : S mod 16 = 0.
Hypothesis SBK : ablk S (S + 7176).
Hypothesis STRM4 : rw_cells bsegs m4 Zs (strm_cells (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 0) no ao (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0) dt (Z_to_bv 64 1) reserved p1 p2 p3).
Hypothesis ISTC4 : rw_cells bsegs m4 S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 16180) (Z_to_bv 64 0) (Z_to_bv 64 5) (Z_to_bv 64 0)
                                      (Z_to_bv 64 (-1)) (Z_to_bv 64 32768) check (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 15)
                                      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      len off ext (Z_to_bv 64 (S + 1384)) (Z_to_bv 64 (S + 1384)) lb db ncode nlen ndist have
                                      (Z_to_bv 64 (S + 1384))).
Hypothesis JARR4 : rw_cells bsegs m4 (S + 168) [CB (Z.to_nat 6992) jarr].
Hypothesis TAIL4 : rw_cells bsegs m4 (S + 7160) (itail_cells (Z_to_bv 64 1) (Z_to_bv 64 (-1)) was pad).

Notation LBN := (LBn Fu S p LB).
Notation UINV := (uc_inv AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) lo S D n payload p LB j8 j16 n trc m RNG s SL).
Notation LOOP pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 len v10 left x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
           (* [U14B] A2 2026-11-12: the COMBINED 1.4 image: s3 = destLen, s5 = left (as LOOP in U2cB_loop) *)
           (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL) (Z_to_bv 64 left) v10 (Z_to_bv 64 Zs)
           (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) (Z_to_bv 64 len) x28 x29 x30 x31)
      FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

Lemma uc_keep_cl : forall a, uc_keep sp SPA Fu SL a -> aclient_addr CI (FB2 Fu :: LB) SPA a /\ ~ in_ranges [(Zs, Zs + 112)] a.
Proof.
  intros a KP. pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). pose proof (ablk_lin _ _ F1B) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in *.
  pose proof uspa_f as (SPAB & _). pose proof LOS as LOS'. unfold UC_STACK in LOS'. atop_facts.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (G8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (FIN2 : In (FB2 Fu) (FB2 Fu :: LB)) by (left; reflexivity).
  assert (GIN2 : In (FB1 F1) (FB2 Fu :: LB)) by (right; exact F1IN).
  assert (AH4' : AHEAP AI L RNG1 (aps_m sA1) (HB p S 7176 :: FB2 Fu :: LB) m4) by exact AH4.
  assert (SEPFG : Fu + 256 <= F1 \/ F1 + 64 <= Fu).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (FB2 Fu) (FB1 F1) AH4 ltac:(right; left; reflexivity) ltac:(right; right; exact F1IN) ltac:(discriminate)) as X.
    cbn [ab_addr ab_size] in X. lia. }
  assert (LOCa : (SPA <= a < 2^47) \/ ((Fu <= a < Fu + 32 \/ Fu + 144 <= a < Fu + 256) \/ (F1 <= a < F1 + 64) \/ (KLS <= a < 0x10007fff8000))).
  { unfold uc_keep in KP. destruct KP as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; [left; lia| right; left; lia| right; left; lia| | left; lia| left; lia | |].
    - right. right. right. unfold KLS. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. intros K. Z.div_mod_to_equations. lia.
    - right. right. right. unfold KLS. subst a. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
    - right. right. right. unfold KLS. subst a. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  split.
  - unfold uc_keep in KP. destruct KP as [K|[K|[K|[K|[K|[K|[K|K]]]]]]].
    + left. lia.
    + right. right. left. exists (FB2 Fu). split; [exact FIN2| cbn [ab_addr ab_size]; lia].
    + right. right. left. exists (FB2 Fu). split; [exact FIN2| cbn [ab_addr ab_size]; lia].
    + right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right. right. exists 2, Fu, 256. split; [exact FIN2|]. unfold ASHOFF. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      intros K. Z.div_mod_to_equations. lia.
    + left. lia.
    + left. lia.
    + right. right. right. exists DL. split; [| rewrite shadE; exact K]. left. lia.
    + right. right. right. exists SL. split; [| rewrite shadE; exact K]. left. lia.
  - intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr.
    destruct LOCa as [K|[K|[K|K]]]; [lia| lia| lia|]. apply (ablk_clear_band _ _ a FBK K). lia.
Qed.

Lemma uc_start : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  evtF bsegs RNG1 (fun ms5 => exists (st : ist) (v : uvw) (m5 : amem) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      ms5 = LOOP A_INFLATE (Z_to_bv 64 0x8cf4c) y5 y6 y7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17 0 (Z_to_bv 64 4294967295) 0 y28 y29 y30 y31 m5
      /\ UINV 0 RNG1 sA1 LBN st v m5)
    (LOOP 0x8cd34 (Z_to_bv 64 0x8cd34) x5 x6 x7 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 n (Z_to_bv 64 D) 262144 x28 x29 x30 x31 m4).
Proof.
  intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
  pose proof uspa_f as (SPAB & SPA32). pose proof LOS as LOS'. unfold UC_STACK in LOS'.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). pose proof (ablk_lin _ _ F1B) as (GL1 & GL2 & GL3 & GL4).
  pose proof (ablk_lin _ _ SBK) as (SL1 & SL2 & SL3 & SL4). unfold AIMG_HI in FL1, GL1, SL1.
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (SIN : In (HB p S 7176) LBN) by (left; reflexivity).
  assert (FIN : In (FB2 Fu) LBN) by (right; left; reflexivity).
  assert (SUB : forall b, In b LB -> In b LBN) by (intros b Hb; right; right; exact Hb).
  assert (SUB2 : forall b, In b LB -> In b (FB2 Fu :: LB)) by (intros b Hb; right; exact Hb).
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH4) as ND. unfold LBn in *.
  apply NoDup_cons_iff in ND. destruct ND as [NS ND1]. apply NoDup_cons_iff in ND1. destruct ND1 as [NF _].
  assert (SEPSF : S + 7176 <= Fu \/ Fu + 256 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p S 7176) (FB2 Fu) AH4 SIN FIN ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
  assert (RFU1 : rng RNG1 Fu 256) by (eapply rng_fp_le; [exact FPL| exact RF]).
  assert (RSFU1 : rng RNG1 SHF 32) by (eapply rng_fp_le; [exact FPL| exact RSF]).
  unfold client_agree in CA4.
  assert (FRM4 : uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL j8 j16 n trc m4).
  { eapply (uc_frame_agree ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL SPAB ltac:(lia) TOP S0SP); [| exact FRM3].
    eapply magree_mono; [exact CA4|]. exact uc_keep_cl. }
  assert (ESZ : Z.shiftr Zs 3 + 2147450880 = SHF + 4)
    by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (SHZ4 : shadow_bytes m4 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
  { destruct FRM4 as (_ & _ & _ & _ & _ & FSH4 & _). unfold UFSH in FSH4. rw_split FSH4 4%nat FSa FSr. rw_split FSr 14%nat FSz FSt.
    eapply (rw_cells_recast bsegs _ _ _ [CB (Z.to_nat 14) (repeat (Z_to_bv 8 0) (Z.to_nat 14))]) in FSz; [| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity| reflexivity].
    rewrite ESZ. replace (SHF + 4) with (Z.shiftr Fu 3 + 2147450884) by lia.
    apply (shadow_bytes_of_rw_cells_repeat bsegs _ _ 14 0 FSz); [lia|]. apply no_image_asan. pose proof (Z.shiftr_nonneg Fu 3) as X. lia. }
  eapply evtF_mono.
  { eapply (uc_first gp tp sp FR fc D F1 Fu S lo SPA RNG1 SL ESL F256 FBK RFU1 RSFU1);
      [exact MI4| exact (proj1 FRM4)| exact STRM4| exact SHZ4| exact N26
      | eapply rng_sub'; [eapply rng_fp_le; [exact FPL| exact RSTK]| lia]| lia| lia]. }
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & STRM5).
  assert (AG5 : magree bsegs (fun a => outside [(Fu + 32, Fu + 144)] a) m4 m5) by exact (magree_of_munch bsegs _ m4 m5 MU5 WM5).
  assert (FW5 : Forall wclr [(Fu + 32, Fu + 144)]) by (constructor; [eapply wclr_ablk; [exact FBK| lia| lia]| constructor]).
  assert (AH5 : AHEAP AI L RNG1 (aps_m sA1) (HB p S 7176 :: FB2 Fu :: LB) m5).
  { eapply (AI_frame AI _ _ _ _ m4 m5 _ AH4 MU5 WM5). constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 Fu 256); [exact FIN| lia| lia]| constructor]. }
  assert (UOUT : forall a, uset a -> ~ (Fu <= a < Fu + 256)).
  { intros a U. exact (uset_outside_fake RNG1 _ _ m4 2 Fu 256 a AH4 SUB FIN FBK U). }
  assert (US5 : ustatics m5).
  { eapply ustatics_agree; [| eapply ustatics_agree; [| exact US3]].
    - eapply magree_mono; [exact AG5|]. intros a U. cbn [outside]. pose proof (UOUT a U). split; [lia| exact I].
    - eapply magree_mono; [exact CA4|]. intros a U. split; [apply uset_client; [exact SUB2| exact U]|].
      intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr. pose proof (UOUT a U). lia. }
  destruct US5 as (VSH5 & TSH5 & (obr & OBB5) & SHOB5 & PBY5).
  assert (FRM5 : uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL j8 j16 n trc m5).
  { eapply (uc_frame_agree ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) SL SPAB ltac:(lia) TOP S0SP); [| exact FRM4].
    eapply magree_mono; [exact AG5|]. intros a KP. cbn [outside]. destruct (uc_keep_cl a KP) as [_ NW].
    pose proof (not_in_ranges_hd _ _ _ _ NW). split; [lia| exact I]. }
  assert (PF5 : magree bsegs UPF m m5).
  { assert (POUT : forall a, UPF a -> ~ (Fu <= a < Fu + 256)).
    { intros a [HC _]. pose proof (client_outside_blk AI L RNG1 _ _ LB m4 (FB2 Fu) SP a AH4 FIN NF SUB FBK ltac:(lia) HC) as X. cbn [ab_addr ab_size] in X. exact X. }
    eapply magree_trans; [exact PF3|]. eapply magree_trans.
    - eapply magree_mono; [exact CA4|]. intros a PA. pose proof (POUT a PA). destruct PA as [HC _]. split.
      + eapply aclient_addr_weaken; [exact SUB2| | exact HC]. lia.
      + intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr. lia.
    - eapply magree_mono; [exact AG5|]. intros a PA. cbn [outside]. pose proof (POUT a PA). split; [lia| exact I]. }
  assert (ISTC5 := ISTC4). eapply rw_cells_transport in ISTC5; [| exact MU5| exact WM5| rewrite istate_cells_size; cbn [disjoint_from]; split; [lia| exact I]].
  assert (JARR5 := JARR4). eapply rw_cells_transport in JARR5; [| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
  assert (TAIL5 := TAIL4). eapply rw_cells_transport in TAIL5; [| exact MU5| exact WM5| cbn [disjoint_from cells_size csize itail_cells Nat.add]; split; [lia| exact I]].
  assert (ST5 : stk bsegs m5 lo SPA) by (eapply stk_transport_disjoint; [exact ST4| exact MU5| exact WM5| cbn [disjoint_from]; split; [lia| exact I]]).
  assert (SHZ5 : shadow_bytes m5 (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
  { eapply shadow_bytes_munch_wclr; [exact SHZ4| exact MU5| exact FW5| |]; rewrite ESZ; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold KLS; Z.div_mod_to_equations; lia. }
  destruct (blob_split3 bsegs m5 (S + 168) 6992 jarr 640 576 JARR5 ltac:(lia) ltac:(lia) ltac:(lia)) as (b1 & b2 & b3 & B1 & B2 & B3).
  replace (S + 168 + 640) with (S + 808) in B2 by lia. replace (S + 168 + 640 + 576) with (S + 1384) in B3 by lia.
  change (Z.to_nat 640) with (2 * 320)%nat in B1. change (Z.to_nat 576) with (2 * 288)%nat in B2. change (Z.to_nat (6992 - 640 - 576)) with (4 * 1444)%nat in B3.
  destruct (f16arr_of_blob bsegs _ _ _ _ B1) as (lf & LENS5 & LFR). destruct (f16arr_of_blob bsegs _ _ _ _ B2) as (wf & WORK5 & WFR).
  destruct (f32arr_of_blob bsegs _ _ _ _ B3) as (cf & CDS5 & CFR). destruct (f8arr_of_blob bsegs _ _ _ _ OBB5) as (fo & OUT5 & FOR).
  set (nz := fun w : word => bv_unsigned w mod 4294967296).
  assert (NZR : forall w, 0 <= nz w < 4294967296) by (intros w; unfold nz; apply Z.mod_pos_bound; lia).
  set (st0 := st_u2_init (nz len) (nz off) (nz ext) (nz lb) (nz db) (nz ncode) (nz nlen) (nz ndist) (nz have)).
  set (v0 := UVW lf cf wf fo (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) dt (Z_to_bv 64 1) reserved p1 p2 p3
                 (Z_to_bv 64 0) (Z_to_bv 64 32768) check (Z_to_bv 64 0) (Z_to_bv 64 (-1)) was pad).
  exists st0, v0, m5. do 13 eexists. split; [reflexivity|].
  unfold uc_inv.
  split; [exact AH5|].
  split.
  {
    unfold inf_objs. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w].
    split; [split; [exact FIN| split; [reflexivity| split; [exact F256| exact FBK]]]|].
    split.
    { split; [exact SHZ5|]. split; [eapply rng_sub'; [exact RFU1| lia]|].
      split; [| rewrite shadE; exact RSFU1]. destruct FRM5 as (_ & _ & _ & _ & _ & FSH5 & _). rewrite shadE.
      eapply rw_cells_wr_at; [exact FSH5|]. unfold UFSH. cbn [cells_size csize Nat.add]. lia. }
    split.
    { exists p. split; [exact SIN|]. destruct PAY as [(pd & PDI & NPOS)|(N0 & DE)]; [left| right; split; assumption].
      exists pd. split; [exact (SUB _ PDI)|]. split; [exact NPOS|].
      pose proof (AI_hb_ids AI _ _ _ _ _ AH4) as NDI. unfold hb_ids in NDI. cbn [flat_map ab_kind app] in NDI. fold (hb_ids LB) in NDI.
      apply NoDup_cons_iff in NDI. destruct NDI as [NI _]. intros ->. apply NI. eapply in_hb_ids. exact PDI. }
    split; [left; reflexivity|].
    split; [intros Fa na Fb nb [E|[E|E]] [E'|[E'|E']]; try discriminate E; try discriminate E'; exact (NL0 _ _ _ _ E E')|].
    split; [reflexivity|]. split; [lia|]. split; [exact OBC|].
    split; [unfold A_OUTBUF; change (Z.shiftr 6341056 3 + 2147450880) with 2148243512; change (2148243512 + 32768) with 2148276280; exact SHOB5|].
    split; [eapply rng_fp_le; [exact FPL| exact ROB]|].
    split; [unfold A_OUTBUF; change (Z.shiftr 6341056 3 + 2147450880) with 2148243512; eapply rng_fp_le; [exact FPL| exact RSOB]|].
    split. { destruct PAY as [(pd & PDI & _)|(_ & ->)]; [| lia]. pose proof (LBH _ PDI) as X. apply ablk_lin in X. cbn [ab_addr] in X. unfold AIMG_HI in X. lia. }
    split; [exact N26|]. split; [exact D16|]. split; [exact PFO|]. split; [exact PLEN|].
    split.
    { destruct PAY as [(pd & PDI & _)|(N0 & DE)].
      - destruct (AI_block AI _ _ _ _ _ _ _ _ AH5 (SUB _ PDI)) as (_ & _ & _ & _ & ABS & _).
        pose proof (LBH _ PDI) as X. apply ablk_lin in X. cbn [ab_addr ab_size] in X.
        apply ablock_unpoisoned; [exact ABS| Z.div_mod_to_equations; lia| lia| lia| lia].
      - destruct UNP as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. lia. }
    split; [eapply rng_fp_le; [exact FPL| exact RD]|]. split; [eapply rng_fp_le; [exact FPL| exact RSD]|].
    split; [exact TSH5|].
    split.
    { intros Fa na Fb nb [E|[E|E]] [E'|[E'|E']]; try discriminate E; try discriminate E'; try (exfalso; exact (NL2 _ _ E)); try (exfalso; exact (NL2 _ _ E')).
      inversion E. inversion E'. lia. }
    split; [intros b [<-|[<-|Hb]]; [exact SBK| exact FBK| exact (LBH _ Hb)]|].
    split; [exact TABC1|]. split; [exact TABC2|]. intros X. exfalso. exact (X eq_refl). }
  split.
  { exact (ainv_u2_init S D n OB (8 * (n - 0) + 0 + (262144 - 0)) lf cf _ _ _ _ _ _ _ _ _ ltac:(lia) LFR CFR
                        (NZR len) (NZR off) (NZR ext) (NZR lb) (NZR db) (NZR ncode) (NZR nlen) (NZR ndist) (NZR have)). }
  split; [cbv; discriminate|].
  split.
  {
    unfold uc_emem, inf_emem. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w v_lf v_cf v_wf v_fo v_zti v_zto v_zmsg v_zopq v_zdt v_zadl v_zres v_zp1 v_zp2 v_zp3
                                   v_havedict v_dmax v_check v_total v_back v_was v_pad v0].
    unfold st0, st_u2_init. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
    unfold wsz. cbn [icx_of c_w Z.eqb cp_addrA]. unfold HEAD, A_OUTBUF.
    replace (D + 0) with D by lia. replace (n - 0) with n by lia. replace (6341056 + 0) with 6341056 by lia. replace (262144 - 0) with 262144 by lia.
    split; [exact STRM5|].
    split.
    { eapply rw_cells_recast; [exact ISTC5| cbn; repeat split; exact I| | reflexivity].
      unfold istate_cells. cbn [cells_bytes cbytes app]. unfold nz. rewrite !le4_norm. replace (S + 1384 + 4 * 0) with (S + 1384) by lia. reflexivity. }
    split; [exact LENS5|]. split; [exact WORK5|]. split; [exact CDS5|]. split; [exact TAIL5|]. split; [exact OUT5|]. split; [exact PBY5|].
    split; [split; [intros i _; apply WFR| intros i _; apply FOR]|].
    split; [| split; [intros X; exfalso; exact (X eq_refl)| unfold back_ok; cbn [t_mode]; split; intros E; cbv in E; discriminate E]].
    exists []. change (Z.to_nat (262144 - 262144)) with 0%nat.
    destruct OBB5 as [[_ (OA & OB' & _)] OW]. cbn [cells_bytes cbytes app length] in OB'. cbn [cells_size csize Nat.add] in OW.
    split; [split; [cbn; split; [reflexivity| exact I]|]|].
    - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
    - cbn [cells_size csize Nat.add]. destruct OW as (W1 & W2 & _). split; [lia|]. split; [lia|]. intros i Hi. lia. }
  split; [exact ST5|]. split; [exact MI5|]. split; [exact FRM5|]. split; [exact PF5|].
  split; [eapply aps_ok_rest; [exact RS1| exact OK]|]. split; [exact RS1|]. split; [exact FPL|].
  left. split; reflexivity.
Qed.
End Start.

Theorem uc_body : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  implMAC RNG (fuzz_oneAC AAllocAsan payload) s
    (fun (r : Z) (s' : APS) (RNG' : footprint) (ms' : machine_state) =>
       r = 0 /\ uc_final AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L lo LB m RNG s SL tt s' RNG' ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6341056) (Z_to_bv 64 DL) (Z_to_bv 64 D) (Z_to_bv 64 SL) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 A_UNCOMPRESS2) fc None m (seg_rom bsegs)).
Proof.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
  set (QF := fun (r : Z) (s' : APS) (RNG' : footprint) (ms' : machine_state) =>
               r = 0 /\ uc_final AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L lo LB m RNG s SL tt s' RNG' ms').
  pose proof uspa_f as (SPAB & SPA32). pose proof LOS as LOS'. unfold UC_STACK in LOS'.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; lia).
  eapply implMAC_evtF; [apply uc_head|]. cbv beta.
  intros ms3 (Fu & m3 & y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & j8 & j16 & p1 & ti & no & ao & p2 & to & msg & state & dt & p3 & adler & reserved
              & -> & F256 & FBK & RF & RSF & AH3 & MI3 & STL3 & FRM3 & STRM3 & PF3 & US3).
  pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  unfold fuzz_oneAC, HarnessC.fuzz_one, Client.CLIENT_PRE, Client.CLIENT_OPT.
  change (ProgA.amalloc AAllocAsan) with amalloc_M. change (ProgA.afree AAllocAsan) with afree_M. change (ProgA.aptr AAllocAsan) with AsanCtrl.aptr.
  unfold Client.STATE_SIZE, Client.WINDOW_SIZE. cbn [alloc_all length].
  apply implMAC_lift_bind_assoc.
  eapply implMAC_lift_bind.
  { apply implMA_unfold.
    eapply (INIT L RNG (Z_to_bv 64 576820) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 (Fu + 32)) (Z_to_bv 64 141152) (Z_to_bv 64 112)
                 (* [U14B] A2: the combined inflateInit_stmtA keeps its (unused) binder tr; G's ASan statement dropped it *)
                 y13 y14 y15 y16 y17 _ _ _ _ _ _ _ _ _ _ y28 y29 y30 y31 FR fc m3 s (FB2 Fu :: LB) Fu (Fu + 32) lo (bv_unsigned ra :: trc));
      [exact AH3| split; [left; reflexivity| split; [reflexivity| split; [exact F256| exact FBK]]]
      | | exact STRM3| exact (u2_img_of_aheap AI _ _ _ _ _ AH3)| destruct US3 as (V & _); exact V
      | rewrite USPA; exact STL3| exact LOC| rewrite USPA; unfold INIT_STACK; lia| rewrite USPA; Z.div_mod_to_equations; lia| exact MI3| exact TPE
      | reflexivity| reflexivity| reflexivity| rewrite unsigned_lit by lia; lia| rewrite USPA; lia
      | exact UI0| exact RSTK| exact RIMG| exact RISH| exact OK].
    -
      destruct FRM3 as (_ & _ & _ & _ & _ & FSH3 & _).
      assert (ESZ : Z.shiftr (Fu + 32) 3 + 2147450880 = Z.shiftr Fu 3 + 2147450880 + 4)
        by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
      split.
      { pose proof FSH3 as FS'. unfold UFSH in FS'. rw_split FS' 4%nat FSa FSr. rw_split FSr 14%nat FSz FSt.
        eapply (rw_cells_recast bsegs _ _ _ [CB (Z.to_nat 14) (repeat (Z_to_bv 8 0) (Z.to_nat 14))]) in FSz; [| cbn; split; [reflexivity| exact I]| vm_compute; reflexivity| reflexivity].
        rewrite ESZ. replace (Z.shiftr Fu 3 + 2147450880 + 4) with (Z.shiftr Fu 3 + 2147450884) by lia.
        apply (shadow_bytes_of_rw_cells_repeat bsegs _ _ 14 0 FSz); [lia|]. apply no_image_asan. pose proof (Z.shiftr_nonneg Fu 3) as X. lia. }
      split; [eapply rng_sub'; [exact RF| lia]|].
      split; [| rewrite shadE; exact RSF]. rewrite shadE. eapply rw_cells_wr_at; [exact FSH3|]. unfold UFSH. cbn [cells_size csize Nat.add]. lia. }
  intros r sA1 RNG1 ms4 POST. unfold init_post in POST. rewrite USPA in POST.
  destruct POST as (FPL & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & -> & MI4 & ST4 & RS1 & CA4 & REST).
  destruct r as [p|]; [| contradiction].
  destruct REST as (S & check & len & off & ext & lb & db & ncode & nlen & ndist & have & sane_pad & jarr & was & pad & AH4 & S16 & SBK & STRM4 & ISTC4 & JARR4 & TAIL4).
  apply implMAC_liftretb. cbn [length Nat.ltb Nat.leb].
  replace (ret_pc (Z_to_bv 64 576820)) with (Z_to_bv 64 576820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (RF1' : rng RNG1 F1 64) by (eapply rng_fp_le; [exact FPL| exact RF1]).
  eapply (implMAC_evtF RNG1 _ sA1 _
            (fun ms1 => uc_end AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) lo S D n payload p LB j8 j16 n trc m RNG s SL
                               0 RNG1 sA1 (LBn Fu S p LB) ms1
                        \/ implMA RNG1 (amalloc_M 32768) sA1
                             (uc_postW AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) lo S D n payload p LB j8 j16 n trc m RNG s SL
                                       RNG1 sA1) ms1)).
  { eapply evtF_cut.
    { eapply (uc_start Fu m3 j8 j16 F256 FBK RF RSF FRM3 PF3 US3 RNG1 sA1 p S m4 check len off ext lb db ncode nlen ndist have was pad no ao (Z_to_bv 64 0) reserved p1 p2 p3 jarr
                       FPL MI4 ST4 RS1 CA4 AH4 S16 SBK STRM4 ISTC4 JARR4 TAIL4). }
    cbv beta. intros ms5 (st & v & m5 & z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & -> & INV).
    eapply (uc_loopN AI rng_fs rng_fs_mono INF_W INF_N gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 (fflag L 2 Fu) lo S D n payload p LB
                     j8 j16 n trc m RNG s SL ESL LOC LOS SPAB SPA32 SPTOP F256 FBK F1128 F1B F1IN SBK S0SP TPE RAOK TRL UINB RF RSF RSTK RIMG RISH RFS N26
                     (Datatypes.S (Z.to_nat (umu n st))) RNG1 sA1 st v m5 0x8cf4c); [lia| right; reflexivity| exact INV]. }
  cbv beta. intros ms6 [UE|IMPL].
  -
    apply implMAC_choice_r. apply implMAC_lift. change (implMA RNG1 (HarnessC.fuzz_without afree_M [p]) sA1 QF ms6). unfold HarnessC.fuzz_without.
    eapply implMA_bind.
    { eapply (uc_tail AI fflag AI_fake_flag AI_fake_release END gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 (fflag L 2 Fu) lo S D n payload p LB
                      j8 j16 n trc m RNG s SL ESL LOC LOS ESPA SP16 SPTOP F256 FBK F1B F1IN LBH SBK OBC TPE eq_refl UF1 UF2 RF RSF RF1 RSDL RSSL RSTK RIMG
                      false 0 RNG1 sA1 (LBn Fu S p LB) p ms6); [split; reflexivity| exact UE]. }
    intros u s' RNG' ms' FIN. apply implMA_ret. apply evtF_done. destruct u. unfold QF. split; [reflexivity| exact FIN].
  -
    apply implMAC_choice_l. apply implMAC_lift. change (implMA RNG1 (HarnessC.fuzz_with amalloc_M afree_M [32768] [p]) sA1 QF ms6).
    unfold HarnessC.fuzz_with. cbn [alloc_all].
    eapply (implMA_bind _ _ _ _ (fun ps' s' RNG' ms' => exists pw Wd, ps' = [pw; p] /\
              uc_end AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu (fflag L 2 Fu) lo S D n payload p LB j8 j16 n trc m RNG s SL
                     Wd RNG' s' (HB pw Wd 32768 :: LBn Fu S p LB) ms')).
    { eapply implMA_bind; [exact IMPL|].
      intros r s' RNG' ms' PW. unfold uc_postW in PW. destruct PW as (FPL' & RS' & PW). destruct r as [pw|]; [| contradiction].
      destruct PW as (Wd & WNZ & UE). apply implMA_ret. apply evtF_done. exists pw, Wd. split; [reflexivity| exact UE]. }
    intros ps' s' RNG' ms' (pw & Wd & -> & UE).
    eapply implMA_bind.
    { eapply (uc_tail AI fflag AI_fake_flag AI_fake_release END gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 (fflag L 2 Fu) lo S D n payload p LB
                      j8 j16 n trc m RNG s SL ESL LOC LOS ESPA SP16 SPTOP F256 FBK F1B F1IN LBH SBK OBC TPE eq_refl UF1 UF2 RF RSF RF1 RSDL RSSL RSTK RIMG
                      true Wd RNG' s' (HB pw Wd 32768 :: LBn Fu S p LB) pw ms'); [reflexivity| exact UE]. }
    intros u s'' RNG'' ms'' FIN. apply implMA_ret. apply evtF_done. destruct u. unfold QF. split; [reflexivity| exact FIN].
Qed.
End Body.
End U2c.
End CANSEC1.
