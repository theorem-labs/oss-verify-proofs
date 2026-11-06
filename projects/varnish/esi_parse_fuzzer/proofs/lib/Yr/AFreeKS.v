(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB3 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQWf2 AQPart ACover ABudget ANodijx APgGeo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ANod9v0 AFreeB6 AFreeR AFreeR2 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRP AFreeRQ AFreeRU AFreeRC AWrapKit ACoresk AFreeWD AFreeX1 AFreeX2 AFreeX3 AFreeGD0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKG AFreeKT AFreeKR AFreeKU.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeWD OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeGD0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR.AFreeKX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR.AFreeKM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKG OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.
Ltac splits := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac side_nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac side_one := multimatch goal with H : _ \/ _ |- _ =>
  repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end; lia end.
Ltac sidetac K := cbn [disjoint_from cells_size csize Nat.add Nat.mul length unmap_frame dorec_frame app]; rewrite ?upd_length, ?repeat_length;
  clear - K; decompose [and] K; unfold apart, AMallocA.apart in *; kung_all;
  first [ solve [ splits; first [ exact I | solve [side_nodisj; lia] | side_one ] ] | lia ].
(* [comment removed for export] *)
Ltac sdt K := sidetac K.
Ltac sdtF K := sidetac K.
Ltac nexc := let X := fresh "X" in let Xe := fresh "Xe" in intros X; unfold AFreeX3.EXC, ia_blk in X;
  destruct X as [X|[X|[X|[X|[X|[X|[[Xe X]|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]]; kung_all; first [lia | congruence].

(* [comment removed for export] *)
Lemma kbytes_zero_raw : forall (m : mem) a n, bytes_at rsegs m a (repeat (Z_to_bv 8 0) n) -> 0x60a000 <= a ->
  forall k, 0 <= k < Z.of_nat n -> m (wz (a + k)) = Some (Z_to_bv 8 0).
Proof.
  (intros m a n; (first [ intro dR_38; dand3 dR_38 as B0 B1 B | intros (B0 & B1 & B) ]); intros Ha k Hk). rewrite repeat_length in B1.
  specialize (B (Z.to_nat k) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in B by lia.
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. unfold mrd, wa in B.
  destruct (m (wz (a + k))) as [b'|] eqn:E; try rewrite E in B; [congruence|].
  exfalso. pose proof (pa_seg_rom_none (wz (a + k)) ltac:(rewrite unsigned_lit by lia; right; lia)) as X.
  assert (Y : Some (Z_to_bv 8 0) = None) by (rewrite <- B; exact X). discriminate Y.
Qed.

(* [comment removed for export] *)
Lemma krecs_eager {Clg : Ceiling} : forall A kb i es more dead' s, nth_error (sr_chunks (a_sec A)) i = Some s ->
  pa_eager (recsA A kb i es more dead') = pa_eager A - map_size (cs_n s).
Proof.
  intros A kb i es more dead' s NTH. unfold pa_eager, aeager_of, aeager_of_. cbn [recsA a_pl a_reg a_sec sec_remove sr_chunks sr_reserved].
  rewrite (sec_eager_swap_remove (sr_chunks (a_sec A)) i s NTH). lia.
Qed.

Section RIter.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p0 n00 stkobj lo hi : Z) (TS : TSet).
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p0 n00 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p0 n00 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).

  (* [comment removed for export] *)
  Definition KS0_post (A : AState) (b cnt i0 : Z) (scr : list byte) (pw : word) (p n idx nf ca gA gM rf rfd mu mdv : Z) (vv : mem) : machine_state -> Prop := fun ms' =>
    let h := p - 6144 in let msz := map_size n in let thr := p_thr (a_pl A) in let pa := p_pa (a_pl A) in let hla := cs_map (sec_last A) in
    let nch := Z.of_nat (length (sec_words A)) in
    exists (t0'' t1'' t2'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (m' : mem),
    ms' = MSsvc (mkR (wz ldealloc_resume) (wz (dsp + -32)) gp (cl_tp LPA) t0'' t1'' t2'' (wz h) (wz h)
                     (wz (a8_pbeg h)) (wz (a8_len h msz)) (wz 4) (wz 4) a4'' a5'' a6'' (wz 233)
                     (wz msz) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i0)) (wz (cnt + 16)) (wz (16 + i0)) s10 s11 t3'' t4'' t5'' t6'')
                F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' dsp (dorec_fr thr scr)
    /\ rw_cells rsegs m' (b + 24 + 8 * i0) [C8 pw]
    /\ rw_cells rsegs m' (dsp + -32) [C8 (wz LMA_L); C8 (wz 0xb1d58); C8 (wz T); C8 (wz dorec_retpc)]
    /\ rw_cells rsegs m' 0xb1dd0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0xb1de8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))]
    /\ rw_cells rsegs m' 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
    /\ rw_cells rsegs m' 0xb2018 [C8 (wz (gA - msz)); C8 (wz (gM - msz))]
    /\ u64arr rsegs m' pa (upd (sec_words A) (Z.to_nat idx) (wz hla))
    /\ rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n)); C8 (wz idx)]
    /\ (hla = h \/ rw_cells rsegs m' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz idx)])
    /\ rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))]
    /\ rw_cells rsegs m' (thr + 2888) [C8 (wz mu); C8 (wz mdv)]
    /\ bytes_at rsegs m' (sh h) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8)))
    /\ munch [(dsp - 112, dsp); (0xb2000, 0xb2004); (thr + 2840, thr + 2856); (0xb1dd0, 0xb1dd9); (0xb1de8, 0xb1df8);
              (0xb2018, 0xb2028); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32); (sh h, sh h + msz / 8); (thr + 2888, thr + 2904)] vv m'
    /\ wmono rsegs vv m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (dsp + -32).

  (* [comment removed for export] *)
  Definition KS1_post (A : AState) (b cnt i0 : Z) (scr : list byte) (pw : word) (p n idx nf ca gA gM rf rfd mu mdv : Z) (vv : mem) : machine_state -> Prop := fun ms' =>
    let h := p - 6144 in let msz := map_size n in let thr := p_thr (a_pl A) in let pa := p_pa (a_pl A) in let hla := cs_map (sec_last A) in
    let nch := Z.of_nat (length (sec_words A)) in
    exists (t0'' t1'' t2'' a3'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (uscr : list byte) (m' : mem),
    ms' = MSsvc (mkR (wz unmap_resume) (wz (dsp + -48)) gp (cl_tp LPA) t0'' t1'' t2'' (wz msz) (wz 0)
                     (wz h) (wz msz) (wz 0) a3'' a4'' a5'' a6'' (wz 215)
                     (wz h) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i0)) (wz (cnt + 16)) (wz (16 + i0)) s10 s11 t3'' t4'' t5'' t6'')
                F (wz munmap_ecall_pc) (wz 215) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' dsp (dorec_fr thr scr)
    /\ rw_cells rsegs m' (b + 24 + 8 * i0) [C8 pw]
    /\ rw_cells rsegs m' (dsp + -48) (unmap_frame uscr (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_retpc))
    /\ rw_cells rsegs m' 0xb1dd0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0xb1de8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))]
    /\ rw_cells rsegs m' 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
    /\ rw_cells rsegs m' 0xb2018 [C8 (wz (gA - msz)); C8 (wz (gM - msz))]
    /\ u64arr rsegs m' pa (upd (sec_words A) (Z.to_nat idx) (wz hla))
    /\ rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n)); C8 (wz idx)]
    /\ (hla = h \/ rw_cells rsegs m' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz idx)])
    /\ rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))]
    /\ rw_cells rsegs m' (thr + 2888) [C8 (wz (mu + 1)); C8 (wz (mdv + msz))]
    /\ munch [(dsp - 112, dsp); (thr + 2888, thr + 2904)] vv m'
    /\ wmono rsegs vv m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (dsp + -48).

  (* [comment removed for export] *)
  Definition KS2_post (A : AState) (b cnt i0 : Z) (scr : list byte) (pw : word) (vv : mem) : machine_state -> Prop := fun ms' =>
    let thr := p_thr (a_pl A) in
    exists (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (m' : mem) (pc : Z),
    ms' = MS (it_regs (wz dsp) gp (cl_tp LPA) T b cnt s10 s11 (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (i0 + 1)) F (wz pc) fc None m' (seg_rom rsegs)
    /\ ((i0 + 1 < cnt /\ pc = dorec_callblk) \/ (i0 + 1 = cnt /\ pc = dorec_batchblk))
    /\ rw_cells rsegs m' dsp (dorec_fr thr scr)
    /\ rw_cells rsegs m' (b + 24 + 8 * i0) [C8 pw]
    /\ munch [(dsp - 48, dsp)] vv m' /\ wmono rsegs vv m' /\ mem_inv rsegs m' /\ stk rsegs m' lo dsp.

  Lemma step_sec : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (s : chunkS) (n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChS s) n) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i < length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_callblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i = length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_batchblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Proof.
    intros A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n CU NTH KM KD.
    destruct CU as [RI HIST MI ST PF RF DF [LEN ILE] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    set (es' := skipn (S i) (ba_entries b0)) in *. set (kb := ba_idx b0) in *.
    assert (L0 : a_qlimbo A = BA kb (QE (ChS s) n :: es') :: more).
    { rewrite L. unfold limbo_of. rewrite (skipn_cons_nth (ba_entries b0) i _ NTH). reflexivity. }
    destruct s as [hh n1].
    assert (EN : n1 = n).
    { destruct (wrL A W) as (L1 & _). rewrite L0 in L1. (first [ pose proof ((Forall_inv L1)) as dR_1; dand3 dR_1 as _ _ B3 | pose proof (Forall_inv L1) as (_ & _ & B3) ]). cbn [ba_entries] in B3.
      pose proof (Forall_inv B3) as [_ WE]. cbn [qe_chunk qe_n] in WE. (first [ dand3 WE as _ X2 _ | destruct WE as (_ & X2 & _) ]). cbn [cs_n] in X2. lia. }
    subst n1. remember (hh + 6144) as p eqn:EP. assert (HP : hh = p - 6144) by (clear -EP; lia). subst hh. clear EP.
    idtac "K-SEC entry ok".
    (* [comment removed for export] *)
    destruct (bk_idx A p n kb es' more W L0) as [idx NTI].
    (first [ pose proof ((bk_geo A v p n kb es' more AR W L0)) as dR_3; dand11 dR_3 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof (bk_geo A v p n kb es' more AR W L0) as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]).
    (first [ pose proof ((bk_shr A v p n kb es' more AR W L0)) as dR_4; dand4 dR_4 as SHA M512 D512 SIDE | pose proof (bk_shr A v p n kb es' more AR W L0) as (SHA & M512 & D512 & SIDE) ]).
    (first [ pose proof ((bk_sb A v p n kb es' more AR W L0)) as dR_5; dand4 dR_5 as SBL SBH HSB POUT | pose proof (bk_sb A v p n kb es' more AR W L0) as (SBL & SBH & HSB & POUT) ]).
    (first [ pose proof ((bk_nch A v p n kb es' more AR W L0)) as dR_6; dand4 dR_6 as NRC NLE NRES NEC | pose proof (bk_nch A v p n kb es' more AR W L0) as (NRC & NLE & NRES & NEC) ]).
    (first [ pose proof ((bk_pa A v p n kb es' more AR W L0)) as dR_7; dand5 dR_7 as PALO PAHI PAAL PARES PALE | pose proof (bk_pa A v p n kb es' more AR W L0) as (PALO & PAHI & PAAL & PARES & PALE) ]).
    pose proof (bk_arr A v p n kb es' more AR W L0) as ARR.
    pose proof (bk_nearest A v p n kb es' more AR W L0) as NRST.
    (first [ pose proof ((bk_last A v p n kb es' more AR W L0)) as dR_8; dand4 dR_8 as EL INL ELw HLU | pose proof (bk_last A v p n kb es' more AR W L0) as (EL & INL & ELw & HLU) ]).
    (first [ pose proof ((bk_regs A v AR)) as dR_9; dex5 dR_9 as srt nf ca gA gM; dand9 dR_9 as SRTR NFR CAR GAR GMR NSRT NFCA LCK GAM | pose proof ((bk_regs A v AR)) as dR_9; dand14 dR_9 as srt nf ca gA gM SRTR NFR CAR GAR GMR NSRT NFCA LCK GAM | destruct (bk_regs A v AR) as (srt & nf & ca & gA & gM & SRTR & NFR & CAR & GAR & GMR & NSRT & NFCA & LCK & GAM) ]).
    (first [ pose proof ((bk_consts A v AR)) as dR_10; dand4 dR_10 as CLMA CSEAL CSB CGCF | pose proof (bk_consts A v AR) as (CLMA & CSEAL & CSB & CGCF) ]).
    (first [ pose proof ((bk_thr_stats A v AR)) as dR_11; dex4 dR_11 as rf rfd mu mdv; dand6 dR_11 as RFR RFDR MUR MDR TRF TMU | pose proof ((bk_thr_stats A v AR)) as dR_11; dand10 dR_11 as rf rfd mu mdv RFR RFDR MUR MDR TRF TMU | destruct (bk_thr_stats A v AR) as (rf & rfd & mu & mdv & RFR & RFDR & MUR & MDR & TRF & TMU) ]).
    pose proof (bk_i A p n idx NTI) as [IR NTHw].
    pose proof (bk_hdr A v p n kb es' more AR W L0 idx NTI) as [HDRL CSR].
    (first [ pose proof ((bk_sep_h A v p n kb es' more AR W L0 idx NTI)) as dR_12; dand5 dR_12 as SEP_hp SEP_ht SEP_hc SEP_hn SEP_hf | pose proof (bk_sep_h A v p n kb es' more AR W L0 idx NTI) as (SEP_hp & SEP_ht & SEP_hc & SEP_hn & SEP_hf) ]).
    (first [ pose proof ((bk_sep_pa A v AR)) as dR_13; dand5 dR_13 as SEP_At SEP_Ac SEP_An SEP_Af _ | pose proof (bk_sep_pa A v AR) as (SEP_At & SEP_Ac & SEP_An & SEP_Af & _) ]).
    pose proof (bk_hl A v p n kb es' more AR W L0 idx NTI) as HLX. cbv zeta in HLX.
    (first [ dand11 HLX as HLLO HLHI HLAL HLE HLA HLC SEP_lp SEP_lt SEP_lc SEP_ln SEP_lf | destruct HLX as (HLLO & HLHI & HLAL & HLE & HLA & HLC & SEP_lp & SEP_lt & SEP_lc & SEP_ln & SEP_lf) ]).
    pose proof (bk_kgeo A m p n kb es' more AR W L0) as G.
    (first [ pose proof ((ka8_geo p n G)) as dR_15; dand15 dR_15 as G1 G2 G3 G4 G5 G6 G7 G8 GM1 GM2 GM3 GM4 _ BIG _ | pose proof (ka8_geo p n G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GM1 & GM2 & GM3 & GM4 & _ & BIG & _) ]).
    pose proof (sec_words_length A) as NCH.
    (* [comment removed for export] *)
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (RENT i _ (Nat.le_refl i) NTH) as LE.
    (first [ pose proof ((bk_cells A v p n kb es' more AR W L0 LE)) as dR_17; dex2 dR_17 as b1 ctxw; dand6 dR_17 as B1R B1M HDRU CTXW MAGW MPD | pose proof ((bk_cells A v p n kb es' more AR W L0 LE)) as dR_17; dand8 dR_17 as b1 ctxw B1R B1M HDRU CTXW MAGW MPD | destruct (bk_cells A v p n kb es' more AR W L0 LE) as (b1 & ctxw & B1R & B1M & HDRU & CTXW & MAGW & MPD) ]).
    (first [ pose proof ((bk_shadow A v p n kb es' more AR W L0 LE)) as dR_18; dand3 dR_18 as SHB SHL SHC | pose proof (bk_shadow A v p n kb es' more AR W L0 LE) as (SHB & SHL & SHC) ]).
    pose proof (ek_slot v (a_sb A) (batch_addr (a_sb A) b0) (ba_entries b0) i (batch_bytes b0) i _ RBAT (Nat.le_refl i) NTH LEN) as SLOT. cbn [qe_chunk qe_n] in SLOT.
    idtac "K-SEC kit ok".
    (* [comment removed for export] *)
    assert (L0P : a_qlimbo A = BA kb (QE (ChS (CS (p - 6144) n)) n :: es') :: more) by exact L0.
    pose proof (AFreeRP.head_in A kb _ more W L0) as HIN.
    pose proof (batch_known A v [] AR (BA kb (QE (ChS (CS (p - 6144) n)) n :: es')) HIN) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR kb KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_ri A v [] AR)) as dR_20; dand10 dR_20 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_21; dand6 dR_21 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_22; dand6 dR_22 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_CRI A v [] AR) as CRI.
    idtac "K-SEC cursor kit ok".
    (* [comment removed for export] *)
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *. set (cnt := Z.of_nat (length (ba_entries b0))) in *.
    assert (BLO' : kHighMemBeg <= b) by exact BLO. assert (BHI' : b + 8192 <= alloc_ceiling) by exact BHI.
    assert (HDRE : hdr_of sb (ChS (CS (p - 6144) n)) n = p + -16).
    { unfold hdr_of, user_of, sec_user_beg, kPageSize, kChunkHeaderSize. cbn [cs_map]. lia. }
    rewrite HDRE in SLOT.
    pose proof (MInv_perm _ _ _ _ _ _ (khull_perm0 A p n idx G NTI) (klhull_perm0 A p n idx G NTI) HMI) as HMI0.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (CR0 : hull_cover (REST A idx) (LREST A idx) (m_vm_lazy md) /\ lazy_free (m_vm_lazy md) (p - 6144) (p - 6144 + map_size n)).
    { pose proof LED as (LB1 & _ & _ & _ & _ & LB6 & _ & _ & LB9). split.
      - apply (kcover_REST A p n idx G NTI md); [| exact LB9|].
        + intros sc Hsc. (first [ pose proof ((sec_chunk_boundsT A sc (WFT_of_WFR A W) Hsc)) as dR; dand5 dR as B1 _ B3 B4 _ | pose proof (sec_chunk_boundsT A sc (WFT_of_WFR A W) Hsc) as (B1 & _ & B3 & B4 & _) ]).
          apply app_facts in B3. clear - B1 B3 CE. Zify.zify; xlia zchecker.
        + apply Forall_forall. intros sc Hsc. apply (proj1 (Forall_forall _ _) LB6). exact (in_firstn_skipn_S _ _ _ Hsc).
      - pose proof (proj1 (Forall_forall _ _) LB6 (CS (p - 6144) n) (nth_error_In _ _ NTI)) as EM. cbn [cs_map cs_n] in EM.
        pose proof (lazy_free_of_eager_map _ _ md EM) as LF. rewrite !unsigned_lit in LF by (clear - H5 MSZ HHI CE; Zify.zify; xlia zchecker). exact LF. }
    pose proof (khidc_H0p A p n idx G NTI) as HD0.
    pose proof (koff_segments_H A p n idx (H0p A p n idx) ltac:(right; right; right; apply Permutation_refl)) as OFF0.
    pose proof (koff_segments_H A p n idx (H1 A p n idx) ltac:(right; left; apply Permutation_refl)) as OFF1.
    pose proof (koff_segments_H A p n idx (H2 A p n idx) ltac:(right; right; left; apply Permutation_refl)) as OFF2.
    (first [ pose proof ((klen_facts0 p n G)) as dR_23; dand17 dR_23 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 _ _ MP _ _ PL PMZ | pose proof (klen_facts0 p n G) as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & _ & _ & MP & _ & _ & PL & PMZ) ]).
    assert (IL : (i < length (ba_entries b0))%nat) by exact (nth_error_Some_lt _ _ _ NTH).
    assert (DSPU : bv_unsigned (wz dsp) = dsp) by (apply unsigned_lit; clear -CE LOW SPHI HI47 SPR CEIL; lia).
    (* [comment removed for export] *)
    pose proof (batch_carved A v [] AR _ HIN) as CVb. cbn [ba_idx] in CVb.
    pose proof (carved_apart_pa A v [] AR _ CVb) as Dbpa. cbn [chunk_lo chunk_hi alloc_beg] in Dbpa. change (class_size kQuarantineBatchClass) with 8192 in Dbpa.
    pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CVb INL ltac:(discriminate)) as Dbl. rewrite AFreeKT.chunk_lo_S, AFreeKT.chunk_hi_S in Dbl.
    cbn [chunk_lo chunk_hi alloc_beg] in Dbl. change (class_size kQuarantineBatchClass) with 8192 in Dbl.
    (first [ pose proof ((bk_chunk A v AR _ INL)) as dR_24; dand6 dR_24 as LC1 LC2 LC3 LC4 LC5 _ | pose proof (bk_chunk A v AR _ INL) as (LC1 & LC2 & LC3 & LC4 & LC5 & _) ]).
    assert (SEP_bpa : apart b 8192 (p_pa (a_pl A)) (8 * Z.of_nat (length (sr_chunks (a_sec A))))).
    { unfold apart, b, batch_addr, sb. unfold kb in Dbpa. clear -Dbpa PALE. lia. }
    assert (SEP_bl : apart b 8192 (cs_map (sec_last A)) 32).
    { unfold apart, b, batch_addr, sb. unfold kb in Dbl. clear -Dbl LC4. lia. }
    assert (HLC0 : cs_map (sec_last A) = p - 6144 \/
                   ((p - 6144 + 32 <= cs_map (sec_last A) \/ cs_map (sec_last A) + 32 <= p - 6144) /\
                    rw_cells rsegs v (cs_map (sec_last A)) [C8 (wz (cs_map (sec_last A))); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A))));
                                                            C8 (wz (Z.of_nat (length (sr_chunks (a_sec A))) - 1))])).
    { destruct HLA as [E|AP]; [left; exact E|]. destruct HLC as [E|C]; [left; exact E| right]. split; [| exact C].
      unfold apart in AP. clear -AP MSZ. lia. }
    idtac "K-SEC S0 facts ok".
    (* [comment removed for export] *)
    unfold it_cfgG. fold sb. fold b cnt.
    eapply (srz_evt_restrict rsegs (H0p A p n idx) OFF0 pa_wxR _ (pa_eager A)
              (KS0_post A b cnt (Z.of_nat i) scr (wz (p + -16)) p n (Z.of_nat idx) nf ca gA gM rf rfd mu mdv v) _ md TS HMI0 HLT).
    { rewrite restrict_MS, <- HD0. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (kiter_sec_pre gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := 512 * kb) (pw := wz (p + -16)) (mh := p + -16) (pa := p_pa (a_pl A)) (u1 := 0) (u2 := 0) (srt := srt)
             (h := p - 6144) (msz := map_size n) (csz := needed_size2 n) (idx := Z.of_nat idx) (nf := nf) (ca := ca) (gA := gA) (gM := gM) (nsz := n)
             (st := CHUNK_QUARANTINE) (b1 := b1) (rf := rf) (rfd := rfd) (mu := mu) (md := mdv) (sealed := 1) (hs := sec_words A)
             (hl := wz (cs_map (sec_last A))) (hlb := wz (cs_map (sec_last A))) (hlm := wz (map_size (cs_n (sec_last A)))) (hls := wz (needed_size2 (cs_n (sec_last A))))
             (old := sshadow_quar n).
      all: rewrite ?DSPU, ?NCH, ?HLU.
      all: try assumption.
      all: try (first [ reflexivity
                      | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                      | unfold pa_tsd; clear; lia
                      | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                      | unfold cnt; clear -LEN IL; unfold kQuarantineBatchCount in LEN; lia
                      | clear -KB0 KBH; lia
                      | apply unsigned_lit; clear -H5 HHI CE MSZ; lia
                      | clear -N6 NR PIN; unfold kMaxPrimaryUser, REQ_MAX in NR; lia
                      | unfold CHUNK_QUARANTINE; clear; lia
                      | clear; lia
                      | clear -SEP_At PALE; unfold apart in *; lia
                      | clear -SEP_Ac PALE; unfold apart in *; lia
                      | clear -G5; lia
                      | exact (proj1 HDRU) ]).
      intros t0c t1c t2c a4c a5c a6c t3c t4c t5c t6c m2 DF2 ENT2 DLF2 NSRT2 NFCA2 LCK2 GAM2 ARR2 HDRL2 HLC2 TRF2 TMU2 SHZ MU2 WM2 MI2 ST2.
      unfold KS0_post. cbv zeta. first [ hotw_ex11 t0c t1c t2c a4c a5c a6c t3c t4c t5c t6c m2 | exists t0c, t1c, t2c, a4c, a5c, a6c, t3c, t4c, t5c, t6c, m2 ]. rewrite ?NCH.
      split; [reflexivity|]. splits; first [eassumption | match goal with |- ?g => idtac "S0post FAIL" g end]. }
    idtac "K-SEC S0 done".
    intros msr0 md1 Q0 HI1 SB1 Hcl0.
    (first [ dex11 Q0 as xt0 xt1 xt2 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mv0'; dand18 Q0 as -> P_df P_ent P_dlf P_nsrt P_nfca P_lck P_gam P_arr P_hdrl P_hlc P_trf P_tmu P_sh MU0 WM0 MI0 ST0 | dand29 Q0 as xt0 xt1 xt2 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mv0' -> P_df P_ent P_dlf P_nsrt P_nfca P_lck P_gam P_arr P_hdrl P_hlc P_trf P_tmu P_sh MU0 WM0 MI0 ST0 | destruct Q0 as (xt0 & xt1 & xt2 & xa4 & xa5 & xa6 & xt3 & xt4 & xt5 & xt6 & mv0' & -> & P_df & P_ent & P_dlf & P_nsrt & P_nfca & P_lck & P_gam & P_arr & P_hdrl & P_hlc
                    & P_trf & P_tmu & P_sh & MU0 & WM0 & MI0 & ST0) ]).
    rewrite unrestrict_MSsvc. unfold hclean in Hcl0. cbn [ms_mem MSsvc] in Hcl0.
    pose proof (same_but_materialized_frame _ _ SB1) as FRM1.
    assert (HH1 : m_halted md1 = None).
    { (first [ dand18 FRM1 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HLT. }
    (* [comment removed for export] *)
    pose proof (aobj_facts _ _ PT) as T'. pose proof (aobj_facts _ _ PC) as C'. pose proof (aobj_facts _ _ PALO) as PA'.
    pose proof (aobj_facts _ _ HLO) as HM'. pose proof (aobj_facts _ _ HLLO) as HL'.
    assert (SHR : 0x7fff8200 <= sh (p - 6144) /\ sh (p - 6144) + map_size n / 8 <= kHighMemBeg) by (clear -SIDE; kung_all; lia).
    assert (AG0 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo dsp a -> mv0' (wz a) = v (wz a)).
    { intros a Ha NE. apply MU0. rewrite (unsigned_lit a Ha). unfold AFreeX3.EXC in NE. cbn [outside]. splits; try exact I; intros X; apply NE.
      - left. clear -X LOW. lia.
      - do 14 right. exact X.
      - right; left. clear -X. lia.
      - do 7 right; left. exact X.
      - do 8 right; left. exact X.
      - do 9 right; left. exact X.
      - do 10 right; left. exact X.
      - do 11 right; left. exact X.
      - do 13 right; left. exact X.
      - do 2 right; left. exact X. }
    idtac "K-SEC AG0 ok".
    (* [comment removed for export] *)
    unfold a8_len.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz (a8_pbeg (p - 6144))) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz (a8_pend (p - 6144) (map_size n) - a8_pbeg (p - 6144))) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A2E : ms_gpr ms1 2 = wz 4) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    eapply (srz_madvise rsegs ms1 md1 (wz 233) TS HH1 eq_refl eq_refl).
    - eapply (kfsm_madvise_args A m md p n kb es' more); eassumption.
    - idtac "K-SEC N1 side goals ok".
      unfold madvise_eff. rewrite !A0E, !A1E, U2, PL. subst ms1.
      rewrite advance_apply_MSsvc, apply_mem_zeros, mkR_set_a0, lit_add_lit. change (madvise_ecall_pc + 4) with madvise_after_pc.
      set (md2 := madvise_model (wz (a8_pbeg (p - 6144))) (wz (a8_pend (p - 6144) (map_size n) - a8_pbeg (p - 6144))) md1).
      assert (CR1 : hull_cover (REST A idx) (LREST A idx) (m_vm_lazy md1) /\ lazy_free (m_vm_lazy md1) (p - 6144) (p - 6144 + map_size n)) by (rewrite (sbm_lazy _ _ SB1); exact CR0).
      pose proof (kMInv_H1 A p n idx G (pa_eager A) md1 (kMInv_H0s A p n idx G (pa_eager A) md1 HI1 (proj1 CR1) (proj2 CR1)) (proj1 CR1) (proj2 CR1)) as HI2. fold md2 in HI2.
      assert (HH2 : m_halted md2 = None) by (unfold md2; rewrite madvise_model_halted; exact HH1).
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with m end.
      change (apply_zeros (munrestrict (hidc (H0p A p n idx)) m mv0') [(wz (a8_pbeg (p - 6144)), wz (a8_pend (p - 6144) (map_size n) - a8_pbeg (p - 6144)))])
        with (AFreeGD0.rm2 A m p n idx mv0').
      idtac "K-SEC N1 done".
      (* [comment removed for export] *)
      set (mv1 := AFreeGD0.mv1 A m p n idx mv0').
      pose proof (kT01 A m p n idx G mv0' Hcl0) as MU01. fold mv1 in MU01.
      pose proof (khop01 A m p n idx G mv0' Hcl0) as HOP01. fold mv1 in HOP01.
      pose proof (kMI1 A m p n idx G mv0' MI0) as MIv1. fold mv1 in MIv1.
      pose proof (kmv1_clean A m p n idx mv0') as Hcl1s. fold mv1 in Hcl1s.
      assert (AG1 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo dsp a -> mv1 (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (HOP01 a Ha); [exact (AG0 a Ha NE)|]. intros X. apply NE. unfold AFreeX3.EXC. do 13 right; left. clear -X G1 G6. lia. }
      (first [ pose proof ((khit_sep A (proj1 AR))) as dR_27; dand13 dR_27 as _ _ _ _ _ SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (khit_sep A (proj1 AR)) as (_ & _ & _ & _ & _ & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
      pose proof (aobj_facts _ _ DN01) as N0'. pose proof (aobj_facts _ _ DF01) as F0'.
      assert (AGq1 : forall x, img_quiet x -> mv1 (wz x) = v (wz x)).
      { intros x Hx. unfold img_quiet in Hx. apply AG1; [clear -Hx; lia|]. clear -Hx T' N0' F0' PA' HL' H5 SHR CEIL LOW CE IR. kung_all. nexc. }
      (* [comment removed for export] *)
      pose proof (conj F4 (conj G1 (conj SHR (conj CE (conj CEIL (conj LOW (conj T' (conj PA' (conj HM' (conj HL' (conj C' (conj IR (conj BLO' BHI'))))))))))))) as K01.
      assert (STv1 : stk rsegs mv1 lo (dsp + -32)) by (eapply stk_mu; [exact ST0| exact MU01| sdt K01]).
      assert (TCv1 : thread_cells mv1 (cl_tp LPA) pa_tsd (p_ctx (a_pl A)) thr).
      { apply (thread_cells_agq v mv1 AGq1 _ _ _ _ TC eq_refl ltac:(unfold pa_tsd; clear; lia)). intros k Hk.
        apply (AGapp A m p n kb es' more idx mv1 lo dsp AR W L0 NTI CEIL AG1 (p_ctx (a_pl A)) 0x10000);
          try (clear -Hk C' SP5 SEP_n0c SEP_f0c SEP_Ac SEP_lc SEP_hc LC4; unfold apart, AMallocA.apart in *; kung_all; lia). }
      idtac "K-SEC TCv1 ok".
      assert (P_df1 : rw_cells rsegs mv1 dsp (dorec_fr thr scr)) by (eapply rw_cells_mu; [exact P_df| exact MU01| sdt K01]).
      assert (P_ent1 : rw_cells rsegs mv1 (b + 24 + 8 * Z.of_nat i) [C8 (wz (p + -16))]).
      { eapply rw_cells_mu; [exact P_ent| exact MU01|]. pose proof (conj K01 (conj LEN IL)) as K01e. fold cnt in K01e. sdt K01e. }
      assert (P_dlf1 : rw_cells rsegs mv1 (dsp + -32) [C8 (wz LMA_L); C8 (wz 0xb1d58); C8 (wz T); C8 (wz dorec_retpc)]) by (eapply rw_cells_mu; [exact P_dlf| exact MU01| sdt K01]).
      assert (P_nsrt1 : rw_cells rsegs mv1 0xb1dd0 [C8 (wz (Z.of_nat (length (sec_words A)) - 1)); C1 (Z_to_bv 8 0)]) by (eapply rw_cells_mu; [exact P_nsrt| exact MU01| sdt K01]).
      assert (P_nfca1 : rw_cells rsegs mv1 0xb1de8 [C8 (wz (nf + 1)); C8 (wz (ca - map_size n))]) by (eapply rw_cells_mu; [exact P_nfca| exact MU01| sdt K01]).
      assert (P_lck1 : rw_cells rsegs mv1 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]) by (eapply rw_cells_mu; [exact P_lck| exact MU01| sdt K01]).
      assert (P_gam1 : rw_cells rsegs mv1 0xb2018 [C8 (wz (gA - map_size n)); C8 (wz (gM - map_size n))]) by (eapply rw_cells_mu; [exact P_gam| exact MU01| sdt K01]).
      assert (P_arr1 : u64arr rsegs mv1 (p_pa (a_pl A)) (upd (sec_words A) (Z.to_nat (Z.of_nat idx)) (wz (cs_map (sec_last A))))).
      { eapply u64arr_mu; [exact P_arr| exact MU01|]. pose proof (conj K01 (conj NCH PALE)) as K01a. sdt K01a. }
      assert (P_hdrl1 : rw_cells rsegs mv1 (p - 6144) [C8 (wz (p - 6144)); C8 (wz (map_size n)); C8 (wz (needed_size2 n)); C8 (wz (Z.of_nat idx))]) by (eapply rw_cells_mu; [exact P_hdrl| exact MU01| sdt K01]).
      assert (P_hlc1 : cs_map (sec_last A) = p - 6144 \/ rw_cells rsegs mv1 (cs_map (sec_last A)) [C8 (wz (cs_map (sec_last A))); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat idx))]).
      { destruct P_hlc as [E|C]; [left; exact E| right]. eapply rw_cells_mu; [exact C| exact MU01| sdt K01]. }
      assert (P_trf1 : rw_cells rsegs mv1 (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))]) by (eapply rw_cells_mu; [exact P_trf| exact MU01| sdt K01]).
      assert (P_tmu1 : rw_cells rsegs mv1 (thr + 2888) [C8 (wz mu); C8 (wz mdv)]) by (eapply rw_cells_mu; [exact P_tmu| exact MU01| sdt K01]).
      idtac "K-SEC mv1 cells ok".
      (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs (H1 A p n idx) OFF1 pa_wxR _ (pa_eager A)
                (KS1_post A b cnt (Z.of_nat i) scr (wz (p + -16)) p n (Z.of_nat idx) nf ca gA gM rf rfd mu mdv mv1) _ md2 TS HI2 HH2).
      { rewrite restrict_MS. change (mrestrict (hidc (H1 A p n idx)) (AFreeGD0.rm2 A m p n idx mv0')) with mv1.
        replace (dsp + -32) with (bv_unsigned (wz dsp) + -32) by (rewrite DSPU; reflexivity).
        eapply (kiter_sec_mid gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                  (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                  pa_tsd (p_ctx (a_pl A)) thr sb ri)
          with (kb := 512 * kb) (m7 := mv1) (pw := wz (p + -16)) (mh := p + -16) (pa := p_pa (a_pl A)) (u1 := 0) (u2 := 0)
               (h := p - 6144) (msz := map_size n) (csz := needed_size2 n) (idx := Z.of_nat idx) (nf := nf) (ca := ca) (gA := gA) (gM := gM) (nsz := n)
               (rf := rf) (rfd := rfd) (mu := mu) (md := mdv) (sealed := 1) (hs := sec_words A)
               (hl := wz (cs_map (sec_last A))) (hlb := wz (cs_map (sec_last A))) (hlm := wz (map_size (cs_n (sec_last A)))) (hls := wz (needed_size2 (cs_n (sec_last A)))).
        all: rewrite ?DSPU, ?NCH, ?HLU.
        all: try assumption.
        all: try (first [ reflexivity
                        | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                        | unfold pa_tsd; clear; lia
                        | unfold cnt; clear -LEN IL; unfold kQuarantineBatchCount in LEN; lia
                        | clear -KB0 KBH; lia
                        | clear -N6 NR PIN; unfold kMaxPrimaryUser, REQ_MAX in NR; lia
                        | clear; lia
                        | clear -SEP_At PALE; unfold apart in *; lia
                        | clear -SEP_Ac PALE; unfold apart in *; lia
                        | rewrite <- NCH; exact P_nsrt1
                        | exact 0 ]).
        all: try (intros yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 uscr mv1' DF1' ENT1' UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MI1' ST1';
                  unfold KS1_post; cbv zeta; first [ hotw_ex13 yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 uscr mv1' | exists yt0, yt1, yt2, ya3, ya4, ya5, ya6, yt3, yt4, yt5, yt6, uscr, mv1' ]; rewrite ?NCH;
                  split; [reflexivity|]; splits; first [eassumption | match goal with |- ?g => idtac "S1post FAIL" g end]).
        all: match goal with |- ?g => idtac "S1 REM" g end. }
      idtac "K-SEC S1 done".
      intros msr1 md3 Q1 HI3 SB3 Hcl1.
      (first [ dex13 Q1 as yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 uscr mv1'; dand17 Q1 as -> Q_df Q_ent UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MIv1' STv1' | dand30 Q1 as yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 uscr mv1' -> Q_df Q_ent UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MIv1' STv1' | destruct Q1 as (yt0 & yt1 & yt2 & ya3 & ya4 & ya5 & ya6 & yt3 & yt4 & yt5 & yt6 & uscr & mv1' & -> & Q_df & Q_ent & UF1 & Q_nsrt & Q_nfca & Q_lck & Q_gam & Q_arr & Q_hdrl & Q_hlc
                      & Q_trf & Q_tmu & MU1 & WM1 & MIv1' & STv1') ]).
      rewrite unrestrict_MSsvc. unfold hclean in Hcl1. cbn [ms_mem MSsvc] in Hcl1.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with (AFreeGD0.rm2 A m p n idx mv0') end.
      change (munrestrict (hidc (H1 A p n idx)) (AFreeGD0.rm2 A m p n idx mv0') mv1') with (AFreeGD0.rm3 A m p n idx mv0' mv1').
      pose proof (same_but_materialized_frame _ _ SB3) as FRM3.
      assert (HH3 : m_halted md3 = None).
      { (first [ dand18 FRM3 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HH2. }
      assert (MD2 : md2 = madvise_model (wz (a8_pbeg (p - 6144))) (wz (a8_pend (p - 6144) (map_size n) - a8_pbeg (p - 6144))) md1) by reflexivity.
      pose proof (kfsm_has A md p n idx NTI LED md1 md2 md3 SB1 MD2 SB3) as HAS3.
      pose proof (kfsm_eager A md p n idx NTI LED md1 md2 md3 SB1 MD2 SB3) as EM3.
      (* [comment removed for export] *)
      match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms3 := ms) end.
      assert (B0E : ms_gpr ms3 0 = wz (p - 6144)) by (subst ms3; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
      assert (B1E : ms_gpr ms3 1 = wz (map_size n)) by (subst ms3; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
      assert (PRU : page_round_up (wz (map_size n)) = wz (map_size n)) by (unfold page_round_up; rewrite U4, PMZ; reflexivity).
      eapply (srz_munmap_lazy rsegs ms3 md3 (wz 215) TS HH3 eq_refl eq_refl).
      { unfold munmap_args_ok. rewrite B0E, B1E, PRU, U3, U4, PMZ. unfold page_size, TASK_SIZE.
        split; [exact HAL|]. split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U4, unsigned_lit in E by lia; clear -E MP; lia|].
        split; [clear -HHI CE; lia| exact HAS3]. }
      unfold munmap_eff. rewrite B0E, B1E, PRU. subst ms3.
      rewrite advance_apply_MSsvc, apply_mem_unmaps, mkR_set_a0, lit_add_lit, munmap_model_modelL. change (munmap_ecall_pc + 4) with munmap_after_pc.
      set (md4 := munmap_modelL (wz (p - 6144)) (wz (map_size n)) md3).
      pose proof (kMInv_H2 A p n idx G (pa_eager A) md3 HI3 HAS3 EM3) as HI4. fold md4 in HI4.
      assert (HH4 : m_halted md4 = None) by (unfold md4; rewrite <- munmap_model_modelL, munmap_model_halted; exact HH3).
      change (apply_unmaps (AFreeGD0.rm3 A m p n idx mv0' mv1') [(wz (p - 6144), wz (map_size n))]) with (AFreeGD0.rm4 A m p n idx mv0' mv1').
      idtac "K-SEC N2 done".
      (* [comment removed for export] *)
      set (mv2 := AFreeGD0.mv2 A m p n idx mv0' mv1').
      pose proof (kT12 A m p n idx G mv0' mv1' Hcl1) as MU12. fold mv2 in MU12.
      pose proof (khop12 A m p n idx G mv0' mv1' Hcl1) as HOP12. fold mv2 in HOP12.
      pose proof (kMI2 A m p n idx G mv0' mv1' MIv1') as MIv2. fold mv2 in MIv2.
      assert (AG1' : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo dsp a -> mv1' (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (MU1 (wz a)); [exact (AG1 a Ha NE)|]. rewrite (unsigned_lit a Ha). cbn [outside].
        split; [| split; [| exact I]]; intros X; apply NE; unfold AFreeX3.EXC; [left; clear -X CEIL LOW; lia| do 2 right; left; exact X]. }
      assert (AG2 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo dsp a -> mv2 (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (HOP12 a Ha); [exact (AG1' a Ha NE)|]. intros X. apply NE. unfold AFreeX3.EXC. do 12 right; left. exact X. }
      assert (AGq2 : forall x, img_quiet x -> mv2 (wz x) = v (wz x)).
      { intros x Hx. unfold img_quiet in Hx. apply AG2; [clear -Hx; lia|]. clear -Hx T' N0' F0' PA' HL' H5 SHR CEIL LOW CE IR. kung_all. nexc. }
      assert (BFORM' : b = sb + 24 * 2^32 + 16 * (512 * kb)) by exact BFORM.
      pose proof (conj HHI (conj H5 (conj CE (conj CEIL (conj LOW (conj HSB (conj BFORM' (conj KB0 (conj KBH (conj LEN IL)))))))))) as K12. fold cnt in K12.
      assert (STv2 : stk rsegs mv2 lo (dsp + -48)) by (eapply stk_mu; [exact STv1'| exact MU12| sdt K12]).
      assert (UF2 : rw_cells rsegs mv2 (dsp + -48) (unmap_frame uscr (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_retpc))) by (eapply rw_cells_mu; [exact UF1| exact MU12| sdt K12]).
      assert (DF2 : rw_cells rsegs mv2 dsp (dorec_fr thr scr)) by (eapply rw_cells_mu; [exact Q_df| exact MU12| sdt K12]).
      assert (ENT2 : rw_cells rsegs mv2 (b + 24 + 8 * Z.of_nat i) [C8 (wz (p + -16))]) by (eapply rw_cells_mu; [exact Q_ent| exact MU12| sdt K12]).
      assert (CGCFv2 : ro_cells rsegs mv2 0xa9180 [C8 (wz CF)]) by (eapply ro_cells_agq; [exact AGq2| exact CGCF| intros k Hk; cbn in Hk; unfold img_quiet; clear -Hk; lia]).
      assert (CMLv2 : ro_cells rsegs mv2 (CF + 144) [C8 (wz 0)]).
      { eapply ro_cells_agq; [exact AGq2| exact (rk_CML A v [] AR)| intros k Hk; cbn in Hk; unfold img_quiet, ANodeA7.CF, ANodijx.CF; clear -Hk; lia]. }
      idtac "K-SEC mv2 cells ok".
      (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs (H2 A p n idx) OFF2 pa_wxR _ (pa_eager A - map_size n)
                (KS2_post A b cnt (Z.of_nat i) scr (wz (p + -16)) mv2) _ md4 TS HI4 HH4).
      { rewrite restrict_MS. change (mrestrict (hidc (H2 A p n idx)) (AFreeGD0.rm4 A m p n idx mv0' mv1')) with mv2.
        replace (dsp + -48) with (bv_unsigned (wz dsp) + -48) by (rewrite DSPU; reflexivity).
        eapply (iter_sec_post gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                  (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret) thr sb ri)
          with (kb := 512 * kb) (m8 := mv2) (pw := wz (p + -16)) (uscr := uscr).
        all: rewrite ?DSPU.
        all: try assumption.
        all: try (first [ reflexivity
                        | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                        | unfold cnt; clear -LEN IL; unfold kQuarantineBatchCount in LEN; lia
                        | clear -KB0 KBH; lia ]).
        - intros LT a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m' DF' ENT' MU2 WM2 MI2' ST2'.
          apply evt_done. unfold KS2_post. cbv zeta. first [ hotw_ex17 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m' dorec_callblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m', dorec_callblk ].
          split; [reflexivity|]. split; [left; split; [exact LT| reflexivity]|]. splits; assumption.
        - intros EQ a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m' DF' ENT' MU2 WM2 MI2' ST2'.
          apply evt_done. unfold KS2_post. cbv zeta. first [ hotw_ex17 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' m' dorec_batchblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m', dorec_batchblk ].
          split; [reflexivity|]. split; [right; split; [exact EQ| reflexivity]|]. splits; assumption. }
      idtac "K-SEC S2 done".
      intros msr2 md5 Q2 HI5 SB5 Hcl2.
      (first [ dex17 Q2 as za0 za1 za2 za3 za4 za5 za6 za7 zt0 zt1 zt2 zt3 zt4 zt5 zt6 mv2' pcf; dand8 Q2 as -> CASE DF' ENT' MU2 WM2 MIv2' STv2' | dand25 Q2 as za0 za1 za2 za3 za4 za5 za6 za7 zt0 zt1 zt2 zt3 zt4 zt5 zt6 mv2' pcf -> CASE DF' ENT' MU2 WM2 MIv2' STv2' | destruct Q2 as (za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt0 & zt1 & zt2 & zt3 & zt4 & zt5 & zt6 & mv2' & pcf & -> & CASE & DF' & ENT' & MU2 & WM2 & MIv2' & STv2') ]).
      rewrite unrestrict_MS. unfold hclean in Hcl2. cbn [ms_mem MS] in Hcl2.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with (AFreeGD0.rm4 A m p n idx mv0' mv1') end.
      change (munrestrict (hidc (H2 A p n idx)) (AFreeGD0.rm4 A m p n idx mv0' mv1') mv2') with (AFreeGD0.rm5 A m p n idx mv0' mv1' mv2').
      set (rm5 := AFreeGD0.rm5 A m p n idx mv0' mv1' mv2').
      idtac "K-SEC post S2".
      (* [comment removed for export] *)
      set (A' := recsA A kb idx es' more (dead2 p n)).
      assert (AG2' : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo dsp a -> mv2' (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (MU2 (wz a)); [exact (AG2 a Ha NE)|]. rewrite (unsigned_lit a Ha). cbn [outside].
        split; [| exact I]. intros X; apply NE; unfold AFreeX3.EXC; left; clear -X CEIL LOW; lia. }
      assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ AFreeX3.holeD p n a -> v (wz a) <> None -> mv2' (wz a) <> None).
      { intros a H0 H1 H2 NH Hv. unfold AFreeX3.holeD in NH.
        apply (wmono_NNR _ _ a WM2 H1 ltac:(lia)). apply (kT12_NN A m p n idx G mv0' mv1' Hcl1 (wz a)); [rewrite (unsigned_lit a) by lia; clear -NH; lia|].
        apply (wmono_NNR _ _ a WM1 H1 ltac:(lia)). apply (kT01_NN A m p n idx G mv0' Hcl0 (wz a)); [rewrite (unsigned_lit a) by lia; clear -NH; lia|].
        apply (wmono_NNR _ _ a WM0 H1 ltac:(lia)). exact Hv. }
      assert (VIEW : aview_of (pa_hull A') rm5 = mv2').
      { unfold aview_of. subst A'. rewrite (khidc_H2 A p n idx G NTI kb es' more). subst rm5. apply (krm5_view A m p n idx mv0' mv1' mv2'). exact Hcl2. }
      idtac "K-SEC VIEW ok".
      (* [comment removed for export] *)
      assert (AGC : forall a, 0 <= a < 2^64 ->
                 outside [(dsp - 112, dsp); (0xb2000, 0xb2004); (thr + 2840, thr + 2856); (0xb1dd0, 0xb1dd9); (0xb1de8, 0xb1df8);
                          (0xb2018, 0xb2028); (p_pa (a_pl A) + 8 * Z.of_nat idx, p_pa (a_pl A) + 8 * Z.of_nat idx + 8);
                          (cs_map (sec_last A) + 24, cs_map (sec_last A) + 32); (sh (p - 6144), sh (p - 6144) + map_size n / 8); (thr + 2888, thr + 2904)] a ->
                 ~ (p - 6144 <= a < p - 6144 + map_size n) -> mv2' (wz a) = v (wz a)).
      { intros a Ha OUT NM.
        rewrite (MU2 (wz a)) by (rewrite (unsigned_lit a Ha); cbn [outside] in OUT |- *; split; [| exact I]; intros X; apply (proj1 OUT); clear -X; lia).
        rewrite (HOP12 a Ha NM).
        rewrite (MU1 (wz a)) by (rewrite (unsigned_lit a Ha); cbn [outside] in OUT |- *; (first [ dand11 OUT as O1 _ _ _ _ _ _ _ _ O10 _ | destruct OUT as (O1 & _ & _ & _ & _ & _ & _ & _ & _ & O10 & _) ]); split; [exact O1| split; [exact O10| exact I]]).
        rewrite (HOP01 a Ha) by (cbn [outside] in OUT; (first [ dand10 OUT as _ _ _ _ _ _ _ _ O9 _ | destruct OUT as (_ & _ & _ & _ & _ & _ & _ & _ & O9 & _) ]); intros X; apply O9; clear -X G1 G6; lia).
        apply MU0. rewrite (unsigned_lit a Ha). exact OUT. }
      idtac "K-SEC AGC ok".
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      pose proof (conj H5 (conj HHI CE)) as KI12. pose proof (conj CEIL (conj LOW CE)) as KI2.
      pose proof (conj SEP_hp (conj NCH IR)) as KA12. pose proof (conj CEIL (conj LOW (conj CE (conj PA' (conj NCH PALE))))) as KA2.
      pose proof (conj CEIL (conj LOW (conj CE HL'))) as KH2.
      assert (PNSRT : rw_cells rsegs mv2' 0xb1dd0 [C8 (wz (Z.of_nat (length (sr_chunks (a_sec A))) - 1)); C1 (Z_to_bv 8 0)]).
      { rewrite <- NCH. eapply rw_cells_mu; [eapply rw_cells_mu; [exact Q_nsrt| exact MU12| sdtF KI12]| exact MU2| sdtF KI2]. }
      assert (PLCK : rw_cells rsegs mv2' 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)])
        by (eapply rw_cells_mu; [eapply rw_cells_mu; [exact Q_lck| exact MU12| sdtF KI12]| exact MU2| sdtF KI2]).
      assert (PARR : u64arr rsegs mv2' (p_pa (a_pl A)) (upd (sec_words A) idx (wz (cs_map (sec_last A))))).
      { rewrite Nat2Z.id in Q_arr. eapply u64arr_mu; [eapply u64arr_mu; [exact Q_arr| exact MU12| sdtF KA12]| exact MU2| sdtF KA2]. }
      assert (PHLC : cs_map (sec_last A) = p - 6144 \/ rw_cells rsegs mv2' (cs_map (sec_last A)) [C8 (wz (cs_map (sec_last A))); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat idx))]).
      { destruct HLA as [E|AP]; [left; exact E|]. destruct Q_hlc as [E|C]; [left; exact E| right].
        eapply rw_cells_mu; [eapply rw_cells_mu; [exact C| exact MU12| sdtF AP]| exact MU2| sdtF KH2]. }
      idtac "K-SEC post cells ok".
      (* [comment removed for export] *)
      assert (PDR : depot_repL AL_pasan rsegs (a_depot A) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) mv2').
      { apply (depot_repL_agree AL_pasan rsegs (a_depot A) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) v mv2' (ar_depot _ _ _ _ _ RAR)).
        intros a Fa. unfold depot_foot in Fa. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Fa. unfold kDepotNodesL1 in Fa.
        assert (Ha : 0 <= a < 2^64) by (clear -Fa N0' F0' CE; kung_all; lia).
        destruct Fa as [Fa|[Fa|Fa]]; (apply (AGC a Ha); [cbn [outside]; splits|]);
          first [ exact I
                | clear -Fa CEIL LOW CE N0' F0'; kung_all; lia
                | clear -Fa T' SEP_n0t SEP_f0t; unfold apart, AMallocA.apart in *; kung_all; lia
                | clear -Fa PA' IR PALE SEP_An SEP_Af; unfold apart, AMallocA.apart in *; kung_all; lia
                | clear -Fa HL' SEP_ln SEP_lf; unfold apart, AMallocA.apart in *; kung_all; lia
                | clear -Fa N0' F0' SHR; kung_all; lia
                | clear -Fa H5 SEP_hn SEP_hf; unfold apart, AMallocA.apart in *; kung_all; lia ]. }
      assert (IAW : forall a, 0xb65c0 <= a < 0x144e4c -> mv2' (wz a) = v (wz a)).
      { intros a Ha. apply (AGC a ltac:(clear -Ha; lia)); [cbn [outside]|]; clear -Ha CEIL LOW CE T' PA' HL' H5 SHR IR; splits; try exact I; kung_all; lia. }
      assert (IAH : forall a, iafoot a -> mv2' (wz a) = v (wz a)).
      { intros a Ha. apply IAW. unfold iafoot in Ha. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in Ha. clear -Ha. lia. }
      assert (IAL : u8_at rsegs mv2' (al_internal_alloc_inited AL_pasan + 1) 0).
      { pose proof (ar_locks _ _ _ _ _ RAR) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
        change (al_internal_alloc_inited AL_pasan + 1) with 0x144e49 in LK |- *. rewrite lockb_nil in LK.
        eapply (bytes_at_agree_gen _ _ _ _ _ LK). intros k Hk. cbn in Hk. apply IAW. lia. }
      assert (IAP : bytes_at rsegs mv2' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0]).
      { pose proof (consts_cell v 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ RAR)) eq_refl) as PD.
        eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros k Hk. cbn in Hk. apply IAW. lia. }
      assert (HNONE : forall a, p - 6144 <= a < p - 6144 + map_size n -> mv2' (wz a) = None).
      { intros a Ha. rewrite (MU2 (wz a)); [exact (kmv2_none_map A m p n idx G mv0' mv1' a Ha)|].
        rewrite unsigned_lit by (clear -Ha H5 HHI CE; lia). cbn [outside]. split; [clear -Ha HHI CEIL LOW; lia| exact I]. }
      assert (SM' : mapped v lo (dsp - lo)).
      { intros k Hk. (first [ dand3 ST as _ _ STx | destruct ST as (_ & _ & STx) ]). destruct (STx (lo + k) ltac:(lia)) as [Wv _]. unfold wview, wa in Wv.
        rewrite unsigned_lit in Wv by (clear -Hk CEIL LOW CE SPR; lia). rewrite (pa_find_segment_none (lo + k) 1) in Wv by (clear -Hk CEIL LOW CE SPR; lia).
        destruct (v (wz (lo + k))); [discriminate| exact Wv]. }
      idtac "K-SEC finale facts ok".
      (* [comment removed for export] *)
      assert (HID1 : forall z, in_shadow_maps z -> ~ (sh (p - 6144) <= z < sh (p - 6144) + map_size n / 8) -> rm5 (wz z) = m (wz z)).
      { intros z Z1 Z2. assert (Zr : 0 <= z < 2^64) by (unfold in_shadow_maps in Z1; clear -Z1; kung_all; lia).
        assert (NZ : ~ (p - 6144 <= z < p - 6144 + map_size n)) by (unfold in_shadow_maps in Z1; clear -Z1 HM'; kung_all; lia).
        destruct (in_hullb (H2 A p n idx) z) eqn:V2.
        - subst rm5. rewrite (krm5_vis A m p n idx mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), V2; reflexivity).
          rewrite (AG2' z Zr) by (unfold in_shadow_maps in Z1; clear -Z1 Z2 CEIL LOW CE T' N0' F0' PA' HL' HM' IR; kung_all; nexc).
          unfold v, aview_of, mrestrict. rewrite HD0. unfold hidc. rewrite (unsigned_lit z Zr), <- (kvis_same A p n idx G z Z2 NZ), V2. reflexivity.
        - subst rm5. apply (krm5_hid A m p n idx G mv0' mv1' mv2' z Zr); [| exact NZ].
          rewrite <- (kvis_same A p n idx G z Z2 NZ). exact V2. }
      idtac "K-SEC HID1 ok".
      assert (HID2 : forall z, sh (p - 6144) <= z < sh (p - 6144) + map_size n / 8 -> rm5 (wz z) = Some (Z_to_bv 8 0)).
      { intros z Hz. assert (Zr : 0 <= z < 2^64) by (clear -Hz SHR; kung_all; lia).
        destruct (decide (a8_pbeg (p - 6144) <= z < a8_pend (p - 6144) (map_size n))) as [MID|EDGE].
        - destruct (in_hullb (H2 A p n idx) z) eqn:V2.
          + subst rm5. rewrite (krm5_vis A m p n idx mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), V2; reflexivity).
            rewrite (MU2 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| exact I]).
            rewrite (HOP12 z Zr) by (clear -Hz SHR HM'; kung_all; lia).
            rewrite (MU1 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| split; [clear -Hz SHR T'; kung_all; lia| exact I]]).
            apply (kmv1_mid A m p n idx G mv0' z MID). unfold hidc. rewrite (unsigned_lit z Zr), (kvis_H2_H1 A p n idx z V2). reflexivity.
          + subst rm5. exact (krm5_mid A m p n idx G mv0' mv1' mv2' z MID V2).
        - subst rm5. rewrite (krm5_vis A m p n idx mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), (kvis_edges A p n idx z ltac:(clear -Hz EDGE G1 G6; lia)); reflexivity).
          rewrite (MU2 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| exact I]).
          rewrite (HOP12 z Zr) by (clear -Hz SHR HM'; kung_all; lia).
          rewrite (MU1 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| split; [clear -Hz SHR T'; kung_all; lia| exact I]]).
          rewrite (HOP01 z Zr) by exact EDGE.
          assert (SH5 : 0x60a000 <= sh (p - 6144)) by (clear -SHR; lia).
          replace z with (sh (p - 6144) + (z - sh (p - 6144))) by lia. apply (kbytes_zero_raw mv0' (sh (p - 6144)) _ P_sh SH5).
          rewrite Z2Nat.id by (apply Z.div_pos; [clear -MSZ; lia| lia]). clear -Hz. lia. }
      idtac "K-SEC HID ok".
      (* [comment removed for export] *)
      assert (AGstk : forall a, dsp <= a < 2^47 -> mv2' (wz a) = v (wz a)).
      { intros a Ha. apply (AGC a ltac:(clear -Ha CE CEIL LOW; lia)); [cbn [outside]; splits|];
          first [ exact I
                | clear -Ha CEIL LOW CE; kung_all; lia
                | clear -Ha CEIL LOW CE T'; kung_all; lia
                | clear -Ha CEIL LOW CE PA' IR PALE; kung_all; lia
                | clear -Ha CEIL LOW CE HL'; kung_all; lia
                | clear -Ha CEIL LOW CE SHR; kung_all; lia
                | clear -Ha CEIL LOW CE HHI; kung_all; lia ]. }
      assert (PF' : put_frame (p_thr (a_pl A)) mv2').
      { unfold put_frameG in *. eapply rw_cells_agp; [exact PF|]. intros k Hk. cbn [cells_size csize Nat.add length] in Hk. apply AGstk. clear -Hk LOW SPHI HI47. lia. }
      assert (RF' : rec_frame (p_thr (a_pl A)) mv2').
      { unfold rec_frameG in *. eapply rw_cells_agp; [exact RF|]. intros k Hk. cbn [cells_size csize Nat.add length] in Hk. apply AGstk. clear -Hk LOW SPHI HI47. lia. }
      assert (RTMP' : tmp_hdr (a_sb A) mv2' T more).
      { unfold tmp_hdr in *. eapply rw_cells_agp; [exact RTMP|]. intros k Hk. cbn [cells_size csize Nat.add length] in Hk. apply AGstk. clear -Hk LOW SPHI HI47. lia. }
      assert (SMu : mapped v lo (uspd - lo)).
      { intros q Hq.
        destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
        { exact (stk_mapped_pa v lo dsp lo (dsp - lo) ST CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
        destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
        { pose proof (rw_mapped_hi v _ _ DF ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
          specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
        destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
        { unfold tmp_hdr in RTMP. pose proof (rw_mapped_hi v _ _ RTMP ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
        destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
        { unfold rec_frameG in RF. pose proof (rw_mapped_hi v _ _ RF ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
        unfold put_frameG in PF. pose proof (rw_mapped_hi v _ _ PF ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
      idtac "K-SEC frames ok".
      (* [comment removed for export] *)
      (first [ pose proof ((kdead2_ok p n G)) as dR_35; dand3 dR_35 as DEADF DEADL DEADB | pose proof (kdead2_ok p n G) as (DEADF & DEADL & DEADB) ]).
      assert (W' : WFR A') by exact (WFR_sec A kb n (CS (p - 6144) n) idx es' more (dead2 p n) W L0 NTI DEADF DEADL DEADB).
      assert (MD4 : md4 = munmap_modelL (wz (p - 6144)) (wz (map_size n)) md3) by reflexivity.
      assert (HI3x : exists Hx HLx Ex, MInv Hx HLx Ex md3) by (exists (H1 A p n idx), (L1 A p n idx), (pa_eager A); exact HI3).
      pose proof (same_but_materialized_frame _ _ SB5) as FRM5.
      assert (NEL : forall e', In e' (es' ++ q_entries more) -> qe_chunk e' <> ChS (CS (p - 6144) n)).
      { intros e' He' E. apply (rsec_quar_other A kb n (CS (p - 6144) n) es' more W L0). rewrite <- E, quarantined_chunks_def, q_entries_nil. cbn [app].
        apply in_map. rewrite AState.q_entries_app. apply in_or_app. right. rewrite q_entries_cons. cbn [ba_entries]. exact He'. }
      assert (INlim : forall e', In e' (es' ++ q_entries more) -> In e' (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)))).
      { intros e' He'. apply (AFreeRP.limbo_in A kb _ more W L0). cbn [app]. right. exact He'. }
      assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' (es' ++ q_entries more)).
      { intros b' e' Hb' He'. apply in_or_app. right. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
      assert (INhead : forall j e', (S i <= j)%nat -> nth_error (ba_entries b0) j = Some e' -> In e' (es' ++ q_entries more)).
      { intros j e' Hj He'. apply in_or_app. left. subst es'. apply (nth_error_In _ (j - S i)). rewrite nth_error_skipn. replace (S i + (j - S i))%nat with j by (clear -Hj; lia). exact He'. }
      assert (RC' : rcells A' mv2' T (Some (b0, S i)) more).
      { constructor.
        - exact (krecs_arepr A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN PNSRT PLCK PARR PHLC PDR IAH IAL IAP).
        - exact RTMP'.
        - apply (ktmp_chain_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' more); [intros b' Hb'; exact (AFreeRP.more_in A kb _ more W L0 b' Hb')| exact RCH].
        - intros b' e' Hb' He'. apply (klentry_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN PARR PHLC e');
            [exact (INlim e' (INmore b' e' Hb' He'))| exact (NEL e' (INmore b' e' Hb' He'))| exact (RME b' e' Hb' He')].
        - intros b' Hb'. destruct (RMO b' Hb') as [LB SHBb]. pose proof (AFreeRP.more_in A kb _ more W L0 b' Hb') as Hb2.
          destruct (klbatch_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                      (batch_carved A v [] AR b' Hb2) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
          split; [exact LB'| exact (SHB' SHBb)].
        - split; [|split].
          + intros j e' Hj He'. apply (klentry_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN PARR PHLC e');
              [exact (INlim e' (INhead j e' Hj He'))| exact (NEL e' (INhead j e' Hj He'))| exact (RENT j e' ltac:(clear -Hj; lia) He')].
          + assert (LBi : lbatch_cells sb v (chunk_addr sb kQuarantineBatchClass kb) (ba_entries b0) (S i) (batch_bytes b0)).
            { (first [ dand3 RBAT as X1 X2 X3 | destruct RBAT as (X1 & X2 & X3) ]). split; [| exact (conj X2 X3)]. intros i0 e' Hi0 He'. apply (X1 i0 e'); [clear -Hi0; lia| exact He']. }
            exact (proj1 (klbatch_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN kb (ba_entries b0) (S i) (batch_bytes b0) CVb LEN LBi)).
          + exact (proj2 (klbatch_xfer A m p n kb es' more idx mv2' lo dsp AR W L0 NTI CEIL AG2' NN kb (ba_entries b0) i (batch_bytes b0) CVb LEN RBAT) RBSH). }
      idtac "K-SEC rcells ok".
      assert (RI' : RINV A' rm5 md5 T (Some (b0, S i)) more).
      { constructor.
        - exact W'.
        - reflexivity.
        - rewrite VIEW. exact RC'.
        - subst A'. cbn [recsA a_pl a_reg a_sec]. exact (krecs_hidden A m p n idx rm5 W HID NTI HID1 HID2).
        - exact EXTRA.
        - subst A'. cbn [recsA a_pl a_sec]. eapply (kfsm_ledger A m md p n kb es' more idx); eassumption.
        - subst A'. rewrite (krecs_eager A kb idx es' more (dead2 p n) _ NTI). cbn [cs_n].
          apply (MInv_perm _ _ _ _ _ _ (khull_permF A p n idx G NTI kb es' more) (klhull_permF A p n idx G NTI kb es' more)). exact HI5.
        - (first [ dand18 FRM5 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HH4.
        - subst A'. cbn [recsA a_pl a_sec]. eapply (kfsm_cover A m md p n kb es' more idx); eassumption.
        - exact (proj1 (kfsm_ceil md p n CEI md1 md2 md3 md4 md5 SB1 MD2 SB3 MD4 SB5)). }
      idtac "K-SEC RINV ok".
      (* [comment removed for export] *)
      assert (AG2u : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n idx lo uspd a -> mv2' (wz a) = v (wz a)).
      { intros a Ha NE. apply (AG2' a Ha). intros X. apply NE. unfold AFreeX3.EXC in X |- *. destruct X as [X|X]; [left; clear -X; lia| right; exact X]. }
      pose proof (krecs_rstep A m p n kb es' more idx mv2' lo uspd AR W L0 NTI CEIL AG2u NN PARR PHLC HNONE SMu ltac:(clear -SPHI HI47; lia)) as RS.
      fold A' in RS.
      pose proof (RHIST_step A0 v0 md0 p0 n00 uspd lo hi A v md A' mv2' md5 HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl   (* [comment removed for export] *)
                    (fun c0 NE V0 => V0)
                    ltac:(eapply (kfsm_frame md p n); eassumption) RS) as HIST'.
      idtac "K-SEC HIST ok".
      (* [comment removed for export] *)
      assert (CU' : CUR A' rm5 md5 (Some (b0, S i)) more scr).
      { constructor; rewrite ?VIEW.
        - exact RI'.
        - exact HIST'.
        - exact MIv2'.
        - exact STv2'.
        - exact PF'.
        - exact RF'.
        - exact DF'.
        - split; [exact LEN| clear -IL; lia].
        - unfold A', recsA. cbn [a_qlimbo]. rewrite L0 in QB. rewrite !q_bytes_cons, !batch_bytes_ebytes in QB |- *. cbn [ba_entries] in QB |- *. rewrite ebytes_cons in QB.
          pose proof (user_size_pos n ltac:(clear -NR; unfold kMaxPrimaryUser in NR; lia)) as (U1' & _). unfold qe_bytes in QB at 1. cbn [qe_n] in QB. clear -QB U1'. lia. }
      idtac "K-SEC CUR ok".
      destruct CASE as [[LT ->]|[EQ ->]].
      + specialize (KM A' rm5 md5 za0 za1 za2 za3 za4 za5 za6 za7 zt0 zt1 zt2 zt3 zt4 zt5 zt6 ltac:(unfold cnt in LT; clear -LT; lia) CU' eq_refl).
        unfold it_cfgG in KM. rewrite Nat2Z.inj_succ in KM. exact KM.
      + specialize (KD A' rm5 md5 za0 za1 za2 za3 za4 za5 za6 za7 zt0 zt1 zt2 zt3 zt4 zt5 zt6 ltac:(unfold cnt in EQ; clear -EQ; lia) CU' eq_refl).
        unfold it_cfgG in KD. rewrite Nat2Z.inj_succ in KD. exact KD.
  Qed.
End RIter.
