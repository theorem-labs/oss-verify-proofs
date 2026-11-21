(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit U2ABlob ItAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BCall U2BGlue U2BIface ItB_pro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import StrFun RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

From Stdlib Require Import FunctionalExtensionality.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma byte_of_c1 : forall m s b, rw_cells bsegs m s [C1 b] -> 0x67f000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image bsegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.
Lemma mem_eq_single : forall (mp m' : amem) A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> m' = write_to_mem mp (wa A) [b].
Proof.
  intros mp m' A b HA HB MU Hb. apply functional_extensionality. intros x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Definition bx (P : Prop) : Prop := P.

Section S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (lo SPA : Z) (RNG : footprint).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOS : lo <= SP - 288.
  Hypothesis LOC : ATOP + 4096 <= lo.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SPT : SP + 16 < KEND.
  Hypothesis ESPA : SPA = (SP - 256) - (SP - 256) mod 32.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RI : rng_aimg RNG.
  Variables (F FLG : Z).
  Hypothesis F256 : F mod 256 = 0.
  Hypothesis FB : ablk F (F + 256).
  Hypothesis FTOP : F + 256 <= ATOP.
  Hypothesis GB : ablk FLG (FLG + 1).
  Hypothesis GTOP : FLG + 1 <= ATOP.
  Hypothesis GF : FLG + 1 <= F \/ F + 256 <= FLG.
  Hypothesis RF : rng RNG F 256.
  Hypothesis RSF : rng RNG (shad F) 32.
  Hypothesis RG : rng RNG FLG 1.

  Notation SHF := (Z.shiftr F 3 + 2147450880).

  Lemma it_epi : forall (r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word) m
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (h0 h1 h2 : word) (jb8 : list byte),
    stk bsegs m lo SPA -> stk bsegs m (SPA + 152) (SP + -104) -> mem_inv bsegs m ->
    rw_cells bsegs m SPA [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 v96; C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144] ->
    rw_cells bsegs m (SP + -104) (it_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells bsegs m F [C8 h0; C8 h1; C8 h2; CB 8 jb8] ->
    rw_cells bsegs m (F + 248) [C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m FLG [C1 (Z_to_bv 8 1)] ->
    rw_cells bsegs m SHF it_shcells ->
    evtF bsegs RNG (fun ms' => exists (mp m' : amem) (q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word),
        ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 (Z_to_bv 64 r) q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
                 FR (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ munch [(SHF, SHF + 32); (F, F + 8)] m mp /\ wmono bsegs m mp /\ mem_inv bsegs mp
        /\ munch [(FLG, FLG + 1)] mp m' /\ wmono bsegs mp m' /\ mem_inv bsegs m'
        /\ stk bsegs m' lo SP /\ rw_cells bsegs m' FLG [C1 (Z_to_bv 8 0)])
      (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 F) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 SHF) (Z_to_bv 64 F) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x97768) fc None m (seg_rom bsegs)).
  Proof using All.
    intros until jb8. intros STL STG MI FRA FRB FH FFL FLC FSH.
    unfold it_SAVED, it_shcells, c1z in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND in SPT.
    atop_facts. pose proof (ablk_lin _ _ FB) as (FB1 & FB2 & FB3 & FB4). unfold AIMG_HI in FB1.
    pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
    assert (SPAB : SP - 272 <= SPA <= SP - 256 /\ SPA mod 32 = 0) by (rewrite ESPA; Z.div_mod_to_equations; lia).
    assert (LO0 : 0 <= lo) by (destruct STL as [? _]; assumption).
    assert (F8 : F mod 8 = 0) by (Z.div_mod_to_equations; lia).
    rewrite shadE in RSF.
    assert (BSF : 2147450880 <= SHF /\ SHF + 32 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    assert (DSF : SHF + 32 <= F \/ F + 256 <= SHF)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ablk, AIMG_HI, KLS in FB; Z.div_mod_to_equations; lia).
    assert (DSG : SHF + 32 <= FLG \/ FLG + 1 <= SHF)
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; unfold ablk, AIMG_HI, KLS in FB, GB; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(SHF, SHF + 32); (F, F + 8)] m) as MU1. pose proof (wmono_refl bsegs m) as WM1.
    zrunb [0x97820].
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv bsegs mx |- _ => pose proof MIx as MIp; change (mem_inv bsegs mx) with (bx (mem_inv bsegs mx)) in MIp end end.
    lazymatch type of MU1 with ?T => change T with (bx T) in MU1 end.
    lazymatch type of WM1 with ?T => change T with (bx T) in WM1 end.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(FLG, FLG + 1)] mx) as MU2; pose proof (wmono_refl bsegs mx) as WM2 end.
    zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    zs. zs. (* [comment removed for export] *)
    do 13 zs. zs. zs.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells bsegs _ SPA _ |- _ => rename H into FRA2 end.
    lazymatch goal with H : rw_cells bsegs _ (SP + -104) _ |- _ => rename H into FRB2 end.
    lazymatch goal with H : stk bsegs _ lo SPA |- _ => rename H into STL2 end.
    lazymatch goal with H : stk bsegs _ (SPA + 152) (SP + -104) |- _ => rename H into STG2 end.
    eapply stk_release in FRA2; [| exact STL2| lia]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRA2.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (stk_merge bsegs mx lo (SPA + 152) (SP + -104) FRA2 STG2 ltac:(lia)) as ST2 end.
    release_frame FRB2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold bx in MU1, WM1, MIp.
    replace (Z.shiftr F 3 + 2147450912) with (SHF + 32) by lia.
    eexists _, _. do 14 eexists. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MIp|].
    split; [exact MU2|]. split; [exact WM2|]. split; [eassumption|]. split; [exact ST2| eassumption].
  Qed.
End S.
End CANSEC1.
