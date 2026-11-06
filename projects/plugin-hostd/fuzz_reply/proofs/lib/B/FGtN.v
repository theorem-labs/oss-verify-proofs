(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/FGtN.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, CacheDealloc walk (H3 DMcd* + FG*N, a Theorem Labs lane's DMcdGWb / DMcdGW); file sha256 0694b37619f8) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 13 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/FGtN.v at commit 9ee489aa7d7, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (13 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30, a Theorem Labs lane (lane B1 slice H3, a Theorem Labs lane's real-merge drain walk; a Theorem Labs lane approval 01:19Z): an ADDITIVE copy of
   FGt.v for tfib_efa_spec_lk (FGtN.v): EnsureFreeArraySpace's walk with the region info's LOCK WORD (RG+0) carried as a literal
   chunk.  The ONLY semantic change against FGt.v is noted at its site; everything else is FGt.v with FGs/FGk/FGw/FGc/FGt renamed to
   their N copies.  Why: ReturnToAllocator re-reads RG+0 after the call (0x34978, the unlock), and the original leaf frames the callee by
   all of RG..RG+128, so the value was lost.  rule 24: proves function __sanitizer::SizeClassAllocator64::EnsureFreeArraySpace
   (re-walk of the released FG* walk with one more invariant chunk); reuse search `proof-index ReturnToAllocator EnsureFreeArraySpace
   0x34928 0x347c4` 2026-10-30T01:1xZ exit 4: no released contract of EnsureFreeArraySpace that keeps RG+0 (the released
   YFgz.segK2 walks ReturnToAllocator's tail only on the no-growth arm). *)
(* The return-path contract: EnsureFreeArraySpace as the callee of ReturnToAllocator, in the form the generic
   Deallocate's drain / recycle path uses for the shared (reply / preset) instance.

   [tfib_efa_spec] (below) is FGcN.efa_call with the walk's helper atoms hidden: the caller supplies only the register
   and memory facts at the jal 0x34924 (the entry registers, the stack window, the image's constant cells, the four
   windows the walk writes, the class's mapped_free_array word), the model fact [rg_mapped_fa (reg S c) = mf] and, on
   the growth arm, the placement and the footprint room.  No allocator relation (cgif's AR, the shared instance's
   ARX) appears, so both instances discharge the premises from their own view.

   How the drain uses it.  DMspec.tfib_drain_spec_cf's tree is drain_body_cf -> recycle_body_cf -> do_recycle ->
   cache_dealloc (0x3428c) -> return_to_allocator (0x347c4, YG00.v:450-455).  ReturnToAllocator calls
   EnsureFreeArraySpace at 0x34924 with a0 = this, a1 = the class's region info, a2 = the region begin and
   a3 = fa_len (rg_free r) + |offs| (the model's [newlen]); the released cache_dealloc walk (YFgz.v segK2) takes only
   the arm in which the call returns at once, because cgif's wfc_fa_room makes 4 * newlen <= rg_mapped_fa r hold.
   The shared instance drops wfc_fa_room (a Theorem Labs lane), so its walk splits at 0x34b10: it cites [tfib_efa_spec] at the
   jal, with [cnt := newlen], and resumes at 0x34928 from [efa_leafT] -- no growth (the released arm, model state
   unchanged), or growth (a0 = 1, mapped_free_array = mf + kFreeArrayMapSize in memory and in the region, the new
   map and its shadow present, the world grown by the two allowances).  The refused answer of the request is not a
   successor: see FGcN.v's header and FGrf.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB19 YF0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0u.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YFl1 YFhy YFis YFkp YFk6 YFk5 YFhz YFk8 YFk9.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import FGsN.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YFkn FGwN FGkN FGcN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section f.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c cnt : Z).
(* N: the values of the caller's cells the walk carries (RG+80, RG+88, the stats word T+2784). *)
Variables (j80 j88 jst : Z).
(* N: the region's free count, allocated and mapped user sizes (cells the caller re-reads). *)
Variables (nf au mu : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let mf : Z := rg_mapped_fa (reg S c).
Let fadr : Z := YFk5.FAv ly c + mf.
Let shf : Z := YFk5.SHBv + fadr / 8.
Let mf2 : Z := mf + kFreeArrayMapSize.

(* The premises at the call (the jal 0x34924 of ReturnToAllocator; pc = 0x34aec, ra = 0x34928). *)
Definition efa_pre_lk : Prop :=
  img_cover ly /\ layout_ok ly /\ TfibSyms B /\ ly_tsd ly = TFIB_TSD /\
  Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) /\
  1 <= c <= 31 /\ 0 <= cnt <= 2 ^ 27 /\
  (0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0) /\
  4 * cnt <= mf + kFreeArrayMapSize /\
  YK0s.ret_ok (getr regs0 1) /\ getr regs0 4 = w64 TFIB_TP /\
  getr regs0 10 = w64 A_ALLOCATOR /\ getr regs0 11 = w64 (YFk5.RGv ly c) /\
  getr regs0 12 = w64 (YFk5.RBv ly c) /\ getr regs0 13 = w64 cnt /\
  (ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) /\
  (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) /\
  (forall a, (YFk5.RGv ly c <= a < YFk5.RGv ly c + 128) \/ (YFk5.Pr ly c <= a < YFk5.Pr ly c + 16) \/
             (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) mem0 a) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 24) 8 mf /\
  (exists jm1 jm2, 0 <= jm1 < 2 ^ 64 /\ 0 <= jm2 < 2 ^ 64 /\
     val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1 /\
     val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2) /\
  (* N: the lock word ReturnToAllocator's acquire leaves at RG+0 (FGsN.LOCKV), and the cells the caller re-reads *)
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c) 8 LOCKV /\
  (0 <= j80 < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 80) 8 j80) /\
  (0 <= j88 < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 88) 8 j88) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.Pr ly c + 0) 4 (max_cached c / 2) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.Pr ly c + 8) 8 (class_size c) /\
  (0 <= jst < 2 ^ 64 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 jst) /\
  (* N: the region record's cells and the class max *)
  (0 <= nf /\ 4 * nf <= mf) /\ (0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 8) 8 0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 16) 8 nf /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 32) 8 au /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 40) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 48) 8 mu /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 56) 8 0 /\
  (* the class's exhausted byte RG+68 (the flag at cf): carried unchanged, whatever its value *)
  (exists j68, 0 <= j68 < 2 ^ 8 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 68) 1 j68) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.Pr ly c + 4) 4 (max_cached c) /\
  (mf < 4 * cnt ->
     mf + kFreeArrayMapSize <= kFreeArrayMax /\
     region_free (vm_reserved (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     map_contains (vm_maps (m_vmmaps md0)) (w64 fadr) (w64 kUserMapSize) = true /\
     amwf md0 /\ YM05.ceil_of_top (alloc_top (m_vmmaps md0)) /\
     eager_used md0 + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md0) /\
     (forall a, YFkn.SHR shf a -> mem0 (w64 a) <> None)).

(* The leaf at ReturnToAllocator's continuation 0x34928. *)
Definition efa_leafT_lk (r : bool * astate) (W' : world tfibsegs) (c' : config) : Prop :=
  (* j68: the entry's byte at RG+68, which the leaf states unchanged *)
  exists j68, val_mem tfibsegs (mrestrict (w_H W) mem0) (YFk5.RGv ly c + 68) 1 j68 /\
  @FGcN.efa_leaf _ W ly regs0 mem0 md0 c (max_cached c) (max_cached c / 2) nf mf au mu (class_size c) j68 j80 j88 jst cnt fadr shf mf2 S r W' c'.

Theorem tfib_efa_spec_lk : forall (k : bool -> M unit) (Q : unit * astate -> world tfibsegs -> config -> Prop),
  efa_pre_lk ->
  (forall r W' c', efa_leafT_lk r W' c' -> amreal tfibsegs (k (fst r) (snd r)) W' c' Q) ->
  amreal tfibsegs (bind (ensure_free_array c cnt true) k S) W (cfg_at tfibsegs A_EFA regs0 mem0 md0) Q.
Proof.
  intros k Q PRE Hk.
  destruct PRE as (IMG & LY & TS & HTSD & Hconst & HcR & Hcnt & Hmf & Hone & Hra & Htp & Ha0 & Ha1 & Ha2 & Ha3 &
                   Hsp & Hpres0R & Hcells & Hmfv & (jm1 & jm2 & Hjm1 & Hjm2 & Hjm1v & Hjm2v) & Hlk & [H80r Hk80] & [H88r Hk88] & Hkp & Hks & [Hstr Hkt] & Hnf0 & Hmu0 & Hk8 & Hk16 & Hk32 & Hk40 & Hk48 & Hk56 & (j68 & Hj68 & Hk68v) & Hkmax & Hgrow).
  assert (Hz32 : 0 <= 0 < 2 ^ 32) by lia.
  assert (Hz64 : 0 <= 0 < 2 ^ 64) by lia.
  assert (Hz32' : 0 <= j68 < 2 ^ 32) by lia.
  exact (@FGcN.efa_call _ _ W ly regs0 mem0 md0 c (max_cached c) (max_cached c / 2) nf mf au mu (class_size c)
    j68 j80 j88 jst jm1 jm2 1 16 fadr shf kUserMapSize 0 0 cnt 0 fadr shf mf2 0 0
    IMG LY HcR eq_refl eq_refl eq_refl Hnf0 Hmf Hmu0
    Hz32' H80r H88r Hstr Hjm1 Hjm2 Hsp Hra Htp Ha0 Ha1 Ha2 Ha3
    eq_refl eq_refl eq_refl Hcnt eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    B TS HTSD Hconst Hpres0R Hcells Hmfv Hjm1v Hjm2v Hlk Hk80 Hk88 Hkp Hks Hkt Hk8 Hk16 Hk32 Hk40 Hk48 Hk56 (conj Hj68 Hk68v) Hkmax S k Q eq_refl Hone Hgrow
    (fun r W' c' L => Hk r W' c' (ex_intro _ j68 (conj Hk68v L)))).
Qed.
End f.
End d.
