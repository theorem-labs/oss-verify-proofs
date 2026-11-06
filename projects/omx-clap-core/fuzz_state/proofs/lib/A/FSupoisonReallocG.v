(* The any-U (user-poison) form of fuzz_state's ASan realloc contract, image-free part (POISON-U lane, a Theorem Labs lane; asked by another Theorem Labs lane,
   21:19Z). It is lib/A/FSH_ReallocModelG.v's `arealloc_realizes_all` (a Theorem Labs lane's file, over cgif_rgb
   YG0f.v:221-230 at the primary-size bound) with the donor's AR / acall_pre read through FSupoison's ARU, every other
   clause verbatim, plus the one premise a free needs: no user-poisoned range lies in the block realloc releases.
   It also states the two premises realloc's inner calls need, which FSH_ReallocModelG's plain text lacks: the C5
   trace margin and the stack margin (see the Definition). So the plain text is no longer a corollary of this one,
   and the former Up = [] corollary (arealloc_realizes_all_of_U, which had no consumer) is removed.

   NAMING: FSH_ReallocModelG's `U : list (list Z)` is the TRACE UNIVERSE (as_universe B). The user-poisoned set is a
   `list (Z * Z)` and is called `Up` here, so the two never collide.

   Why the plain form alone does not serve fs (a Theorem Labs lane's measurement, same shape as this lane's for malloc / free):
   at fs's realloc call site other blocks' heads are still poisoned, so AR's al_shadow (a live block's user granules
   read 0) contradicts FSupoison.upoisoned (those bytes read 247). The plain contract is therefore usable only when the
   poisoned set is exactly the head being replaced; ARU is what holds for every other set.

   SPLIT 2026-10-29 (a Theorem Labs lane; ruled by a Theorem Labs lane, 08:41Z), for the closure rule (no lib/A file may
   Require a lib/B file, and no lib/B file may use an image-A term): this file is the image-free part of the former
   lib/A/FSupoisonRealloc.v. astageU, arealloc_leafU and arealloc_realizesU moved verbatim, under the same names; their
   model names are cited from lib/A/FSH_ReallocModelG.v. It names no image pc. The per-image entries are
   lib/A/FSupoisonRealloc.v (FS_AREALLOC_AU) and lib/B/FSupoisonRealloc.v (FS_AREALLOC_BU); each does `Require Export`
   of this file.
   STATEMENT only; no Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_ReallocModelG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* FSH_ReallocModelG.astage with ARU in place of AR, at the same poisoned set. *)
Definition astageU (stk : Z) (ly : alayout) (S : astate) (Up : list (Z * Z)) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (E : Z -> Prop)
    (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) : Prop :=
  FSP.ARU segs B ly' S' Up W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* FSH_ReallocModelG.arealloc_leaf over astageU; the model posts (realloc_mpost / realloc_fpost) are unchanged. *)
Definition arealloc_leafU (Un : list (list Z)) (Up : list (Z * Z)) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
    (r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
  exists ly' regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
  getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
  match fst r with
  | PNull => astageU ASTACK ly S Up W regs mem md (fun _ => False) ly' (snd r) W' mem' md' /\
             (exists ns, FSH_ReallocModelG.realloc_mpost Un S n ns r)
  | q => exists ly2 S2 W2 mem2 md2,
         astageU ASTACK ly S Up W regs mem md
           (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 mem2 md2 /\
         (exists ns, FSH_ReallocModelG.realloc_mpost Un S n ns (q, S2)) /\ qtight S2 /\
         (forall i, 0 <= i < Z.min n_old n ->
            aview segs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
         astageU ASTACK ly2 S2 Up W2 regs mem2 md2
           (fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) ly' (snd r) W' mem' md' /\
         (exists ns, FSH_ReallocModelG.realloc_fpost Un S2 p n_old ns (tt, snd r))
  end.

(* FSH_ReallocModelG.arealloc_realizes_all for any user-poisoned set.
   The extra premise is the one a free needs (same as FSupoisonU.afree_realizesU's): no poisoned range lies in the
   block realloc releases. At fs's call sites it is discharged, not carried: fuzz_realloc unpoisons its own head
   before the call (A 0x82a98 before `jal __wrap_realloc` 0x82b30; B 0x82c54 before 0x82cec), and the other heads are
   heads of OTHER live blocks (FSupoisonU.fs_heads + ARU_free_outside).
   TRACE PREMISE in the C5 form with realloc's two inner events counted: the call's trace is in the universe OR two
   events remain (`st_nev S + 2 < EV_MAX`), because Allocate runs one event and Deallocate two events after realloc's
   entry, and the callees take fs's standard C5 premise `In .. \/ st_nev _ < EV_MAX` at THEIR states (a Theorem Labs lane's c5 text,
   ReallocG.v:24-26; measured by a Theorem Labs lane: with only `st_nev S < EV_MAX` the callees' premise is false at S1 / S2). A caller
   discharges it from its own budget premise (ALLOC's fsw_aj_reallocU already has `st_nev Sc + 2 < EV_MAX`,
   FSW_realloc.v:511). Its left arm is FSH_ReallocModelG's plain `In .. U` form.
   STACK MARGIN `ly_bot ly + 0x8a0 < spZ regs`: realloc's own four frames (interceptor 0x7f0, the GetCurrentPc / unwind
   frame 0x70, asan_realloc 0x10, Reallocate 0x30 = 0x8a0, identical on A and B; the stack note at
   lib/A/FSH_ReallocModel.v:37-45) lie between its entry sp and the inner Allocate / Deallocate calls, whose contracts
   need `ly_bot ly < sp_callee` (AllocG.v:75,
   DeallocG.v:81); c5's realloc_pre carries the same bound as RSTACK (ReallocG.v:121). acall_preU's `ly_bot ly < spZ regs`
   alone cannot give it (measured by a Theorem Labs lane). A caller discharges it from its own stack window. *)
Definition arealloc_realizesU (Un : list (list Z)) (pc pc0 : Z) : Prop :=
  forall ly S Up W regs mem md p n_old n ch,
  FSU.acall_preU segs B ly S Up W regs mem md ch -> FSH_ReallocModelG.aregime3 S n ->
  In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) -> getr regs 11 = w64 n ->
  1 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
  (forall rg, In rg Up -> fst rg + snd rg <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n_old <= fst rg) ->
  In (call_trace ly pc0 regs ch) Un \/ st_nev S + 2 < EV_MAX ->
  ly_bot ly + 0x8a0 < spZ regs ->
  amreal segs (FSH_ReallocModelG.realloc_tree p n (call_trace ly pc0 regs ch) S) W
    (cfg_at segs pc regs mem md)
    (arealloc_leafU Un Up ly S W regs mem md p n_old n).
End r.
