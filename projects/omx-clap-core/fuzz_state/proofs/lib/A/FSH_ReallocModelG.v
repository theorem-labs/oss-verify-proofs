(* fs ASan realloc MODEL EXTENSION (a Theorem Labs lane). STATEMENTS ONLY: definitions, no proofs.

   SPLIT 2026-10-29 (a Theorem Labs lane, for owner a Theorem Labs lane), for the closure rule (a lib/B file may not Require a lib/A file
   that holds a per-image address Definition): this file is the image-free part of the former lib/A/FSH_ReallocModel.v.
   Every Definition below moved verbatim, under the same name. It names no image address (ASTACK is Reusable/YG0d.v's
   stack size, the same for both images). The per-image entries are lib/A/FSH_ReallocModel.v (FS_AREALLOC_PC_A /
   FS_AREALLOC_IPC_A / FS_AREALLOC_A) and lib/B/FSH_ReallocModel.v (FS_AREALLOC_PC_B / FS_AREALLOC_IPC_B /
   FS_AREALLOC_B). Each of them does `Require Export` of this file.

   Why a new file: the donor cgif_file has no ASan realloc at all (a Theorem Labs lane premise-check section 0: asyms,
   model ops YG00.v:410/539, contracts YG0d.v:253-276 all lack it). The source is cgif_rgb_fuzzer's released
   realloc set. Its model lives in cgif_rgb lib/YG0f.v, whose NAME clashes with fs's own Reusable/YG0f.v
   (cgif_file's, no realloc), so the realloc-specific part is relocated here instead of overwriting it
   (a Theorem Labs lane's "second instance beside the model" ruling, via a Theorem Labs lane 20:19Z).

   port-from: proofs/cgif/cgif_rgb_fuzzer/lib/YG0f.v @ c8557374ad2e -- astage, realloc_tree, realloc_s1,
   realloc_mpost, realloc_fpost, aregime3, realloc_leaf (:28-34, :106-111, :221-230 and the astage / leaf
   definitions above them). Module path and the renames below are the only changes.

   RENAMES (declared, because the fs tree already uses these names for the PLAIN allocator):
   - cgif_rgb `realloc_leaf`  -> `arealloc_leaf`.  fs's Reusable/YO0d.v:443 already defines a PLAIN
     `realloc_leaf` over (L : layout) / `mreal`; this one is the ASan leaf over (ly : alayout) / `amreal`.
     Different signature, same name, so the ASan one is renamed to keep both unambiguous.
   - the trace universe is a PARAMETER `U` here, where cgif_rgb writes `as_universe B`. fs's universe is
     A/ACej.v `Tfib_universe`, whose numerals are still cgif_file's until the RELOC lane re-points them, so
     this file names no trace numeral.

   Everything this file rests on already exists in fs's tree, unchanged (measured, c8557374ad2e):
     Reusable/YG00.v  malloc :410, free :539, bind/ret/tick/set_nev/set_internal_inited, sptr/PNull :75-79,
                      req_size, EV_MAX :37, MALLOC_MAX :38
     Reusable/YG01.v  malloc_post, free_post, BigInv, qtight, Wf, mgrow, fgrow, blocks, blocks_bytes,
                      universe_ok, atok, aregime
     Reusable/YG0l.v  bud_ok, wcost, hcost
     Reusable/YG0d.v  acall_pre, call_trace, amreal, cfg_at, aregs_preserved, ASTACK, ascratch, same_io, spZ, raZ
     Reusable/YG0n.v  AR, aowned, apresent          Reusable/YA0n.v  wle          Reusable/YG0f.v  layout_le, sptr_addr
   So the model extension is ONE new file; only the WALK that discharges it (cgif_rgb YF78.v and its family)
   is a larger port.

   The bound: cgif_rgb's own arealloc_realizes (YG0f.v:221-230) asks 64513 <= n, which is specific to cgif_rgb's
   image. fs reallocs at the pj_write buffer growth sizes (4112 / 8208 / 16400 / 32784), so this file states the
   PRIMARY-SIZE form 1 <= n < MALLOC_MAX, which is a Theorem Labs lane's shared `arealloc_realizes_all` (a Theorem Labs lane proves
   it; reply / preset / state consume it). fuzz_realloc never asks for 0 (it always asks HEAD + n = 16 + n) and
   never passes p = NULL to realloc (that path goes to fuzz_malloc), so neither case is stated. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YM05 YA0n YG00 YG01 YG0l YG0d YG0f YG0n.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* ---- the model: realloc as the donor's own ops ---- *)

(* cgif_rgb YG0f.v:28-33. free PNull is the no-op that only ticks; then malloc n; on success free the old block.
   So realloc adds 2 counted events (the malloc and the real free); the free of PNull only moves st_nev. *)
Definition realloc_tree (p : sptr) (n : Z) (tr : list Z) : M sptr :=
  YG00.bind (free PNull tr) (fun _ =>
  YG00.bind (malloc n tr) (fun q =>
  match q with
  | PNull => YG00.ret PNull
  | _ => YG00.bind (free p tr) (fun _ => YG00.ret q)
  end)).

(* cgif_rgb YG0f.v:34: the state after the no-op free PNull *)
Definition realloc_s1 (s : astate) : astate := set_internal_inited true (set_nev (st_nev s + 1) s).

(* cgif_rgb YG0f.v:35-40 (its proof is a cbn + destruct on st_internal_inited; ported with the walk) *)
Definition free_null_eq_stmt : Prop :=
  forall tr s, free PNull tr s = IRet (tt, realloc_s1 s).

(* ---- the room regime for a 2-event call (cgif_rgb YG0f.v:110-111) ---- *)
Definition aregime3 (s : astate) (n : Z) : Prop :=
  st_nev s + 2 < EV_MAX \/ (BigInv s /\ qtight s /\ bud_ok s 3 1 (wcost n) (hcost n)).

(* ---- the two half-posts (cgif_rgb YG0f.v:106-109 and its realloc_fpost) ---- *)
Definition realloc_mpost (U : list (list Z)) (s : astate) (n : Z) (ns : bool) (r : sptr * astate) : Prop :=
  malloc_post U (realloc_s1 s) n ns r /\ st_internal_inited (snd r) = true /\
  (BigInv s -> BigInv (snd r) /\ mgrow (realloc_s1 s) n (snd r)).

Definition realloc_fpost (U : list (list Z)) (s2 : astate) (p : sptr) (n_old : Z) (ns : bool)
  (r : unit * astate) : Prop :=
  free_post U s2 p n_old ns r /\ (BigInv s2 -> BigInv (snd r) /\ fgrow s2 (snd r)).

(* ---- one stage of the machine run (cgif_rgb YG0f.v astage): what a sub-run may touch ---- *)
Definition astage (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) : Prop :=
  AR segs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ ascratch B stk regs a -> ~ E a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W') mem' a).

(* ---- the ASan leaf: where the run lands and what it did (cgif_rgb YG0f.v realloc_leaf, RENAMED) ----
   PNull arm kept for faithfulness to the donor; it is DEAD for fs under the granted-allocation rule, which is a
   lemma the walk proves (fuzz_realloc always asks 16 + n >= 16, and a NULL p goes to fuzz_malloc), not a citation. *)
Definition arealloc_leaf (U : list (list Z)) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z)
  (r : sptr * astate) (W' : world segs) (c' : config) : Prop :=
  exists ly' regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
  getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\ qtight (snd r) /\
  match fst r with
  | PNull => astage ASTACK ly S W regs mem md (fun _ => False) ly' (snd r) W' mem' md' /\
             (exists ns, realloc_mpost U S n ns r)
  | q => exists ly2 S2 W2 mem2 md2,
         astage ASTACK ly S W regs mem md
           (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 mem2 md2 /\
         (exists ns, realloc_mpost U S n ns (q, S2)) /\ qtight S2 /\
         (forall i, 0 <= i < Z.min n_old n ->
            aview segs (w_H W2) mem2 (sptr_addr B ly2 q + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
         astage ASTACK ly2 S2 W2 regs mem2 md2
           (fun a => sptr_addr B ly p <= a < sptr_addr B ly p + req_size n_old) ly' (snd r) W' mem' md' /\
         (exists ns, realloc_fpost U S2 p n_old ns (tt, snd r))
  end.

(* ---- the contract: the binary's realloc interceptor realizes the model ----
   cgif_rgb YG0f.v:221-230, at the PRIMARY-SIZE bound (a Theorem Labs lane's arealloc_realizes_all) instead of 64513 <= n. *)
Definition arealloc_realizes_all (U : list (list Z)) (pc pc0 : Z) : Prop :=
  forall ly S W regs mem md p n_old n ch,
  acall_pre segs B ly S W regs mem md ch -> aregime3 S n ->
  In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) -> getr regs 11 = w64 n ->
  1 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX ->
  In (call_trace ly pc0 regs ch) U ->
  amreal segs (realloc_tree p n (call_trace ly pc0 regs ch) S) W
    (cfg_at segs pc regs mem md)
    (arealloc_leaf U ly S W regs mem md p n_old n).

End e.
