(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) copy of lib/A/Prog/FSW_pj_set_num.v (a working branch
   e45b7c0a2da, taken there from a working branch 2b1c9c8141f), same lemma names and bodies; imports point
   at lib/B's FSH_Base / FSH_Rt / FSPstat / FSH_Fn_reader (B's rd_ev / rd_live / grow_tr / grow_res); no image value. *)
(* pj_set's event and live-byte accounting (lemma file, rule 24: no function proved; pure arithmetic over fixed
   definitions, no machine state, no walk). Serves FSW_pj_set_holds.v (pj_set_holds against FSH_Fn_reader.pj_set_spec).

   PROVED (all Qed, no Section hypothesis):
     pSn_trace_app        pj_set_c.set_trace n cap klen = grow_tr 6 n cap ++ [EAlloc (Z.to_nat (klen + 1))], with NO
                          side condition: both traces carry the same two EGrow events when n = cap (so the cap = 0
                          case, where rd_ev charges each EGrow 0 _ as EV_fuzz_malloc, needs no case of its own).
     pSn_ev_split         rd_ev of set_trace = rd_ev of grow's trace + EV_fuzz_malloc (its 0 <= cap premise is the
                          caller's interface; the proof does not use it).
     pSn_len_split / pSn_len_le / pSn_held_split (0 <= klen) / pSn_live_split (0 <= klen).
     pSn_held_le_live     PjGrammar.held l <= rd_live l for every l (no premise: EGrow m n gives n - m <= n + HEAD).
     pSn_quiet_mono       quiet cnt fail j -> 0 <= i <= j -> quiet cnt fail i.
     pSn_blocks_bytes_ablocks  blocks_bytes S is the sum of the second components of ablocks B ly S, for ANY ly
                          (YG01.v blocks / blocks_bytes over the allocated chunks, YG0d.v ablocks maps blocks).
     pSn_bb_perm / pSn_bsum_app / pSn_hsum / pSn_bb_eq  (block sums over Permutation, app, rd_hblocks, equal ablocks).
     pSn_bb_after_grow    the EQUATION read from grow_spec's post Permutation (ablocks B ly' S' ++
                          rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew):
                          blocks_bytes S' + bsum (rd_hblocks Dold) = blocks_bytes S + bsum (rd_hblocks Dnew).
     pSn_grow_new / pSn_grow_old_nonneg / pSn_bb_grow_bound / pSn_bb_after_grow_le  from grow_res and 0 <= cap:
                          bsum (rd_hblocks Dnew) = rd_live (grow_tr ty n cap) (any ty), 0 <= bsum (rd_hblocks Dold),
                          the two as one bound for ty = 6, hence blocks_bytes S' <= blocks_bytes S + rd_live (grow_tr ty n cap).
     pSn_strdup_room      fuzz_strdup_spec's room premise at the state after grow (FSH_Fn_alloc.v:170) from
                          pj_set_spec's entry premise blocks_bytes S + rd_live (set_trace n cap klen) <= LIVE_MAX.
   STATED vs MEASURED: every statement is over the S0 definitions (FSH_Fn_reader.v rd_ev / rd_live / rd_hblocks /
   rd_sum / grow_tr / grow_res, pj_set_c.v set_trace, PjGrammar.v held / held_ev / esize, FSH_Gen.v HEAD / quiet /
   EV_*, YG01.v blocks / blocks_bytes, YG0d.v ablocks); nothing here is measured from the binary.
   No CTX premise anywhere (the CTX drop of 05:03Z does not touch this file). Template: none (arithmetic only). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes pj_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the sum of the second components of a block list (rd_sum's body; written out so the statements read as asked) *)
Local Notation bsum l := (fold_right (fun (b : Z * Z) (acc : Z) => snd b + acc) 0 l) (only parsing).

(* ================= the trace (items 1-5) ================= *)
(* pj_set's trace is grow's trace for an object (ty = 6) followed by the key's one allocation (fuzz_strdup) *)
Lemma pSn_trace_app : forall n cap klen,
  pj_set_c.set_trace n cap klen = grow_tr 6 n cap ++ [PjGrammar.EAlloc (Z.to_nat (klen + 1))].
Proof. intros n cap klen. unfold pj_set_c.set_trace, grow_tr. destruct (n =? cap); reflexivity. Qed.

Lemma pSn_rd_ev_app : forall l1 l2, rd_ev (l1 ++ l2) = rd_ev l1 + rd_ev l2.
Proof.
intros l1 l2. unfold rd_ev. induction l1 as [|e l1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia.
Qed.

Lemma pSn_rd_live_app : forall l1 l2, rd_live (l1 ++ l2) = rd_live l1 + rd_live l2.
Proof.
intros l1 l2. unfold rd_live. induction l1 as [|e l1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. lia.
Qed.

Lemma pSn_held_app : forall l1 l2, PjGrammar.held (l1 ++ l2) = PjGrammar.held l1 + PjGrammar.held l2.
Proof.
intros l1 l2. induction l1 as [|e l1 IH]; cbn [app PjGrammar.held]; [lia|]. rewrite IH. lia.
Qed.

Lemma pSn_len_snoc : forall (A : Type) (l : list A) (x : A), length (l ++ [x]) = S (length l).
Proof. intros A l x. induction l as [|y l IH]; cbn [app length]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* item 1: the 0 <= cap premise is not used (both EGrow events are shared verbatim, cap = 0 included); it is kept
   because the caller states it so *)
Lemma pSn_ev_split : forall n cap klen, 0 <= cap ->
  rd_ev (pj_set_c.set_trace n cap klen) = rd_ev (grow_tr 6 n cap) + EV_fuzz_malloc.
Proof.
intros n cap klen _. rewrite pSn_trace_app, pSn_rd_ev_app.
assert (E : rd_ev [PjGrammar.EAlloc (Z.to_nat (klen + 1))] = EV_fuzz_malloc) by reflexivity.
rewrite E. reflexivity.
Qed.

(* item 2 *)
Lemma pSn_len_split : forall n cap klen,
  Z.of_nat (length (pj_set_c.set_trace n cap klen)) = Z.of_nat (length (grow_tr 6 n cap)) + 1.
Proof. intros n cap klen. rewrite pSn_trace_app, pSn_len_snoc. lia. Qed.

Lemma pSn_len_le : forall n cap klen,
  (length (grow_tr 6 n cap) <= length (pj_set_c.set_trace n cap klen))%nat.
Proof. intros n cap klen. rewrite pSn_trace_app, pSn_len_snoc. lia. Qed.

(* item 3: held_ev (EAlloc m) = Z.of_nat m, and Z.of_nat (Z.to_nat (klen + 1)) = klen + 1 needs klen + 1 >= 0 *)
Lemma pSn_held_split : forall n cap klen, 0 <= klen ->
  PjGrammar.held (pj_set_c.set_trace n cap klen) = PjGrammar.held (grow_tr 6 n cap) + (klen + 1).
Proof.
intros n cap klen Hk. rewrite pSn_trace_app, pSn_held_app.
cbn [PjGrammar.held PjGrammar.held_ev]. rewrite Z2Nat.id by lia. lia.
Qed.

(* item 4 *)
Lemma pSn_live_split : forall n cap klen, 0 <= klen ->
  rd_live (pj_set_c.set_trace n cap klen) = rd_live (grow_tr 6 n cap) + (klen + 1 + HEAD).
Proof.
intros n cap klen Hk. rewrite pSn_trace_app, pSn_rd_live_app.
unfold rd_live at 2. cbn [fold_right PjGrammar.esize]. rewrite Z2Nat.id by lia. lia.
Qed.

(* item 5: each event's held_ev is at most its esize + HEAD (EGrow m n: n - m <= n + HEAD as m >= 0; EFree n: -n) *)
Lemma pSn_held_le_live : forall l, PjGrammar.held l <= rd_live l.
Proof.
induction l as [|e l IH]; [cbn; lia|].
cbn [PjGrammar.held]. unfold rd_live in *. cbn [fold_right].
assert (He : PjGrammar.held_ev e <= Z.of_nat (PjGrammar.esize e) + HEAD)
  by (destruct e; cbn [PjGrammar.held_ev PjGrammar.esize]; unfold HEAD; lia).
lia.
Qed.

Lemma pSn_quiet_mono : forall cnt fail i j, quiet cnt fail j -> 0 <= i <= j -> quiet cnt fail i.
Proof. unfold quiet. intros cnt fail i j (H1 & H2 & H3) Hij. split; [exact H1|]. split; lia. Qed.

(* ================= block bytes across grow (item 6) ================= *)
Lemma pSn_bb_perm : forall l l' : list (Z * Z), Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' HP. induction HP; cbn [fold_right]; lia. Qed.

Lemma pSn_bsum_app : forall l1 l2 : list (Z * Z), bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. induction l1 as [|b l1 IH]; cbn [app fold_right]; lia. Qed.

(* the head-extended list's sum: each reader block (a, k) is the ASan block (a - HEAD, k + HEAD) *)
Lemma pSn_hsum : forall D : list (Z * Z), bsum (rd_hblocks D) = rd_sum D + HEAD * Z.of_nat (length D).
Proof.
induction D as [|b D IH]; [reflexivity|].
unfold rd_hblocks, rd_sum in *. cbn [map fold_right fst snd length]. unfold HEAD in *. lia.
Qed.

(* grow's new blocks are exactly the bytes its trace charges; its old blocks sum to >= 0 (any ty, 0 <= cap) *)
Lemma pSn_grow_new : forall ty n cap kids keys k' y' cap' (Dold Dnew U U' : list (Z * Z)),
  grow_res ty n cap kids keys k' y' cap' Dold Dnew U U' -> 0 <= cap ->
  bsum (rd_hblocks Dnew) = rd_live (grow_tr ty n cap).
Proof.
intros ty n cap kids keys k' y' cap' Dold Dnew U U' HG Hc.
destruct HG as [(Hlt & _ & _ & _ & _ & HDn & _) | (Heq & Hc' & _ & _ & _ & _ & _ & HDn & _)].
- subst Dnew. unfold grow_tr. destruct (Z.eqb_spec n cap) as [E|E]; [lia|reflexivity].
- subst Dnew cap' n. unfold grow_tr. rewrite Z.eqb_refl.
  assert (H2 : 0 <= ReaderRes.cap2 cap) by (unfold ReaderRes.cap2; destruct (cap =? 0); lia).
  unfold rd_hblocks, rd_live. destruct (ty =? 6); cbn [map fold_right fst snd PjGrammar.esize]; lia.
Qed.

Lemma pSn_grow_old_nonneg : forall ty n cap kids keys k' y' cap' (Dold Dnew U U' : list (Z * Z)),
  grow_res ty n cap kids keys k' y' cap' Dold Dnew U U' -> 0 <= cap ->
  0 <= bsum (rd_hblocks Dold).
Proof.
intros ty n cap kids keys k' y' cap' Dold Dnew U U' HG Hc.
destruct HG as [(_ & _ & _ & _ & HDo & _) | (_ & _ & HDo & _)].
- subst Dold. cbn. lia.
- subst Dold. unfold rd_hblocks, ReaderRes.kids_blk, ReaderRes.keys_blk.
  destruct (cap =? 0); destruct (ty =? 6); cbn [orb negb app map fold_right fst snd]; unfold HEAD; lia.
Qed.

(* item 6, the bound for pj_set's grow (ty = 6): the new blocks sum to at most grow's trace charge (equal, in fact),
   the old ones to >= 0 (each is (a - HEAD, k + HEAD) with k = 56 * cap or 8 * cap, cap >= 0) *)
Lemma pSn_bb_grow_bound : forall n cap kids keys k' y' cap' (Dold Dnew U Ug : list (Z * Z)),
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug -> 0 <= cap ->
  bsum (rd_hblocks Dnew) <= rd_live (grow_tr 6 n cap) /\ 0 <= bsum (rd_hblocks Dold).
Proof.
intros n cap kids keys k' y' cap' Dold Dnew U Ug HG Hc. split.
- rewrite (pSn_grow_new 6 n cap kids keys k' y' cap' Dold Dnew U Ug HG Hc). lia.
- exact (pSn_grow_old_nonneg 6 n cap kids keys k' y' cap' Dold Dnew U Ug HG Hc).
Qed.

Section N. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* blocks_bytes is the sum of ablocks' second components, whatever the layout: ablocks maps blocks (YG0d.v:428),
   blocks maps the allocated chunks to (ck_user, ck_req) (YG01.v:255), blocks_bytes sums their ck_req (YG01.v:266) *)
Lemma pSn_blocks_bytes_ablocks : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|c l IH]; [reflexivity|].
cbn [List.filter fold_right]. destruct (is_alloc c); cbn [map fold_right fst snd]; rewrite IH; reflexivity.
Qed.

(* a call that changes no block (pj_get) keeps blocks_bytes *)
Lemma pSn_bb_eq : forall ly1 S1 ly S, ablocks B ly1 S1 = ablocks B ly S -> blocks_bytes S1 = blocks_bytes S.
Proof.
intros ly1 S1 ly S HA. rewrite (pSn_blocks_bytes_ablocks ly1 S1), (pSn_blocks_bytes_ablocks ly S), HA.
reflexivity.
Qed.

(* item 6, the equation: grow_spec's post Permutation read through the two sums *)
Lemma pSn_bb_after_grow : forall ly S ly' S' (Dold Dnew : list (Z * Z)),
  Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew) ->
  blocks_bytes S' + bsum (rd_hblocks Dold) = blocks_bytes S + bsum (rd_hblocks Dnew).
Proof.
intros ly S ly' S' Dold Dnew HP. apply pSn_bb_perm in HP. rewrite !pSn_bsum_app in HP.
rewrite (pSn_blocks_bytes_ablocks ly' S'), (pSn_blocks_bytes_ablocks ly S). exact HP.
Qed.

(* ... its <= corollary with grow_res (any ty) *)
Lemma pSn_bb_after_grow_le : forall ly S ly' S' ty n cap kids keys k' y' cap' (Dold Dnew U U' : list (Z * Z)),
  grow_res ty n cap kids keys k' y' cap' Dold Dnew U U' -> 0 <= cap ->
  Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew) ->
  blocks_bytes S' <= blocks_bytes S + rd_live (grow_tr ty n cap).
Proof.
intros ly S ly' S' ty n cap kids keys k' y' cap' Dold Dnew U U' HG Hc HP.
pose proof (pSn_bb_after_grow ly S ly' S' Dold Dnew HP) as HE.
pose proof (pSn_grow_new ty n cap kids keys k' y' cap' Dold Dnew U U' HG Hc) as HN.
pose proof (pSn_grow_old_nonneg ty n cap kids keys k' y' cap' Dold Dnew U U' HG Hc) as HO.
lia.
Qed.

(* ... and fuzz_strdup_spec's room premise (FSH_Fn_alloc.v:170, cs = the key, klen = Z.of_nat (length cs)) at the
   state after grow, from pj_set_spec's entry premise (FSH_Fn_reader.v pj_set_spec) *)
Lemma pSn_strdup_room : forall ly S ly' S' n cap kids keys k' y' cap' (Dold Dnew U U' : list (Z * Z)) klen,
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U U' -> 0 <= cap -> 0 <= klen ->
  Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B ly S ++ rd_hblocks Dnew) ->
  blocks_bytes S + rd_live (pj_set_c.set_trace n cap klen) <= LIVE_MAX ->
  blocks_bytes S' + (klen + 1 + HEAD) <= LIVE_MAX.
Proof.
intros ly S ly' S' n cap kids keys k' y' cap' Dold Dnew U U' klen HG Hc Hk HP HL.
pose proof (pSn_bb_after_grow_le ly S ly' S' 6 n cap kids keys k' y' cap' Dold Dnew U U' HG Hc HP) as HB.
rewrite (pSn_live_split n cap klen Hk) in HL. lia.
Qed.

End N.

