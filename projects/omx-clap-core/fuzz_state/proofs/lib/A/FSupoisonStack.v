(* The stack's shadow under ARU (lib/A/FSupoison.v): kit lemmas beside FSupoison.ARU_mem_low, for the walks whose
   token runs read the stack's shadow (READER lane). ARU's AR is about `unpoison U mem`; a walk's token run reads the
   machine memory `mem`. The two differ only at U's shadow cells, and those are all below the stack's shadow:
   - each range of U lies in whole granules of a live block (FSupoison.upoison_ok);
   - each live block ends at or below alloc_ceiling (AR_blocks_law, lib/Reusable/YG0d.v);
   - the stack starts at or above alloc_ceiling (layout_ok.lo_stk_ceil, lib/Reusable/YG0f.v);
   - shadow_addr a = SHADOW_OFF + a / 8 is monotone.
   So every shadow cell at or above shadow_addr (ly_stk_lo ly) reads the same in both memories, and the
   range_addressable / shadow_hull_vis facts of a stack range transfer between them in both directions.
   The IMAGE's shadow likewise (fsw_ARU_img_*, for walks that read an image object's shadow, e.g. an rodata string's
   cstr_ok): every user-poisoned shadow cell is at or above the shadow of the image's end (FSupoisonARXm.ush_lo: user
   heads lie in live blocks, which lie above the image), so the shadow of an image address reads the same in both
   memories. These lemmas are VALUE-INDEPENDENT: they say nothing about what the image shadow holds; that comes from
   AR's am_zshadow / am_const (YG0n.v:187-190, :210) over whatever tables the image's asyms give. Only facts that ARU
   and AR_laws already carry are used; no Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARXm FSupoisonARX AB1v AF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
#[local] Abbreviation ARU := (ARU segs B).
(* The layout facts of the stack's low end that the lemmas below use. *)
Lemma fsw_ARU_stk_lo : forall ly S U W mem md, ARU ly S U W mem md ->
  alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly mod 4096 = 0 /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
intros ly S U W mem md (HAR & _ & _). pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
pose proof (lo_stk_ceil ly LO) as SC. pose proof (lo_top ly LO) as (_ & _ & _ & _ & T5 & _ & T7).
split; [exact SC | split; [exact T5 | exact T7]].
Qed.
(* Every user-poisoned shadow cell is below the stack's shadow. *)
Lemma fsw_ARU_ush_below_stack : forall ly S U W mem md s, ARU ly S U W mem md -> in_ush U s = true ->
  s < shadow_addr (ly_stk_lo ly).
Proof.
intros ly S U W mem md s HU Hs. pose proof (fsw_ARU_stk_lo ly S U W mem md HU) as (SC & _ & _).
pose proof HU as (HAR & [F _] & _). apply in_ush_spec in Hs as (r & Hr & Hs).
pose proof (proj1 (Forall_forall _ _) F r Hr) as (A8 & _ & M8 & p & n & Hb & _ & Pn).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (_ & _ & PC & _).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
apply Z.mod_divide in A8 as [q Hq]; [|lia]. apply Z.mod_divide in M8 as [m Hm]; [|lia].
unfold shadow_addr in Hs |- *. rewrite Hq, Hm, !Z.div_mul in Hs by lia.
assert (L : q + m <= ly_stk_lo ly / 8) by (apply Z.div_le_lower_bound; lia).
lia.
Qed.
(* ARU_mem_low's form at the stack's shadow: a cell at or above shadow_addr (ly_stk_lo ly) reads the same in both
   memories. *)
Lemma fsw_ARU_stack_cell : forall ly S U W mem md w, ARU ly S U W mem md -> shadow_addr (ly_stk_lo ly) <= bv_unsigned w ->
  unpoison U mem w = mem w.
Proof.
intros ly S U W mem md w HU Hw. apply unpoison_out. destruct (in_ush U (bv_unsigned w)) eqn:E; [|reflexivity].
exfalso. pose proof (fsw_ARU_ush_below_stack ly S U W mem md _ HU E). lia.
Qed.
(* The shadow byte of any stack address reads the same in both memories. *)
Lemma fsw_ARU_stack_shadow : forall ly S U W mem md a, ARU ly S U W mem md -> ly_stk_lo ly <= a < 2 ^ 64 ->
  unpoison U mem (Z_to_bv 64 (shadow_addr a)) = mem (Z_to_bv 64 (shadow_addr a)).
Proof.
intros ly S U W mem md a HU Ha. pose proof (fsw_ARU_stk_lo ly S U W mem md HU) as (_ & _ & K).
apply (fsw_ARU_stack_cell ly S U W mem md _ HU).
pose proof (Z.div_le_mono (ly_stk_lo ly) a 8 ltac:(lia) ltac:(lia)) as D.
pose proof (Z.div_pos (ly_stk_lo ly) 8 ltac:(unfold kHighMemBeg in K; lia) ltac:(lia)) as P.
pose proof (Z.div_lt_upper_bound a 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as U8.
rewrite wz by (unfold shadow_addr, SHADOW_OFF; lia). unfold shadow_addr. lia.
Qed.
(* The same through the reader a walk uses (aview), for any hidden-page map H. *)
Lemma fsw_ARU_stack_shadow_view : forall ly S U W mem md H a, ARU ly S U W mem md -> ly_stk_lo ly <= a < 2 ^ 64 ->
  aview segs H (unpoison U mem) (shadow_addr a) = aview segs H mem (shadow_addr a).
Proof. intros ly S U W mem md H a HU Ha. apply aview_at. exact (fsw_ARU_stack_shadow ly S U W mem md a HU Ha). Qed.
(* A shadow cell at or above the stack's shadow, through aview. *)
Lemma fsw_ARU_stack_cell_view : forall ly S U W mem md H s, ARU ly S U W mem md ->
  shadow_addr (ly_stk_lo ly) <= s < 2 ^ 64 -> aview segs H (unpoison U mem) s = aview segs H mem s.
Proof.
intros ly S U W mem md H s HU Hs. pose proof (fsw_ARU_stk_lo ly S U W mem md HU) as (_ & _ & K).
pose proof (Z.div_pos (ly_stk_lo ly) 8 ltac:(unfold kHighMemBeg in K; lia) ltac:(lia)) as P.
apply aview_at. apply (fsw_ARU_stack_cell ly S U W mem md _ HU).
rewrite wz by (unfold shadow_addr, SHADOW_OFF in Hs; lia). lia.
Qed.
(* Range corollary: for a range at or above the stack's low end, range_addressable of its shadow holds of one memory
   iff of the other (the per-entry fact of a token run's sh_ok: rd_of segs (mrestrict H m) is aview segs H m). *)
Lemma fsw_ARU_stack_ra : forall ly S U W mem md H lo n, ARU ly S U W mem md -> ly_stk_lo ly <= lo -> lo + n <= 2 ^ 64 ->
  range_addressable (aview segs H (unpoison U mem)) SHADOW_OFF lo n <-> range_addressable (aview segs H mem) SHADOW_OFF lo n.
Proof.
intros ly S U W mem md H lo n HU Hlo Hn.
assert (E : forall x, lo <= x < lo + n ->
  aview segs H (unpoison U mem) (shadow_of_addr SHADOW_OFF x) = aview segs H mem (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. exact (fsw_ARU_stack_shadow_view ly S U W mem md H x HU ltac:(lia)). }
unfold range_addressable. split; intros R x Hx; specialize (R x Hx); [rewrite <- (E x Hx) | rewrite (E x Hx)]; exact R.
Qed.
(* Range corollary: shadow_hull_vis (the 8-byte words of shadow a check loads) of a range at or above the stack's low
   end holds of one memory iff of the other. *)
Lemma fsw_ARU_stack_hull : forall ly S U W mem md H x n, ARU ly S U W mem md -> ly_stk_lo ly <= x -> x + n <= 2 ^ 64 ->
  shadow_hull_vis (aview segs H (unpoison U mem)) x n <-> shadow_hull_vis (aview segs H mem) x n.
Proof.
intros ly S U W mem md H x n HU Hx Hn. pose proof (fsw_ARU_stk_lo ly S U W mem md HU) as (_ & A & K).
assert (E : forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  aview segs H (unpoison U mem) s = aview segs H mem s).
{ intros s Hs. apply (fsw_ARU_stack_cell_view ly S U W mem md H s HU).
  apply Z.mod_divide in A as [k Hk]; [|lia].
  pose proof (Z.div_mod x 8 ltac:(lia)) as X1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as X2.
  pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as S1. pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as S2.
  pose proof (Z.mul_div_le (shadow_addr (x + n - 1)) 8 ltac:(lia)) as V1.
  pose proof (Z.div_le_mono (x + n - 1) (2 ^ 64 - 1) 8 ltac:(lia) ltac:(lia)) as V2.
  change ((2 ^ 64 - 1) / 8) with 2305843009213693951 in V2.
  assert (L : shadow_addr (ly_stk_lo ly) = SHADOW_OFF + 512 * k).
  { unfold shadow_addr. rewrite Hk. replace (k * 4096) with ((512 * k) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  rewrite L. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
split; intros V s Hs; [rewrite <- (E s Hs) | rewrite (E s Hs)]; exact (V s Hs).
Qed.

(* ---- the image's shadow ---- *)
(* ARU_mem_low's form below the shadow of the image's end. *)
Lemma fsw_ARU_img_cell : forall ly S U W mem md w, ARU ly S U W mem md ->
  bv_unsigned w < shadow_addr (fst (ly_img ly) + snd (ly_img ly)) -> unpoison U mem w = mem w.
Proof.
intros ly S U W mem md w HU Hw. apply unpoison_out. destruct (in_ush U (bv_unsigned w)) eqn:E; [|reflexivity].
exfalso. pose proof (FSupoisonARXm.ush_lo segs B ly S U W mem md _ HU E). lia.
Qed.
(* The shadow byte of an image address (a whole granule below the image's end) reads the same in both memories. *)
Lemma fsw_ARU_img_shadow : forall ly S U W mem md a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  a + 8 <= fst (ly_img ly) + snd (ly_img ly) ->
  unpoison U mem (Z_to_bv 64 (shadow_addr a)) = mem (Z_to_bv 64 (shadow_addr a)).
Proof.
intros ly S U W mem md a HU Ha HE. apply (fsw_ARU_img_cell ly S U W mem md _ HU).
pose proof (Z.div_le_mono (a + 1 * 8) (fst (ly_img ly) + snd (ly_img ly)) 8 ltac:(lia) ltac:(lia)) as D.
rewrite Z.div_add in D by lia.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)) as P.
pose proof (Z.div_lt_upper_bound a 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as U8.
rewrite wz by (unfold shadow_addr, SHADOW_OFF; lia). unfold shadow_addr. lia.
Qed.
Lemma fsw_ARU_img_shadow_view : forall ly S U W mem md H a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  a + 8 <= fst (ly_img ly) + snd (ly_img ly) -> aview segs H (unpoison U mem) (shadow_addr a) = aview segs H mem (shadow_addr a).
Proof. intros ly S U W mem md H a HU Ha HE. apply aview_at. exact (fsw_ARU_img_shadow ly S U W mem md a HU Ha HE). Qed.
(* A shadow cell below the shadow of the image's end, through aview. *)
Lemma fsw_ARU_img_cell_view : forall ly S U W mem md H s, ARU ly S U W mem md -> 0 <= s < 2 ^ 64 ->
  s < shadow_addr (fst (ly_img ly) + snd (ly_img ly)) -> aview segs H (unpoison U mem) s = aview segs H mem s.
Proof.
intros ly S U W mem md H s HU Hs HE. apply aview_at. apply (fsw_ARU_img_cell ly S U W mem md _ HU).
rewrite wz by lia. exact HE.
Qed.
(* Range corollary (an image object's range_addressable, e.g. the per-byte shadow test of a string). *)
Lemma fsw_ARU_img_ra : forall ly S U W mem md H lo n, ARU ly S U W mem md -> 0 <= lo -> lo + n <= 2 ^ 64 ->
  lo + n + 8 <= fst (ly_img ly) + snd (ly_img ly) ->
  range_addressable (aview segs H (unpoison U mem)) SHADOW_OFF lo n <-> range_addressable (aview segs H mem) SHADOW_OFF lo n.
Proof.
intros ly S U W mem md H lo n HU Hlo Hn HE.
assert (E : forall x, lo <= x < lo + n ->
  aview segs H (unpoison U mem) (shadow_of_addr SHADOW_OFF x) = aview segs H mem (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. exact (fsw_ARU_img_shadow_view ly S U W mem md H x HU ltac:(lia) ltac:(lia)). }
unfold range_addressable. split; intros R x Hx; specialize (R x Hx); [rewrite <- (E x Hx) | rewrite (E x Hx)]; exact R.
Qed.
(* Range corollary for the 8-byte shadow words a check loads (64 application bytes of margin below the image's end). *)
Lemma fsw_ARU_img_hull : forall ly S U W mem md H x n, ARU ly S U W mem md -> 0 <= x -> 1 <= n -> x + n <= 2 ^ 64 ->
  x + n + 64 <= fst (ly_img ly) + snd (ly_img ly) ->
  shadow_hull_vis (aview segs H (unpoison U mem)) x n <-> shadow_hull_vis (aview segs H mem) x n.
Proof.
intros ly S U W mem md H x n HU Hx Hn1 Hn HE.
assert (E : forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
  aview segs H (unpoison U mem) s = aview segs H mem s).
{ intros s Hs. pose proof (Z.mul_div_le (shadow_addr x) 8 ltac:(lia)) as V0.
  pose proof (Z.mul_div_le (shadow_addr (x + n - 1)) 8 ltac:(lia)) as V1.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P0.
  pose proof (Z.div_pos (shadow_addr x) 8 ltac:(unfold shadow_addr, SHADOW_OFF; lia) ltac:(lia)) as P1.
  pose proof (Z.div_le_mono (x + n - 1 + 8 * 8) (fst (ly_img ly) + snd (ly_img ly)) 8 ltac:(lia) ltac:(lia)) as D.
  rewrite Z.div_add in D by lia.
  pose proof (Z.div_le_mono (x + n - 1) (2 ^ 64 - 1) 8 ltac:(lia) ltac:(lia)) as V2.
  change ((2 ^ 64 - 1) / 8) with 2305843009213693951 in V2.
  apply (fsw_ARU_img_cell_view ly S U W mem md H s HU); unfold shadow_addr, SHADOW_OFF in *; lia. }
split; intros V s Hs; [rewrite <- (E s Hs) | rewrite (E s Hs)]; exact (V s Hs).
Qed.

(* ---- the image's shadow VALUES in every ARU state (a Theorem Labs lane 02:06Z: img_shadow_kept) ----
   AR (on `unpoison U mem`) pins the image shadow through ARm's am_zshadow (YG0n.v:187-190: every as_zero_shadow range
   reads 0) and am_const (YG0n.v:210: every as_const cell holds, incl. the globals' partial / redzone shadow bytes).
   With the transfer above, the same values hold of the machine memory `mem`. Being a fact of EVERY ARU state, the
   value is unchanged across any call whose post re-establishes ARU: this is the shadow part of the rodata arm of
   a Theorem Labs lane's cstr_ok_kept_call / fs_img_facts (kit FSW_rd). VALUE-INDEPENDENT: the values are whatever the image's
   asyms tables state; fs's own table is the generated A/AF0m.v of the start-up layer. *)
(* A zero-shadow granule of the image reads 0 in `mem`. *)
Lemma fsw_ARU_img_zero : forall ly S U W mem md r i, ARU ly S U W mem md -> In r (as_zero_shadow B) ->
  0 <= i < snd r / 8 -> aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF (fst r) + i) = Some 0.
Proof.
intros ly S U W mem md r i HU Hr Hi. pose proof HU as (HAR & _ & _). pose proof (proj1 HAR) as M.
pose proof (am_zshadow B ly S _ M) as ZS. unfold zshadow_ok, zero_shadow_ranges in ZS.
pose proof (proj1 (Forall_forall _ _) ZS r (or_intror Hr) i Hi) as Z0.
pose proof (proj1 (Forall_forall _ _) (aso_zshadow B (am_syms B ly S _ M)) r Hr) as (R0 & R1 & R8 & L8 & RL).
pose proof (proj1 (Forall_forall _ _) (am_static_img B ly S _ M) r (in_or_app _ _ _ (or_intror Hr))) as (_ & SUB).
rewrite <- (fsw_ARU_img_cell_view ly S U W mem md (w_H W) _ HU); [exact Z0| |].
- unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (fst r) (2 ^ 61) 8 ltac:(lia) ltac:(lia)). lia.
- apply Z.mod_divide in R8 as [q Hq]; [|lia]. apply Z.mod_divide in L8 as [m Hm]; [|lia].
  pose proof (Z.div_le_mono (fst r + snd r) (fst (ly_img ly) + snd (ly_img ly)) 8 ltac:(lia) ltac:(lia)) as D.
  unfold shadow_of_addr, shadow_addr in *. rewrite Hq, Hm in *. rewrite Z.div_mul in * by lia.
  rewrite <- Z.mul_add_distr_r, Z.div_mul in D by lia. lia.
Qed.
(* An as_const cell lying below the shadow of the image's end holds of `mem` (any value form). *)
Lemma fsw_ARU_img_const : forall ly S U W mem md c, ARU ly S U W mem md -> In c (as_const B ly) ->
  0 <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= 2 ^ 64 ->
  aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= shadow_addr (fst (ly_img ly) + snd (ly_img ly)) ->
  cell_holds B ly (aview segs (w_H W) mem) c.
Proof.
intros ly S U W mem md c HU Hc H0 H64 HE. pose proof HU as (HAR & _ & _). pose proof (proj1 HAR) as M.
pose proof (proj1 (Forall_forall _ _) (am_const B ly S _ M) c Hc) as CH.
assert (V : forall s, aeval B ly (c_at c) <= s < aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) ->
  aview segs (w_H W) (unpoison U mem) s = aview segs (w_H W) mem s).
{ intros s Hs. apply (fsw_ARU_img_cell_view ly S U W mem md (w_H W) s HU); lia. }
unfold cell_holds in *. destruct (c_val c) as [e | mask v].
- intros k Hk. rewrite <- V; [exact (CH k Hk)|]. lia.
- destruct CH as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- V; [exact Hb|]. lia.
Qed.
End s.

(* fs image A: the image's end is at or above TFIB_IMG_END = 0x5fd000 (FSupoisonARX.fs_img_end, from ALedger.al_img),
   so the premise on the image's end becomes a literal bound. AR is ARU's first conjunct. *)
Lemma fsw_ARU_img_end_fs : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B ly S U W mem md,
  FSupoison.ARU AB1v.tfibsegs B ly S U W mem md -> AF0x.TFIB_IMG_END <= fst (ly_img ly) + snd (ly_img ly).
Proof. intros fx rc B ly S U W mem md (HAR & _). exact (FSupoisonARX.fs_img_end B ly S W (unpoison U mem) md HAR). Qed.
Lemma fsw_ARU_rodata_ra : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B ly S U W mem md H lo n,
  FSupoison.ARU AB1v.tfibsegs B ly S U W mem md -> 0 <= lo -> lo + n + 8 <= AF0x.TFIB_IMG_END ->
  range_addressable (aview AB1v.tfibsegs H (unpoison U mem)) SHADOW_OFF lo n <->
  range_addressable (aview AB1v.tfibsegs H mem) SHADOW_OFF lo n.
Proof.
intros fx rc B ly S U W mem md H lo n HU Hlo HE. pose proof (fsw_ARU_img_end_fs B ly S U W mem md HU) as IE.
unfold AF0x.TFIB_IMG_END in *. apply (fsw_ARU_img_ra AB1v.tfibsegs B ly S U W mem md H lo n HU); lia.
Qed.
