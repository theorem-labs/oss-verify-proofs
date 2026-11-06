(* fuzz_preset lib/A, the #102 re-walk of tx_put: the MODEL LAW of realloc (NULL, n), the model half of the realloc
   wrapper's null call, and its cf instance.
   rule 24: proves no function (kind: model law; tx_put's GROW segments cite realloc_null_model_law_x_cf as the model
   law RMN of YGcallRxKeep.aj_realloc_null_at_x_keep where cap0 = 0, the buffer empty, a0 = 0.)
   GENERIC: no preset name, no image class, no address, no ledger; the cf part uses only the shared instance classes
   CfImg / CfParams. Inputs (lib/Reusable): ReallocP.v (realloc_null_tree_with = free PNull then malloc), YGcallx.v
   (malloc_post_x), YGcfRealloc.v / YGcfAmx2.v (the malloc half of realloc_cf_atok: ipost_free_null, ROOM_cf_nfr,
   atok_cf_any_ns, no_null_block, blocks_bytes_blocks).

   1. THE MODEL LAW of the null tree (realloc_null_model_law_x): from a WFx state with the realloc room RQ, the tree
      realloc_null_tree_with mt ft n tr s is safe, granted-progressing and not a spin, and every model path moves the
      blocks as the malloc it is: malloc_post_x s n (NULL keeps them, success appends (q, n)). Same four-fact form and
      the same room predicate RQ as YGcallRx.v's realloc_model_law_x. YGcallRxKeep.v's realloc_null_model_law_x is
      the same text over the same variables, so a proof of this one is that rule's RMN.
   2. THE CF INSTANCE: realloc_null_cf_atok and realloc_null_model_law_x_cf (the law of 1 at the cf instance,
      RQ := qtight s /\ ROOM_cf_k s (RK_realloc + k), WFx := Wf_cf).
   Numerals: 1 is the least request size (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocP YGcallRx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcallcf YGcfRealloc YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfTok YG06bcf YG07cf YGcfRoomPre YG03cf YG03dcf YGcfAmx YGcfRoomKeep YGcfPath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAmx2.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The model law of the null tree, over YGcallRx.v Section gr's variables.     *)
Section gn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable RQ : astate -> Z -> list Z -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.

Definition realloc_null_model_law_x : Prop :=
forall s n tr, WFx s -> RQ s n tr -> 1 <= n < nmax -> blocks_bytes s + n <= LIVE_MAX -> admits (as_universe B) tr s ->
asafe (realloc_null_tree_with mt ft n tr s) /\ agprog (realloc_null_tree_with mt ft n tr s) /\
is_spin (realloc_null_tree_with mt ft n tr s) = false /\
(forall tr' r, apath (realloc_null_tree_with mt ft n tr s) tr' r -> malloc_post_x s n r) /\
(* the depot step (YGcallRx.v realloc_model_law_x's fifth fact, for the journal's wild-part budget) *)
(forall tr' r, apath (realloc_null_tree_with mt ft n tr s) tr' r -> incl (st_depot (snd r)) (st_depot s ++ [tr])).

End gn.

(* ---------------------------------------------------------------------------- *)
(* 2. The cf instance.                                                            *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* realloc (NULL, n) at the cf model is the free (NULL) frame step and then malloc_cf: its token, with
   malloc_post_x and the depot step on every result (YGcfAmx2.v realloc_cf_atok's first half, the inner malloc's post
   as the end; the depot as in YGcfAmx2.v: free(NULL) keeps it, ipost_free_null_depot, and malloc_cf stores at most
   the trace, YGcfAmx.dep_malloc_cf) *)
Theorem realloc_null_cf_atok : forall U s n tr,
universe_ok U -> Wf_cf U s -> ROOM_cf s -> 1 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
atok_cf true (realloc_null_tree_with malloc_cf free_cf n tr s)
  (fun _ r => malloc_post_x s n r /\ incl (st_depot (snd r)) (st_depot s ++ [tr])).
Proof.
intros U s n tr HU W HR Hn Hlive Htr.
unfold realloc_null_tree_with. apply atok_cf_bind.
(* free(NULL) *)
assert (A1 : atok_cf true (free_cf PNull tr s) (free_post_ycf U s PNull 0)).
{ unfold ROOM_cf in HR. destruct HR as (_ & _ & HB). eapply ml_free_cf; eauto. }
eapply atok_cf_mono; [|exact (atok_cf_ipost _ _ _ _ (atok_cf_ipost _ _ _ _ A1 (YGcfAmx2.ipost_free_null tr s))
  (YGcfAmx2.ipost_free_null_depot tr s))].
intros b [[] s1] [[F1 N1] D1]. cbn [fst snd] in *.
(* free(NULL) keeps the depot, so it keeps the call's trace premise (YG01.admits_keep; YGcfAmx2.realloc_cf_atok's step) *)
pose proof (admits_keep U tr s s1 Htr (or_introl D1)) as Htr1.
unfold free_post_ycf in F1. cbn [snd] in F1. destruct F1 as (W1 & Nev1 & X1 & Fr1 & (l1 & l2 & Bs1 & Bl1) & _).
assert (B1 : blocks s1 = blocks s).
{ rewrite Bl1. destruct Bs1 as [[_ E]|E]; [exact E|].
exfalso. apply (YGcfAmx2.no_null_block _ _ _ _ s 0 W). rewrite E. apply in_or_app. right. left. reflexivity. }
pose proof (YGcfAmx2.ROOM_cf_nfr s s1 N1 HR) as HR1. unfold ROOM_cf in HR1. destruct HR1 as (HS1 & HE1 & HB1).
assert (Hlive1 : blocks_bytes s1 + n <= LIVE_MAX)
  by (rewrite YGcfAmx2.blocks_bytes_blocks, B1, <- YGcfAmx2.blocks_bytes_blocks; exact Hlive).
(* malloc *)
pose proof (YGcfAmx.atok_cf_ipost _ _ _ _ (malloc_ok_cf U s1 n tr HU W1 ltac:(lia) Hlive1 Htr1 HS1 HE1 HB1)
  (YGcfAmx.dep_malloc_cf n tr s1)) as A2.
assert (A2b : atok_cf b (malloc_cf n tr s1) (fun b0 a => malloc_post_cf U s1 n b0 a /\
  (st_depot (snd a) = st_depot s1 \/ st_depot (snd a) = st_depot s1 ++ [tr]))).
{ apply YGcfAmx2.atok_cf_any_ns; [intros b1 b2 a H; exact H | exact A2]. }
eapply atok_cf_mono; [|exact A2b].
intros b2 [q s2] [M2 D2]. cbv beta. cbn [snd] in D2.
split.
2:{ cbn [snd]. destruct D2 as [E|E]; rewrite E, D1; [apply incl_appl, incl_refl | apply incl_refl]. }
unfold malloc_post_cf in M2. cbv beta iota in M2. destruct M2 as (W2 & Nev2 & X2 & Fr2 & Bl2 & _).
pose proof (proj1 (secs_ext_cf_of_secs_ext _ _ X1)) as L1. pose proof (proj1 X2) as L2.
unfold malloc_post_x.
split; [lia|]. split; [lia|]. split; [congruence|].
destruct q as [|qo|qr qo|qc qp]; cbv beta iota in Bl2 |- *.
- rewrite Bl2. exact B1.
- rewrite (proj1 Bl2), B1. reflexivity.
- rewrite (proj1 Bl2), B1. reflexivity.
- rewrite (proj1 Bl2), B1. reflexivity.
Qed.

Section J.
Variable B : asyms.

(* The null tree's model law (section 1) at the cf instance, for every headroom k. *)
Lemma realloc_null_model_law_x_cf : forall k, universe_ok (as_universe B) ->
realloc_null_model_law_x B (fun s _ _ => qtight s /\ ROOM_cf_k s (RK_realloc + k))
  malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).
Proof.
intros k HU s n tr HW (HQ & HRk) Hn Hlive Htr.
assert (HR : ROOM_cf s) by (apply RK_zero; apply (RK_mono s (RK_realloc + k) 0); [lia | exact HRk]).
pose proof (realloc_null_cf_atok (as_universe B) s n tr HU HW HR Hn Hlive Htr) as A.
split; [exact (atok_cf_asafe _ _ _ A)|]. split; [exact (atok_cf_agprog _ _ _ A)|].
split; [exact (atok_cf_nospin _ _ A)|].
split.
- intros tr' r Hpath. destruct (atok_cf_apath _ _ _ tr' r A Hpath) as [ns Hq]. exact (proj1 Hq).
- intros tr' r Hpath. destruct (atok_cf_apath _ _ _ tr' r A Hpath) as [ns Hq]. exact (proj2 Hq).
Qed.
End J.
End G.
