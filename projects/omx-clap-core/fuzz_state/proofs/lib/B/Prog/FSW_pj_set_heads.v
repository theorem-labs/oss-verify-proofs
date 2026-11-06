(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 190 of its 277 lines of code are new or changed and 1286 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_rres.v, with its module names changed; 301 of its 340 lines of code are new or changed and 238 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/Prog/FSW_pj_set_heads.v, with its module paths changed; 7 of its 345 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) copy of lib/A/Prog/FSW_pj_set_heads.v (a working branch
   e45b7c0a2da, taken there from a working branch 42571479544), same lemma names and bodies; imports point
   at lib/B's image files and kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_reader, FSW_rd, FSW_strkit); the
   Section binds the sink head explicitly (owner rule, a Theorem Labs lane); no image value (B's FS_PSTAT_FP and
   FS_IMG_END are read by name from lib/B). *)
(* pj_set's composition (a Theorem Labs lane, FSW_pj_set_holds.v): the U / block bookkeeping across grow (B 0x83ca8), list and
   block reasoning only (no stage, no walk, no SRr). For grow called on an OBJECT (ty = 6, PjTree.tag PJ_OBJECT), with
   grow_spec's result (FSH_Fn_reader.v grow_res) and its post (the new slots' rd_blocks_ok, the Permutation of blocks,
   the journal's block survival off grow's footprint):
   - pSh_ug_sub            : a head of U' is a head of U or one of the two new heads.
   - pSh_ug_removed        : a head of U' other than the new heads is neither old head (n = cap, 0 < cap).
   - pSh_obj_apart         : a live block lies wholly before a pobj object, wholly after it, or holds it past its head.
   - pSh_heads_after_grow  : FSupoisonU.fs_heads at grow's return.
   - pSh_fresh_after_grow  : the new kids / keys blocks were not live before grow (from grow's Permutation post).
   - pSh_cstr_U_after_grow : each head of U' is in U or avoids the key string (cstr_ok_kept_call's U' premise, FSW_rd.v).
   A LEMMA FILE (rule 24): no function's contract is proved here; no Section hypothesis. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_rd FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- list facts (no state) ---- *)
Definition pSh_zz_dec (a b : Z * Z) : {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* a pairwise-disjoint list of non-empty ranges has no duplicate (Stdlib's List.NoDup: stdpp's NoDup is in scope) *)
Lemma pSh_nodup : forall l : list (Z * Z), pairwise zdisjoint l -> Forall (fun r => 0 < snd r) l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros P F; [constructor|].
destruct P as [Fx P]. apply Forall_cons_iff in F as [Hx F]. cbv beta in Hx.
constructor; [|exact (IH P F)].
intros Hin. rewrite Forall_forall in Fx. specialize (Fx x Hin). unfold zdisjoint in Fx. lia.
Qed.

(* l ++ [y] with l duplicate-free: an x <> y taken out at one place is nowhere else *)
Lemma pSh_split_once : forall (l V1 V2 : list (Z * Z)) x y, List.NoDup l -> l ++ [y] = V1 ++ x :: V2 -> x <> y ->
  ~ In x (V1 ++ V2).
Proof.
intros l V1 V2 x y ND E Nxy Hin.
pose proof (f_equal (fun l0 => count_occ pSh_zz_dec l0 x) E) as C. cbv beta in C.
rewrite !count_occ_app in C.
assert (Cy : count_occ pSh_zz_dec [y] x = 0%nat)
  by (cbn [count_occ]; destruct (pSh_zz_dec y x); [congruence | reflexivity]).
assert (Cx : count_occ pSh_zz_dec (x :: V2) x = S (count_occ pSh_zz_dec V2 x))
  by (cbn [count_occ]; destruct (pSh_zz_dec x x); [reflexivity | congruence]).
rewrite Cy, Cx in C.
pose proof (proj1 (@NoDup_count_occ _ pSh_zz_dec l) ND x) as Hl.
apply in_app_or in Hin as [Hin|Hin]; apply (@count_occ_In _ pSh_zz_dec) in Hin; lia.
Qed.

(* A3 ++ Do a permutation of A1 ++ Dn, A3 duplicate-free: an x of Dn that is not in Do is not in A1 *)
Lemma pSh_perm_fresh : forall (A3 A1 Do Dn : list (Z * Z)) x, List.NoDup A3 -> Permutation (A3 ++ Do) (A1 ++ Dn) ->
  ~ In x Do -> In x Dn -> ~ In x A1.
Proof.
intros A3 A1 Do Dn x ND P NDo HDn HA1.
pose proof (proj1 (@Permutation_count_occ _ pSh_zz_dec _ _) P x) as C.
rewrite !count_occ_app in C.
pose proof (proj1 (@NoDup_count_occ _ pSh_zz_dec A3) ND x) as C3.
pose proof (proj1 (@count_occ_not_In _ pSh_zz_dec Do x) NDo) as C0.
apply (@count_occ_In _ pSh_zz_dec) in HDn. apply (@count_occ_In _ pSh_zz_dec) in HA1. lia.
Qed.

(* one realloc's U step: a head after it was a head before, or is the new head *)
Lemma pSh_ugrow1_sub : forall U U' old new r, ugrow1 U U' old new -> In r U' -> In r U \/ r = (new - HEAD, HEAD).
Proof.
intros U U' old new r [(_ & ->) | (_ & U1 & U2 & -> & ->)] Hr.
- apply in_app_or in Hr as [Hr | [<- | []]]; [left; exact Hr | right; reflexivity].
- rewrite app_assoc in Hr. apply in_app_or in Hr as [Hr | [<- | []]]; [left | right; reflexivity].
  apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left; exact Hr | right; right; exact Hr].
Qed.

(* the kids / keys blocks of an object of capacity cap *)
Lemma pSh_blk_0 : forall kids keys, ReaderRes.kids_blk kids 0 ++ ReaderRes.keys_blk 6 keys 0 = [].
Proof. reflexivity. Qed.
Lemma pSh_blk_ne0 : forall kids keys cap, cap <> 0 ->
  ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap = [(kids, 56 * cap); (keys, 8 * cap)].
Proof. intros kids keys cap H. unfold ReaderRes.kids_blk, ReaderRes.keys_blk. destruct (Z.eqb_spec cap 0); [lia | reflexivity]. Qed.
Lemma pSh_old_in : forall kids keys cap a k,
  In (a, k) (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) ->
  (a = kids /\ k = 56 * cap) \/ (a = keys /\ k = 8 * cap).
Proof.
intros kids keys cap a k H. destruct (Z.eq_dec cap 0) as [-> | Hc].
- rewrite pSh_blk_0 in H. destruct H.
- rewrite (pSh_blk_ne0 kids keys cap Hc) in H.
  destruct H as [E | [E | []]]; injection E as <- <-; [left | right]; split; reflexivity.
Qed.
(* a byte of grow's old-block footprint lies in the ASan block (a - HEAD, k + HEAD) of some old reader block (a, k) *)
Lemma pSh_inFP_hblocks : forall D x, inFP (ablocks_fp (rd_hblocks D)) x ->
  exists a k, In (a, k) D /\ a - HEAD <= x < a - HEAD + req_size (k + HEAD).
Proof.
intros D x (r & Hr & Hx). unfold ablocks_fp, rd_hblocks in Hr. rewrite map_map in Hr.
apply in_map_iff in Hr as ([a k] & <- & Hin). cbn [fst snd] in Hx. exists a, k. split; [exact Hin | exact Hx].
Qed.

(* ---- 1. pSh_ug_sub: the heads after grow ---- *)
Lemma pSh_ug_sub : forall n cap kids keys k' y' cap' Dold Dnew U Ug,
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug -> forall r, In r Ug ->
  In r U \/ r = (k' - HEAD, HEAD) \/ r = (y' - HEAD, HEAD).
Proof.
intros n cap kids keys k' y' cap' Dold Dnew U Ug G r Hr.
destruct G as [(_ & _ & _ & _ & _ & _ & ->) | (_ & _ & _ & _ & _ & _ & _ & _ & Um & G1 & G2)].
- left. exact Hr.
- change (ugrow1 Um Ug keys y') in G2.
  destruct (pSh_ugrow1_sub Um Ug keys y' r G2 Hr) as [Hm | E]; [|right; right; exact E].
  destruct (pSh_ugrow1_sub U Um kids k' r G1 Hm) as [Hu | E]; [left; exact Hu | right; left; exact E].
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* every range of U starts at or above 4096 (it lies in a live block) *)
Lemma pSh_U_low : forall ly S U (W : world tfibsegs) mem md r, ARU tfibsegs B ly S U W mem md -> In r U -> 4096 <= fst r.
Proof.
intros ly S U W mem md r (HAR & (F & _) & _) Hr.
rewrite Forall_forall in F. destruct (F r Hr) as (_ & _ & _ & p & nn & Hin & Hp & _).
destruct (al_blocks tfibsegs B LAWS ly S W _ md p nn HAR Hin) as (_ & H4 & _). lia.
Qed.
(* a live block list has no duplicate (its ranges are pairwise disjoint and non-empty) *)
Lemma pSh_ablocks_nodup : forall ly S (W : world tfibsegs) mx md, AR tfibsegs B ly S W mx md ->
  List.NoDup (ablocks B ly S).
Proof.
intros ly S W mx md HAR.
destruct (al_sep tfibsegs B LAWS ly S W mx md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
eapply NoDup_map_inv.
apply pSh_nodup; [exact Hp|].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([p nn] & <- & Hin). cbn [fst snd].
destruct (al_blocks tfibsegs B LAWS ly S W mx md p nn HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos nn ltac:(lia)) as (H1 & _). lia.
Qed.

(* ---- 2. pSh_ug_removed: grow (n = cap, 0 < cap) disowns both old heads; a head of U' that is not new is neither
   (the new-head premises matter: realloc may answer the old pointer, k' = kids) ---- *)
Lemma pSh_ug_removed : forall ly1 S1 U (W1 : world tfibsegs) mem1 md1 n cap kids keys k' y' cap' Dold Dnew Ug,
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  ARU tfibsegs B ly1 S1 U W1 mem1 md1 ->
  incl (rd_heads (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) U ->
  forall r, In r Ug -> r <> (k' - HEAD, HEAD) -> r <> (y' - HEAD, HEAD) ->
  0 < cap -> n = cap -> r <> (kids - HEAD, HEAD) /\ r <> (keys - HEAD, HEAD).
Proof.
intros ly1 S1 U W1 mem1 md1 n cap kids keys k' y' cap' Dold Dnew Ug G HU HI r Hr Nk Ny Hc Hn.
destruct G as [(Hlt & _) | (_ & _ & _ & _ & _ & _ & _ & _ & Um & G1 & G2)]; [lia|].
change (ugrow1 Um Ug keys y') in G2.
assert (Hc0 : cap <> 0) by lia.
rewrite (pSh_blk_ne0 kids keys cap Hc0) in HI.
assert (Hik : In (kids - HEAD, HEAD) U) by (apply HI; left; reflexivity).
assert (Hiy : In (keys - HEAD, HEAD) U) by (apply HI; right; left; reflexivity).
pose proof (pSh_U_low _ _ _ _ _ _ _ HU Hik) as Lk. pose proof (pSh_U_low _ _ _ _ _ _ _ HU Hiy) as Ly.
cbn [fst] in Lk, Ly.
assert (ND : List.NoDup U).
{ destruct HU as (_ & (F & PW) & _). apply pSh_nodup; [exact PW|].
  apply Forall_forall. intros x Hx. rewrite Forall_forall in F. destruct (F x Hx) as (_ & H8 & _). lia. }
destruct G1 as [(E0 & _) | (_ & U1 & U2 & EU & EUm)]; [unfold HEAD in Lk; lia|].
destruct G2 as [(E0 & _) | (_ & V1 & V2 & EVm & EUg)]; [unfold HEAD in Ly; lia|].
rewrite EUg, app_assoc in Hr. apply in_app_or in Hr as [Hr | [E | []]]; [|exfalso; exact (Ny (eq_sym E))].
assert (HrUm : In r Um).
{ rewrite EVm. apply in_app_or in Hr as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]. }
rewrite EUm, app_assoc in HrUm. apply in_app_or in HrUm as [HrU | [E | []]]; [|exfalso; exact (Nk (eq_sym E))].
rewrite EU in ND.
pose proof ND as ND12. apply NoDup_remove_1 in ND12.
pose proof ND as NIk. apply NoDup_remove_2 in NIk.
split; intros ->.
- exact (NIk HrU).
- assert (Eu : (U1 ++ U2) ++ [(k' - HEAD, HEAD)] = V1 ++ (keys - HEAD, HEAD) :: V2)
    by (rewrite <- app_assoc, <- EUm; exact EVm).
  exact (pSh_split_once (U1 ++ U2) V1 V2 _ _ ND12 Eu Nk Hr).
Qed.

(* ---- 3. pSh_obj_apart: a live block and a pobj object (a fake-frame object, or a kid past its block's head) ---- *)
Lemma pSh_obj_apart : forall ly S (W : world tfibsegs) mx md m o,
  AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m o ->
  forall p nn, In (p, nn) (ablocks B ly S) ->
  p + req_size nn <= o \/ o + 56 <= p \/ (p + HEAD <= o /\ o + 56 <= p + req_size nn).
Proof.
intros ly S W mx md m o HAR ([((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] & _) p nn Hp.
- pose proof (sep_block_frame tfibsegs B LAWS ly S W mx md p nn cid pos HAR Hp Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
- destruct (pSh_zz_dec (p, nn) (b, n)) as [E | NE].
  + injection E as -> ->. right; right. split; assumption.
  + pose proof (sep_blocks tfibsegs B LAWS ly S W mx md p nn b n HAR Hp Hin NE) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold HEAD in H1. lia.
Qed.

(* ---- pSh_heads_after_grow: fs_heads at grow's return. A head of a new slot block: that block is live at (ly3, S3)
   by the new slots' rd_blocks_ok. Any other head (q, 16) was in U, and is not an old kids / keys head; its block
   (q, m) at (ly1, S1) survives grow because its first byte q is off grow's footprint: q is below obj's fields or
   past them (pSh_obj_apart's form), outside the old kids / keys blocks (live blocks are disjoint), and no image
   byte (fuzz/alloc.c's statics are image bytes) ---- *)
Lemma pSh_heads_after_grow :
forall ly1 S1 U ly3 S3 Ug (W1 W3 : world tfibsegs) mem1 mem3 md1 md3 o kids keys n cap k' y' cap' Dold Dnew,
  ARU tfibsegs B ly1 S1 U W1 mem1 md1 -> ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 ->
  FSupoisonU.fs_heads B ly1 S1 U ->
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  incl (rd_heads (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) U ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 mem1 (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn ->
     ~ inFP ([(o + 24, o + 40); (o + 48, o + 56)] ++
             ablocks_fp (rd_hblocks (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) ++
             FS_PSTAT_FP) x ->
     In (p, nn) (ablocks B ly3 S3)) ->
  (forall p nn, In (p, nn) (ablocks B ly1 S1) ->
     p + req_size nn <= o \/ o + 56 <= p \/ (p + HEAD <= o /\ o + 56 <= p + req_size nn)) ->
  FSupoisonU.fs_heads B ly3 S3 Ug.
Proof.
intros ly1 S1 U ly3 S3 Ug W1 W3 mem1 mem3 md1 md3 o kids keys n cap k' y' cap' Dold Dnew
  HU1 HU3 FH G HI RB1 RB3 SURV APART r Hr.
pose proof HU1 as (HAR1 & _).
destruct (in_dec pSh_zz_dec r (rd_heads (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap')))
  as [HrN | HrN].
- (* the head of a new slot block *)
  unfold rd_heads in HrN. apply in_map_iff in HrN as ([a k] & <- & Hak).
  destruct (RB3 a k Hak) as (Hin3 & _ & Hk & _).
  cbn [fst snd]. split; [reflexivity|]. exists (k + HEAD). split; [exact Hin3|].
  unfold req_size, HEAD. destruct (Z.eqb_spec (k + 16) 0); lia.
- (* a head that was in U *)
  assert (HrNot : forall a k, In (a, k) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
    r <> (a - HEAD, HEAD)).
  { intros a k Hak E. apply HrN. unfold rd_heads. apply in_map_iff. exists (a, k).
    split; [rewrite E; reflexivity | exact Hak]. }
  assert (HK : In r U /\ (0 < cap -> r <> (kids - HEAD, HEAD) /\ r <> (keys - HEAD, HEAD))).
  { pose proof G as G'.
    destruct G' as [(_ & Ek & Ey & Ec & _ & _ & EUg) | (Hn & Ec & _)].
    - subst k' y' cap' Ug. split; [exact Hr|]. intros Hc.
      assert (Hc0 : cap <> 0) by lia.
      rewrite (pSh_blk_ne0 kids keys cap Hc0) in HrNot.
      split; [exact (HrNot kids (56 * cap) (or_introl eq_refl))
             | exact (HrNot keys (8 * cap) (or_intror (or_introl eq_refl)))].
    - assert (Hc' : cap' <> 0) by (rewrite Ec; unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
      rewrite (pSh_blk_ne0 k' y' cap' Hc') in HrNot.
      pose proof (HrNot k' (56 * cap') (or_introl eq_refl)) as Nk.
      pose proof (HrNot y' (8 * cap') (or_intror (or_introl eq_refl))) as Ny.
      split.
      + destruct (pSh_ug_sub _ _ _ _ _ _ _ _ _ _ _ G r Hr) as [H | [E | E]];
          [exact H | exfalso; exact (Nk E) | exfalso; exact (Ny E)].
      + intros Hc. exact (pSh_ug_removed ly1 S1 U W1 mem1 md1 n cap kids keys k' y' cap' Dold Dnew Ug
          G HU1 HI r Hr Nk Ny Hc Hn). }
  destruct HK as (HrU & Nold).
  destruct (FH r HrU) as (E16 & m & Hm & H16).
  destruct r as [q s]. cbn [fst snd] in E16, Hm. subst s.
  cbn [fst snd]. split; [reflexivity|]. exists m. split; [|exact H16].
  assert (Hq : q <= q < q + req_size m) by lia.
  apply (SURV q m q Hm Hq).
  rewrite !inFP_app. intros [HF | [HF | HF]].
  + (* obj's fields *)
    rewrite !inFP_cons in HF. assert (EH : HEAD = 16) by reflexivity.
    destruct HF as [HF | [HF | HF]]; [| | exact (inFP_nil _ HF)];
      destruct (APART q m Hm) as [A | [A | A]]; lia.
  + (* the old kids / keys blocks *)
    destruct (pSh_inFP_hblocks _ _ HF) as (a & k & Hak & Hx).
    destruct (RB1 a k Hak) as (Hin1 & _ & Hk & _).
    assert (Hc : 0 < cap) by (destruct (pSh_old_in _ _ _ _ _ Hak) as [(_ & ->) | (_ & ->)]; lia).
    destruct (Nold Hc) as (N1 & N2).
    assert (NE : (q, m) <> (a - HEAD, k + HEAD)).
    { intros E. injection E as Eq _.
      destruct (pSh_old_in _ _ _ _ _ Hak) as [(-> & _) | (-> & _)];
        [apply N1 | apply N2]; rewrite Eq; reflexivity. }
    pose proof (sep_blocks tfibsegs B LAWS ly1 S1 W1 _ md1 q m (a - HEAD) (k + HEAD) HAR1 Hm Hin1 NE) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
  + (* fuzz/alloc.c's statics: image bytes; a live block lies below 0x10000 or past fs's image *)
    pose proof (FSW_rd.fsw_ablock_off_img B ly1 S1 W1 _ md1 q m HAR1 Hm) as L. unfold FS_IMG_END in L.
    unfold FS_PSTAT_FP in HF. rewrite !inFP_cons in HF.
    destruct HF as [HF | [HF | [HF | [HF | HF]]]]; [lia | lia | lia | lia | exact (inFP_nil _ HF)].
Qed.

(* ---- pSh_fresh_after_grow: grow's two new blocks were not live before it. From grow's post Permutation
   (ablocks3 ++ rd_hblocks Dold) (ablocks1 ++ rd_hblocks Dnew): a new block is in rd_hblocks Dnew, not in rd_hblocks
   Dold (its size differs: cap' = cap2 cap), and ablocks3 holds it at most once ---- *)
Lemma pSh_fresh_after_grow :
forall ly1 S1 ly3 S3 (W3 : world tfibsegs) mx3 md3 n cap kids keys k' y' cap' Dold Dnew U Ug,
  AR tfibsegs B ly3 S3 W3 mx3 md3 ->
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  Permutation (ablocks B ly3 S3 ++ rd_hblocks Dold) (ablocks B ly1 S1 ++ rd_hblocks Dnew) ->
  n = cap -> ~ In (k' - HEAD, 56 * cap' + HEAD) (ablocks B ly1 S1) /\
             ~ In (y' - HEAD, 8 * cap' + HEAD) (ablocks B ly1 S1).
Proof.
intros ly1 S1 ly3 S3 W3 mx3 md3 n cap kids keys k' y' cap' Dold Dnew U Ug HAR3 G P Hn.
destruct G as [(Hlt & _) | (_ & Ec & EDo & _ & _ & _ & _ & EDn & _)]; [lia|].
pose proof (pSh_ablocks_nodup ly3 S3 W3 mx3 md3 HAR3) as ND.
assert (EHn : rd_hblocks Dnew = [(k' - HEAD, 56 * cap' + HEAD); (y' - HEAD, 8 * cap' + HEAD)])
  by (rewrite EDn; reflexivity).
assert (HDo : forall x, In x (rd_hblocks Dold) -> cap <> 0 /\ cap' = 2 * cap /\
  (x = (kids - HEAD, 56 * cap + HEAD) \/ x = (keys - HEAD, 8 * cap + HEAD))).
{ intros x Hx. rewrite EDo in Hx. destruct (Z.eq_dec cap 0) as [-> | Hc].
  - rewrite pSh_blk_0 in Hx. destruct Hx.
  - rewrite (pSh_blk_ne0 kids keys cap Hc) in Hx. split; [exact Hc|]. split.
    + rewrite Ec. unfold ReaderRes.cap2. destruct (Z.eqb_spec cap 0); [lia | reflexivity].
    + destruct Hx as [<- | [<- | []]]; [left | right]; reflexivity. }
split; intros Hin.
- refine (pSh_perm_fresh _ _ _ _ _ ND P _ _ Hin).
  + intros Hx. destruct (HDo _ Hx) as (Hc & Ec2 & [E | E]); injection E as _ E2; unfold HEAD in E2; lia.
  + rewrite EHn. left. reflexivity.
- refine (pSh_perm_fresh _ _ _ _ _ ND P _ _ Hin).
  + intros Hx. destruct (HDo _ Hx) as (Hc & Ec2 & [E | E]); injection E as _ E2; unfold HEAD in E2; lia.
  + rewrite EHn. right. left. reflexivity.
Qed.

(* ---- 4. pSh_cstr_U_after_grow: each head of U' is in U or avoids the key string [k, k + |kname| + 1) ---- *)
(* a live block's head (c - HEAD, HEAD) avoids a run of image bytes *)
Lemma pSh_img_apart : forall ly S (W : world tfibsegs) mx md c M k len,
  AR tfibsegs B ly S W mx md -> In (c - HEAD, M) (ablocks B ly S) -> 16 <= req_size M -> 0 <= len ->
  (forall a, k <= a < k + len + 1 -> in_img tfibsegs a) ->
  c <= k \/ k + len + 1 <= c - HEAD.
Proof.
intros ly S W mx md c M k len HAR Hin HM Hlen Himg.
destruct (Z_le_gt_dec c k) as [L | L]; [left; exact L|].
destruct (Z_le_gt_dec (k + len + 1) (c - HEAD)) as [L2 | L2]; [right; exact L2|]. exfalso.
assert (Hx1 : k <= Z.max k (c - HEAD) < k + len + 1) by (unfold HEAD in *; lia).
assert (Hx2 : c - HEAD <= Z.max k (c - HEAD) < c - HEAD + req_size M) by (unfold HEAD in *; lia).
exact (proj2 (al_client_img tfibsegs B LAWS ly S W mx md (Z.max k (c - HEAD)) HAR
  (or_introl (ex_intro _ (c - HEAD) (ex_intro _ M (conj Hin Hx2))))) (Himg _ Hx1)).
Qed.
(* a block (c - HEAD, M) live after grow and not before it: its head avoids the key string the caller keeps. Block
   arm: the string's block survives grow (its byte k is off FPg) and differs from the fresh block, so the two are
   disjoint. Table arms: the string is image bytes, the head is not *)
Lemma pSh_newhead_apart :
forall ly1 S1 U ly3 S3 (W3 : world tfibsegs) mx3 md3 (FPg : list (Z * Z)) c M k kname,
  AR tfibsegs B ly3 S3 W3 mx3 md3 ->
  In (c - HEAD, M) (ablocks B ly3 S3) -> ~ In (c - HEAD, M) (ablocks B ly1 S1) -> 16 <= req_size M ->
  cstr_kept B ly1 S1 U k kname -> ~ inFP FPg k ->
  (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn -> ~ inFP FPg x ->
     In (p, nn) (ablocks B ly3 S3)) ->
  c <= k \/ k + Z.of_nat (length kname) + 1 <= c - HEAD.
Proof.
intros ly1 S1 U ly3 S3 W3 mx3 md3 FPg c M k kname HAR3 Hn3 Hn1 HM Hk HkF SURV.
assert (Hl : 0 <= Z.of_nat (length kname)) by lia.
destruct Hk as [(b & m & Hb & Hbk & Hkm & _) | [Htbl | (ps & Hps & ->)]].
- assert (Hm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hx : b <= k < b + req_size m) by lia.
  pose proof (SURV b m k Hb Hx HkF) as Hb3.
  assert (NE : (b, m) <> (c - HEAD, M)) by (intros E; rewrite E in Hb; exact (Hn1 Hb)).
  pose proof (sep_blocks tfibsegs B LAWS ly3 S3 W3 mx3 md3 b m (c - HEAD) M HAR3 Hb3 Hn3 NE) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. unfold HEAD in *. lia.
- apply (pSh_img_apart ly3 S3 W3 mx3 md3 c M k _ HAR3 Hn3 HM Hl).
  intros a Ha. exact (FSW_strkit.fs_ro_strs_img k kname a Htbl Ha).
- apply (pSh_img_apart ly3 S3 W3 mx3 md3 c M k _ HAR3 Hn3 HM Hl).
  intros a Ha. exact (FSW_strkit.fs_sn_fmts_img k ps a Hps Ha).
Qed.

Lemma pSh_cstr_U_after_grow :
forall ly1 S1 U ly3 S3 Ug (W3 : world tfibsegs) mem3 md3 (FPg : list (Z * Z))
  n cap kids keys k' y' cap' Dold Dnew k kname,
  ARU tfibsegs B ly3 S3 Ug W3 mem3 md3 ->
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  cstr_kept B ly1 S1 U k kname ->
  (forall a, k <= a < k + Z.of_nat (length kname) + 8 -> ~ inFP FPg a) ->
  (n = cap -> ~ In (k' - HEAD, 56 * cap' + HEAD) (ablocks B ly1 S1) /\
              ~ In (y' - HEAD, 8 * cap' + HEAD) (ablocks B ly1 S1)) ->
  (forall p nn x, In (p, nn) (ablocks B ly1 S1) -> p <= x < p + req_size nn -> ~ inFP FPg x ->
     In (p, nn) (ablocks B ly3 S3)) ->
  forall r, In r Ug -> In r U \/ fst r + snd r <= k \/ k + Z.of_nat (length kname) + 1 <= fst r.
Proof.
intros ly1 S1 U ly3 S3 Ug W3 mem3 md3 FPg n cap kids keys k' y' cap' Dold Dnew k kname
  HU3 G RB3 Hk HkF Hfr SURV r Hr.
pose proof HU3 as (HAR3 & _).
pose proof G as G'.
destruct G' as [(_ & _ & _ & _ & _ & _ & EUg) | (Hn & Ec & _)].
- left. rewrite <- EUg. exact Hr.
- assert (Hc' : cap' <> 0) by (rewrite Ec; unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
  rewrite (pSh_blk_ne0 k' y' cap' Hc') in RB3.
  destruct (Hfr Hn) as (F1 & F2).
  assert (Hkk : k <= k < k + Z.of_nat (length kname) + 8) by lia.
  pose proof (HkF k Hkk) as HkF0.
  destruct (pSh_ug_sub _ _ _ _ _ _ _ _ _ _ _ G r Hr) as [H | [-> | ->]]; [left; exact H | right | right].
  + destruct (RB3 k' (56 * cap') (or_introl eq_refl)) as (Hin3 & _ & Hpos & _).
    assert (HM : 16 <= req_size (56 * cap' + HEAD))
      by (unfold req_size, HEAD; destruct (Z.eqb_spec (56 * cap' + 16) 0); lia).
    destruct (pSh_newhead_apart ly1 S1 U ly3 S3 W3 _ md3 FPg k' (56 * cap' + HEAD) k kname
      HAR3 Hin3 F1 HM Hk HkF0 SURV) as [L | L]; cbn [fst snd]; unfold HEAD in *; lia.
  + destruct (RB3 y' (8 * cap') (or_intror (or_introl eq_refl))) as (Hin3 & _ & Hpos & _).
    assert (HM : 16 <= req_size (8 * cap' + HEAD))
      by (unfold req_size, HEAD; destruct (Z.eqb_spec (8 * cap' + 16) 0); lia).
    destruct (pSh_newhead_apart ly1 S1 U ly3 S3 W3 _ md3 FPg y' (8 * cap' + HEAD) k kname
      HAR3 Hin3 F2 HM Hk HkF0 SURV) as [L | L]; cbn [fst snd]; unfold HEAD in *; lia.
Qed.
End h.
