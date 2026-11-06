(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 234 of its 303 lines of code are new or changed and 709 lines of the source are left out. *)
(* fuzz_preset, image A: the generic walk layer proved in the S10 lane, in one file other walks can cite without merging
   that lane's branch (a merge of it drags the PRH_Base.v / PRH_FnTx.v / PRH_Img.v into conflict).
   Rule 24: no function is proved here. Nothing new is stated: every declaration is MOVED.
   ORIGIN. Each declaration below is moved BY PATH, CHARACTER FOR CHARACTER (statement, proof and the comment above it),
   from the S10 lane, branch origin/cold/h-hpreset-7-walk-S10 at commit 9c35e29a72ce382785e1fc17ea781fa51fea6ec8
   (read with `git show 9c35e29a72c:proofs/omx-clap-core/fuzz_preset/lib/A/Prog/<file>`):
     lib/A/Prog/S10TxKit.v     blob 25f898edb9f8c51a28d23c9084825466d4552c17
       :33-112   s10_pairwise_perm, s10_zdisjoint_sym, s10_rdword_some, s10_chain_ex_n, s10_chain_of_present,
                 s10_aview_byte
       :255-266  s10_fabortW_mono (in S10TxKit's Section c / d: the same Context, B, ARx and SK as there)
     lib/A/Prog/S10TxString.v  blob 501ed97b5cc94ed629adbc99b247fc12d5b26167
       :107-114  s10s_nth_all_regs, cur_atoms, xr
       :127-276  its Section d: TE, te_env, te_entry, te_cur, te_more, te_more_lt, cur_atoms_nth, te_regs_ok,
                 ts_st_ok, ts_bv_some, ts_rok, ts_chunk, ts_aview_range, ts_rdword_range, ts_land_m32, ts_region_nth,
                 ts_low_byte_mod, ts_field, ts_U_atom_mod
       :539-547, :560-579, :582-590  ts_keep, ts_add0_word, ts_reg_kept, ts_reg_kept_c, ts_val_mem_rd32 (from its
                 Section g, where the entry registers are the Variable regs; Section g below has the same Variable, so
                 the closed statements quantify regs first, as S10's do)
   Section headers: S10TxString's Section d keeps here only the four notations its lemmas use (PA, SEGS, VAL, BASE);
   its PL / SIGMA / RLO / RHI / PST lines are used by none of them, and PST would Require PRH_Img.
   S10's copies are to be DELETED once S10 re-points S10TxKit.v and S10TxString.v at this file. That is for S10's owner
   on resume (the lane is paused; nothing in S10's files is changed here).
   IMAGE. The TE section is bound to image A's listing instance (S10TxString.v:118 `PA := (PI_prog_A)`, :130
   `@Eimg _ A_prog_listing PA`); that is why this file lives in lib/A/Prog (the PRW_* walk-kit convention) and not in
   lib/Reusable, which Requires nothing from lib/A. The S10TxKit pieces are image-generic.
   SET. Built on K0 walkkit 2e154b9c0ce6 + the engine fold origin/cold/c-omx-alloc-preset-s1 63997a07aa6, by path:
   lib/Reusable/YCbqG.v blob 83da015952be (= cold/h-hpreset-7-walks-new a14d426ce3f1) and lib/A/Img0.v / Listing_prog.v
   / PAImg_prog.v (image A asan d83eb25d). This file's 204-file closure differs from S10's tree (9c35e29a72c) only in
   PRH_Base.v, YCbqG.v, Listing_prog.v and PAImg_prog.v (S10 has listing v4), and from h-w6u-rep's crs2 tree
   (99b1377a9e8) only in PRH_Base.v and YCbqG.v. Of those, the moved pieces cite only PRH_Base's fabortW (the same text
   in all three) and the listing's names PI_prog_A / A_prog_listing.
   STAYED IN S10 (not moved): tx_string's own functional model, pcs, frame and entry segments (S10TxString.v :49-105,
   :322-337, :401-537, :549-559, :593-655); its Admitted segment lemmas (:659-761) and what rests on them (ts_loop
   :721, tx_string_holds :765); S10TxKit's tx_put buffer lemmas prhtx_grow_refl / prhtx_grow_trans / prhtx_call_fp
   (:121-186, over the Tx part's PRH_FnTx predicates); and S10TxKit's call rules s10_call_or / s10_call_orW / s10_tail_orW
   (:194-249, :268-400), whose proofs do NOT build on this set, even in S10TxKit's own Require block with the Section's
   LAWS rebound for hl: the journal's ajournal_x_sub takes fp_sub_x, whose last case is `sp0 - STK <= a < sp0`, while
   their HF gives `alloc_ceiling <= a /\ ..`, so `exact HF` fails at S10TxKit.v:243 / :325 / :387 (cb build
   20261029T053207Z on this branch's clone). No frame_alloc or shadow-poke lemma is CLOSED in either file: tx_string's
   frame_alloc_0 step (ts_A) and frame header / shadow stretch (ts_at_B) are Admitted, and the frame-class-0 contract
   (ASM0, OWNLOW, SMX, ASFX, FFLX, SFX) is Section hypotheses there.
   Numerals: 32 / 64 / 240 are the engine's atom bands (DERIVED: A_TEXT = 240, YP0b.v); 5 / 8 / 64 / 256 and 2 ^ 64 are
   bit widths and byte ranges (WORD); 8 / 16 are word size and frame-pointer slots, 32 in ts_land_m32 is the
   `andi sp, sp, -32` realignment, 4096 is fpchain's return-address floor (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- from S10TxKit.v (blob 25f898edb9f8) ---- *)

(* pairwise R is invariant under permutation when R is symmetric (zdisjoint is) *)
Lemma s10_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.

Lemma s10_zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

(* ---- a frame-pointer chain exists wherever the words it reads are present (S10put's tp_rdword_some / tp_chain_ex_n /
   tp_chain_ex, S10TxPut.v, moved here verbatim so tx_put's and tx_string's walks cite one copy; the Tx part's ruling on
   blob 807e61a3900b: afn_pre_x asks for SOME chain, and it exists when [bp - 16, top) is present) ---- *)
Lemma s10_rdword_some : forall (rd : reader) a,
  (forall i, 0 <= i < 8 -> rd (a + i) <> None) ->
  (forall x v, rd x = Some v -> 0 <= v < 256) ->
  exists v, rdword rd a = Some v /\ 0 <= v.
Proof.
intros rd a Hp Hb. unfold rdword.
assert (H0 : rd a <> None) by (replace a with (a + 0) by lia; apply Hp; lia).
destruct (rd a) as [b0|] eqn:E0; [|exfalso; exact (H0 eq_refl)].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (Hp 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (Hp 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (Hp 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (Hp 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (Hp 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (Hp 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (Hp 7 ltac:(lia) E7)].
eexists. split; [reflexivity|].
pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.

Lemma s10_chain_ex_n : forall (rd : reader) (top : Z),
  (forall x v, rd x = Some v -> 0 <= v < 256) ->
  forall (n : nat) (bp : Z), top - bp <= Z.of_nat n -> bp < top -> bp mod 8 = 0 ->
  (forall a, bp - 16 <= a < top -> rd a <> None) ->
  exists ch, fpchain (rdword rd) bp top ch.
Proof.
intros rd top Hb n. induction n as [|n IH]; intros bp Hn Hbt Hal Hpres.
- exfalso. lia.
- destruct (s10_rdword_some rd (bp - 8) ltac:(intros i Hi; apply Hpres; lia) Hb) as (ra & Hra & Hra0).
  destruct (Z_lt_ge_dec ra 4096) as [Hlt | Hge].
  + exists []. cbn [fpchain]. exists ra. split; [exact Hra | lia].
  + destruct (s10_rdword_some rd (bp - 16) ltac:(intros i Hi; apply Hpres; lia) Hb) as (nfp & Hnfp & Hnfp0).
    destruct (bad_next bp top nfp) eqn:Ebn.
    * exists [(bp, ra, nfp)]. cbn [fpchain]. rewrite Ebn.
      split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra|]. split; [exact Hnfp|]. split; [lia | reflexivity].
    * unfold bad_next in Ebn.
      apply orb_false_iff in Ebn as [Ebn E3]. apply orb_false_iff in Ebn as [E1 E2].
      apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply negb_false_iff in E3. apply Z.eqb_eq in E3.
      destruct (IH nfp ltac:(lia) ltac:(lia) E3 ltac:(intros a Ha; apply Hpres; lia)) as (ch & Hch).
      exists ((bp, ra, nfp) :: ch). cbn [fpchain]. unfold bad_next.
      rewrite (proj2 (Z.leb_gt nfp bp) E1), (proj2 (Z.leb_gt (top - 16) nfp) E2).
      rewrite (proj2 (Z.eqb_eq (nfp mod 8) 0) E3). cbn [orb negb].
      split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra|]. split; [exact Hnfp|]. split; [lia | exact Hch].
Qed.

Lemma s10_chain_of_present : forall (rd : reader) (top bp : Z),
  (forall x v, rd x = Some v -> 0 <= v < 256) -> bp < top -> bp mod 8 = 0 ->
  (forall a, bp - 16 <= a < top -> rd a <> None) ->
  exists ch, fpchain (rdword rd) bp top ch.
Proof.
intros rd top bp Hb Hbt Hal Hpres.
apply (s10_chain_ex_n rd top Hb (Z.to_nat (top - bp)) bp ltac:(lia) Hbt Hal Hpres).
Qed.

(* the bytes a reader of an image's view returns are bytes (S10put's tp_aview_byte, over any segment list) *)
Lemma s10_aview_byte : forall (sg : list Segment) (H : word -> bool) mem x v, aview sg H mem x = Some v -> 0 <= v < 256.
Proof.
intros sg H mem x v E. unfold aview in E.
destruct (mbyte sg (mrestrict H mem) x) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

Section d.
Variable SK : YI16.sink_head.

(* the abort tail's evidence weakens pointwise (e.g. a callee's prhtx_refused at its larger free tail, lowered to the
   caller's by ROOM_cf_k's monotonicity) *)
Lemma s10_fabortW_mono : forall F STK d FP regs ly S Hp W mem md
  (E E' : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  (forall ly' S' Hp' W'' regs' mem' md', E ly' S' Hp' W'' regs' mem' md' -> E' ly' S' Hp' W'' regs' mem' md') ->
  fabortW B ARx SK F STK d FP regs ly S Hp W mem md E W' c' ->
  fabortW B ARx SK F STK d FP regs ly S Hp W mem md E' W' c'.
Proof.
intros F STK d FP regs ly S Hp W mem md E E' W' c' HEE (fx' & ly' & S' & Hp' & regs' & mem' & md' & own & k & Hc & HJ & HW & HE).
exists fx', ly', S', Hp', regs', mem', md', own, k. split; [exact Hc|]. split; [exact HJ|]. split; [exact HW|].
exact (HEE _ _ _ _ _ _ _ HE).
Qed.
End d.

End c.

(* ======================================================================================================== *)
(* ---- from S10TxString.v (blob 501ed97b5cc9) ---- *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- registers and the segment environment ---- *)
Lemma s10s_nth_all_regs : forall k, (k < 32)%nat -> nth k all_regs 0%bv = Z_to_bv 5 (Z.of_nat k).
Proof. intros k Hk. do 32 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia. Qed.

(* the atoms 32-63 hold the current registers *)
Definition cur_atoms : list sv := SLit 0 :: map (fun i => SOff (32 + i) 0) (seq 1 31).
Definition xr (r : nat) : nat := (32 + r)%nat.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

(* the segment environment: entry registers, current registers, extras *)
Definition TE (regs0 regsc : bvmap 5 word) (more : list word) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs0 (map (getr regsc) all_regs ++ more)).

Lemma te_env : forall regs0 regsc more, img_env VAL A_LIM (TE regs0 regsc more).
Proof. intros. unfold TE. apply Eimg_env. Qed.
Lemma te_entry : forall regs0 regsc more (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (TE regs0 regsc more) n = getr regs0 r.
Proof.
intros regs0 regsc more r n Hn. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.
Lemma te_cur : forall regs0 regsc more (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew (TE regs0 regsc more) (32 + k) = getr regsc r.
Proof.
intros regs0 regsc more r k Hk. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsc 0%bv)) by (rewrite length_map; cbn; lia).
rewrite map_nth. rewrite s10s_nth_all_regs by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Hk. apply Z.mod_small. lia.
Qed.
Lemma te_more : forall regs0 regsc more j, ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0) \/ (240 <= 64 + j)%nat.
Proof.
intros regs0 regsc more j. destruct (Nat.lt_ge_cases (64 + j) 240) as [H|H]; [left|right; exact H].
unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia). replace (64 + j)%nat with (32 + (32 + j))%nat by lia.
rewrite ew_Ereg_extra. rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn [length all_regs].
f_equal. lia.
Qed.
Lemma te_more_lt : forall regs0 regsc more j, (64 + j < 240)%nat -> ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0).
Proof. intros regs0 regsc more j Hj. destruct (te_more regs0 regsc more j) as [H|H]; [exact H | lia]. Qed.

Lemma cur_atoms_nth : forall k, (1 <= k < 32)%nat -> nth k cur_atoms (SLit 0) = SOff (32 + k) 0.
Proof.
intros k Hk. destruct k as [|k']; [lia|]. unfold cur_atoms. cbn [nth].
pose proof (map_nth (fun i : nat => SOff (32 + i) 0) (seq 1 31) 0%nat k') as M. cbv beta in M.
rewrite (nth_indep _ (SLit 0) (SOff (32 + 0) 0)) by (rewrite length_map, length_seq; lia).
rewrite M, seq_nth by lia. first [reflexivity | f_equal; lia].
Qed.
Lemma te_regs_ok : forall regs0 regsc more, regs_ok (TE regs0 regsc more) cur_atoms regsc.
Proof.
intros regs0 regsc more r. unfold sr_get. pose proof (u5_range r) as Hr.
destruct (bv_eqb r 0) eqn:Hz.
- apply bv_eqb_eq in Hz. subst r. rewrite getr_zero. reflexivity.
- assert (Hne : bv_unsigned r <> 0).
  { intros H0. assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in Hz. discriminate. }
  unfold ridx. rewrite cur_atoms_nth by lia. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (te_cur regs0 regsc more r (Z.to_nat (bv_unsigned r))) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- building a segment's symbolic state from concrete facts ---- *)
Lemma ts_st_ok : forall regs0 regsc more pc sr rs G (Wc : world SEGS) memc,
  regs_ok (TE regs0 regsc more) sr regsc -> regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (TE regs0 regsc more) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (TE regs0 regsc more) rs -> facts_ok (TE regs0 regsc more) G ->
  st_ok_pi SEGS VAL (TE regs0 regsc more) (mkSS pc sr rs None G)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; assumption. Qed.

Lemma ts_bv_some : forall E n, base_val E (Some n) = bv_unsigned (ew E n).
Proof. reflexivity. Qed.

Lemma ts_rok : forall E m n base lo hi wlo whi cs, bv_unsigned (ew E n) = base -> 0 <= base + lo -> base + hi <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> YP09.writable_at SEGS m (base + o)) -> Forall (YP09.chunk_ok SEGS E m base) cs ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E m n base lo hi wlo whi cs Hb H1 H2 H3 H4. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb. auto.
Qed.

Lemma ts_chunk : forall E m base off (n : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) ->
  (Z.of_N n <= 8) -> val_mem SEGS m (base + off) (N.to_nat n) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)).
Proof. intros. eapply chunk_ok_val; eassumption. Qed.

Lemma ts_aview_range : forall H mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma ts_rdword_range : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply ts_aview_range in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.

(* `andi sp, sp, -32` on a 64-bit value *)
Lemma ts_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
replace (2 ^ 64 - 32) with (Z.shiftl (Z.ones 59) 5) by reflexivity.
replace (x / 32 * 32) with (Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite !Z.shiftl_spec by lia.
destruct (Z_lt_le_dec i 5) as [Hl|Hl].
- rewrite (Z.testbit_neg_r (Z.ones 59) (i - 5)), (Z.testbit_neg_r (Z.shiftr x 5) (i - 5)) by lia. apply andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z_lt_le_dec i 64) as [H64|H64].
  + rewrite Z.ones_spec_low by lia. apply andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. apply (Z.bits_above_log2 x i); [lia|]. destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
    apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

(* reading a region of a run's final state back as concrete bytes *)
Lemma ts_region_nth : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma ts_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ts_field : forall E m n b cs lo hi wlo whi od (w : N) e,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) (U E e mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as H. cbn [YP09.r_base base_val] in H. rewrite Hn in H.
intros k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z w) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (bb & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal. unfold U.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N w) < 2 ^ (8 * Z.of_nat (N.to_nat w))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply ts_low_byte_mod; [lia | exact Hk].
Qed.
Lemma ts_U_atom_mod : forall E n, U E (SOff n 0) mod 2 ^ 64 = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. lia.
Qed.

End d.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable regs : bvmap 5 word.

(* bytes a run did not write *)
Lemma ts_keep : forall (Wx : world SEGS) E rs mA mB (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H Wx) mA) (mrestrict (w_H Wx) mB) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a.
Proof.
intros Wx E rs mA mB P HF HP a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros H. exact (Hn (HP a H)).
Qed.
Lemma ts_add0_word : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w.
Proof. intros w. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
rewrite Z.add_0_r. unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range 64 w). Qed.
(* a register the segment did not write: its final value is the segment's start value *)
Lemma ts_reg_kept : forall regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok_pi SEGS VAL (TE regs regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regsc more ss H ms r r' HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma ts_reg_kept_c : forall regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok SEGS (TE regs regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regsc more ss H ms r r' HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.

Lemma ts_val_mem_rd32 : forall (H : word -> bool) m a v, rd32 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 4 v.
Proof.
intros H m a v Hr kk Hk. pose proof (Hr kk Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat kk)) as [b|] eqn:Em; [|discriminate].
cbn [option_map] in Hb. injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. transitivity (bv_wrap 8 (bv_unsigned b)).
- unfold bv_wrap. rewrite Z.mod_small; [reflexivity | exact (bv_unsigned_in_range 8 b)].
- f_equal. exact Hb.
Qed.

End g.
