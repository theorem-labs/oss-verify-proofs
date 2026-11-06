(* libreac/fuzz_boxreg: the per-operand lemmas that build the string premise of the strncmp contract
   (lib/A/Rt/StrncmpDef.v fm_cstr_ok, a Theorem Labs lane's cstr_ok FMH_Base.v:175 with the same 8 conjuncts) at boxreg's call
   sites. They are generic in segs and B (they use only AR and its laws), so the asan-ubsan build uses the same file
   (lib/B/Rt/StrncmpSiteB.v states the same lemmas over StrncmpDefB's names).
   The three kinds of operand the six call sites pass (fuzz_boxreg.c:182 / :266 / :394; RT-E3E4-PLAN.md, STRNCMP-PREP.md
   sections 5, 8, 10):
   - a NUL-terminated string inside a heap block of a primary size class (r->box[idx].name and r->box[i].name inside
     the 288-byte registry, read_name's malloc (n + 1) block): fm_cstr_ok_of_block. Every conjunct comes from AR:
     the block law (al_blocks) for the presence of the bytes and the lower bound, the chunk geometry (chunk_facts,
     region_in_prim) for `p + len + 8 <= alloc_ceiling` and amem_range (a primary chunk ends at least 2^31 below the
     ceiling), range_addressable_of_block / shadow_hull_vis_of_block for the shadow, and ar_blk_tail_vis
     (lib/A/Prog/BoxTailVis.v) for the rest of the NUL's aligned 8-byte word.
   - the "" global 0x20ce0 (a one-byte registered global of the read-only image): fm_cstr_ok_of_glob_empty, from the
     globals' shadow (ro_read_ok_glob, lib/A/Prog/BoxRo.v) and the image's bytes, which are always visible.
   - a string inside the class-3 fake frame (:182's prev): fm_cstr_ok_of_present, from presence of its bytes up to the
     next multiple of 8, the frame's bound below the ceiling and the shadow facts the entry walk carries.
   No operand is on the real machine stack (STRNCMP-PREP.md section 8: prev is in the fake frame, row 24's contract).
   The contract's two read-only premises are not built here; a call site cites lib/A/Rt/StrncmpView.v (a Theorem Labs lane,
   pa 4ac2a7b7a17): fm_rom_viewN_of_arodata (from the caller's arodata_okP) and fm_rom_viewO_of_AR (from AR and
   ro_owned_pinned).
   Names from lib/Lib and lib/A/Bz are not used here. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YM05 YCbq YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxTailVis BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import StrncmpDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* ---- the bytes ---- *)

(* a byte the world view shows is a 1-byte value of the restricted memory *)
Lemma val_mem_of_aview : forall H mem a c, aview segs H mem a = Some c -> 0 <= c < 256 ->
  val_mem segs (mrestrict H mem) a 1 c.
Proof.
  intros H mem a c Hv Hc k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
  assert (E : Z.shiftr (c mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256 = c)
    by (cbn [Z.of_nat]; rewrite Z.mul_0_r, Z.shiftr_0_r; rewrite !Z.mod_small; lia).
  match goal with |- context [Z_to_bv 8 ?e] =>
    change e with (Z.shiftr (c mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0) mod 256) end.
  rewrite E.
  unfold aview in Hv. destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
  injection Hv as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma fm_cstr_of_view : forall (W : world segs) mem p (l : list Z),
  Forall (fun c => 0 <= c < 256 /\ c <> 0) l ->
  (forall j, (j < length l + 1)%nat -> aview segs (w_H W) mem (p + Z.of_nat j) = Some (nth j (l ++ [0]) 0)) ->
  fm_cstr segs W mem p l.
Proof.
  intros W mem p l F Hv. split.
  - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    assert (R : 0 <= nth j (l ++ [0]) 0 < 256).
    { destruct (Nat.lt_ge_cases j (length l)) as [L|L].
      - rewrite app_nth1 by exact L. exact (proj1 (proj1 (Forall_forall _ _) F _ (nth_In l 0 L))).
      - rewrite app_nth2 by exact L. replace (j - length l)%nat with 0%nat by lia. cbn. lia. }
    split; [apply val_mem_of_aview; [apply Hv; lia | exact R] | exact R].
  - eapply Forall_impl; [|exact F]. intros c Hc. exact (proj2 Hc).
Qed.

(* a present byte is visible; an image byte is always visible *)
Lemma aview_of_present : forall H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
  intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma aview_of_rom : forall H mem a, seg_rom segs (Z_to_bv 64 a) <> None -> aview segs H mem a <> None.
Proof.
  intros H mem a Hr. unfold aview, mbyte.
  destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [discriminate|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [discriminate | contradiction].
Qed.

(* the NUL's aligned 8-byte word lies inside [q, q + round_up m 8) when q is a multiple of 8 and the NUL inside
   [q, q + m) *)
Lemma nul_word_in : forall q m z a, q mod 8 = 0 -> q <= z -> z < q + m ->
  z < a < z - z mod 8 + 8 -> a < q + round_up m 8.
Proof.
  intros q m z a Hq Hz1 Hz2 Ha. unfold round_up.
  assert (Ez : z - z mod 8 = q + 8 * ((z - q) / 8)).
  { pose proof (Z.div_mod (z - q) 8 ltac:(lia)) as D.
    assert (M : z mod 8 = (z - q) mod 8).
    { replace z with ((z - q) + q) at 1 by lia. rewrite Z.add_mod, Hq, Z.add_0_r, Z.mod_mod by lia. reflexivity. }
    lia. }
  assert (Hd : (z - q) / 8 + 1 <= (m + 8 - 1) / 8).
  { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le (z - q) 8 ltac:(lia)). lia. }
  pose proof (Z.mul_div_le (m + 8 - 1) 8 ltac:(lia)). nia.
Qed.

(* ---- operand kind 1: a heap block of a primary size class ---- *)

(* A primary block ends at least 2^31 below the ceiling, in high memory. *)
Lemma ar_blk_prim_bounds : forall ly S (W : world segs) mem md p n, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> from_primary n = true ->
  kHighMemBeg <= p /\ p + n + 2 ^ 31 <= ASAN_CEIL.
Proof.
  intros ly S W mem md p n (M & _) Hb Hfp.
  unfold ablocks, blocks in Hb. apply in_map_iff in Hb as ([u r] & Eb & Hb). cbn [fst snd] in Eb. injection Eb as Ep En.
  apply in_map_iff in Hb as (k & Ek & Hk). injection Ek as Eu Er. rewrite <- Eu in Ep. rewrite <- Er in En.
  apply filter_In in Hk as [Hk _].
  pose proof (chunk_facts B ly S _ k M Hk) as (IA & CE & _ & UA & RZb & _ & Hn & HX & G).
  rewrite <- Ep, UA. rewrite <- En.
  destruct (ck_beg k) as [|off|rr oo|cc qq] eqn:EB; try solve [destruct G].
  - cbv zeta in G. destruct G as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gal & Gm).
    pose proof (region_in_prim ly (prim_class off) (am_layout _ _ _ _ M) ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    assert (Hreq : ck_req k <= req_size (ck_req k)) by (unfold req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
    split; [lia|]. rewrite Gbase. lia.
  - destruct G as (_ & Hfp' & _). rewrite <- En in Hfp. congruence.
Qed.

Lemma fm_cstr_ok_of_block : forall ly S (W : world segs) mem md b m p (l : list Z),
  AR segs B ly S W mem md -> In (b, m) (ablocks B ly S) -> from_primary m = true ->
  b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  Forall (fun c => 0 <= c < 256 /\ c <> 0) l ->
  (forall j, (j < length l + 1)%nat -> aview segs (w_H W) mem (p + Z.of_nat j) = Some (nth j (l ++ [0]) 0)) ->
  fm_cstr_ok segs W mem p l.
Proof.
  intros ly S W mem md b m p l HAR Hin Hfp Hbp Hpe F Hv.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbia & Hbp' & _ & Hmax).
  destruct (ar_blk_prim_bounds ly S W mem md b m HAR Hin Hfp) as (Hhi & Hcl).
  assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hb8 : b mod 8 = 0).
  { apply Z.mod_divide in Hb16 as [t Ht]; [|lia]. rewrite Ht. replace (t * 16) with ((t * 2) * 8) by lia.
    apply Z.mod_mul. lia. }
  set (len := Z.of_nat (length l)) in *.
  split; [exact (fm_cstr_of_view W mem p l F Hv)|].
  split; [lia|]. split; [lia|]. split; [unfold MALLOC_MAX in Hmax; lia|].
  split; [apply amem_range_high; [lia | right; unfold kHighMemBeg in Hhi; lia | unfold ASAN_CEIL in Hcl; lia]|].
  split; [apply (range_addressable_of_block segs B LAWS ly S W mem md b m p (len + 1) HAR Hin); lia|].
  split; [apply (shadow_hull_vis_of_block segs B LAWS ly S W mem md b m p (len + 1) HAR Hin); lia|].
  intros a Ha.
  destruct (Z.lt_ge_cases a (b + m)) as [Lt|Ge].
  - apply aview_of_present. apply (proj1 (Hbp' a ltac:(rewrite Hrq; lia))).
  - apply (ar_blk_tail_vis segs B ly S W mem md b m a HAR Hin). split; [exact Ge|].
    apply (nul_word_in b m (p + len) a); [exact Hb8 | lia | lia | exact Ha].
Qed.

(* ---- operand kind 2: the empty string at a one-byte registered global of the read-only image ---- *)

Lemma fm_cstr_ok_of_glob_empty : forall G ly S (W : world segs) mem md q sz,
  AR segs B ly S W mem md -> globs_marked segs B G -> In (q, sz) G -> img_shadow_vis segs B ->
  1 <= sz -> IMG_LO + 64 <= q -> q + 1 + 64 <= IMG_HI -> 4096 <= q -> q + 8 <= 2147446784 ->
  aview segs (w_H W) mem q = Some 0 ->
  (forall a, q < a < q - q mod 8 + 8 -> seg_rom segs (Z_to_bv 64 a) <> None) ->
  fm_cstr_ok segs W mem q [].
Proof.
  intros G ly S W mem md q sz HAR HGM HZG HSV Hsz H1 H2 H3 H4 Hq0 Hrom.
  pose proof ASAN_CEIL_range as [CR _]. unfold ASAN_CEIL in CR.
  destruct (ro_read_ok_glob segs B G ly S W mem md q sz q 1 HGM HZG HSV HAR ltac:(lia) ltac:(lia) ltac:(lia) H1 H2)
    as (RA & SH).
  assert (CV : fm_cstr segs W mem q []).
  { apply (fm_cstr_of_view W mem q []); [apply Forall_nil|].
    intros j Hj. cbn [length] in Hj. replace j with 0%nat by lia. cbn [Z.of_nat nth app]. rewrite Z.add_0_r. exact Hq0. }
  unfold fm_cstr_ok. cbn [length Z.of_nat].
  split; [exact CV|].
  split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
  split; [apply amem_range_high; [lia | left; lia | lia]|].
  split; [lazymatch goal with |- range_addressable _ _ _ ?e => replace e with 1 by lia end; exact RA|].
  split; [lazymatch goal with |- shadow_hull_vis _ _ ?e => replace e with 1 by lia end; exact SH|].
  intros a Ha. apply aview_of_rom. apply Hrom. lia.
Qed.

(* ---- operand kind 3: a string whose bytes up to the next multiple of 8 are present (the fake frame) ---- *)

Lemma fm_cstr_ok_of_present : forall (W : world segs) mem p (l : list Z),
  Forall (fun c => 0 <= c < 256 /\ c <> 0) l ->
  (forall j, (j < length l + 1)%nat -> aview segs (w_H W) mem (p + Z.of_nat j) = Some (nth j (l ++ [0]) 0)) ->
  4096 <= p -> p + Z.of_nat (length l) + 8 <= ASAN_CEIL -> Z.of_nat (length l) + 1 < 2 ^ 32 ->
  amem_range p (Z.of_nat (length l) + 8) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length l) + 1) ->
  shadow_hull_vis (aview segs (w_H W) mem) p (Z.of_nat (length l) + 1) ->
  (forall a, p + Z.of_nat (length l) < a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     apresent (w_H W) mem a) ->
  fm_cstr_ok segs W mem p l.
Proof.
  intros W mem p l F Hv H1 H2 H3 H4 H5 H6 H7.
  split; [exact (fm_cstr_of_view W mem p l F Hv)|].
  do 6 (split; [assumption|]).
  intros a Ha. apply aview_of_present. apply H7. exact Ha.
Qed.

End c.
End b.

(* the assumptions, printed into the build log *)
Print Assumptions fm_cstr_ok_of_block.
Print Assumptions fm_cstr_ok_of_glob_empty.
Print Assumptions fm_cstr_ok_of_present.
