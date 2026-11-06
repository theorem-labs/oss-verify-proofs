(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths, module names and numbers changed; 5113 of its 5220 lines of code are new or changed and 407 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxValue.v, with its module paths and module names changed; 250 of its 368 lines of code are new or changed and 5102 lines of the source are left out. *)
(* Theorem Labs, 2026-10: the GENERIC transport lemmas of parse_items' image-B walk (moved out of
   lib/B/Prog/PItems_head.v on PItemsB's request, names and statements unchanged), shared by every segment lane:
   - the reader-agreement frame library: pi_agr / pi_agr_mono and the transport of val_mem, writable_at, rd_rw, garr8,
     rd_u64 / rd_u32, pj_hdrR, pj_cstrR, pj_itemsR / pj_memsR (monotone in the node predicate) and pj_nodeR (over its
     footprint pj_footR) - the R-form of plain lib/Prog/PjStruct.v pj_hdr_eq / pj_cstr_eq / pj_items_mono /
     pj_mems_mono / pj_node_frame; pi_aview_agr / pi_ra_agr (the shadow view); pi_frame_kept (PItems_defs.v's frame
     predicate over an agreement); pi_field / pi_region_nth (reading a field of a symbolic region);
   - image B's shadow address (x >> 3) + s10 as a symbolic value: pi_shx, pi_denot_shx / pi_denot_shx', hd_alu_shx
     (its normal form after a run), and the tactic prregx (a register read without the normalisation);
   - the ledger and placement facts at image B over AR_laws_x: cl_at_bounds (the node prhReader_at places is inside
     the address space), cl_ledger_agr / cl_ledger_rdeq (prh_ledger over a reader agreement / an equal reader),
     cl_D_bounds (a harness block lies below the allocation ceiling). The ledger carries the f97c kit's seven cells
     (prh_glob .. ran most own, PRH_Base.v); a proof here reads it ONLY through PRH_Base's named projections
     (Section ledger_proj), never by the position of a conjunct.
   No segment pre and no pi_ent is mentioned here. Numerals: 4, 8, 16, 56 LENGTH; 4096, 2 ^ 47, 2 ^ 64 DERIVED;
   no ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YC1fP YC1fPx YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================================================================================== *)
(* the shadow address of the byte at x as image B computes it, (x >> 3) + s10, with s10 = SHADOW_OFF (atom 26) *)
Definition pi_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 26 0).

Lemma pi_denot_shx : forall E x sb v, sv_denot E x = Z_to_bv 64 v -> ew E 26 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 -> sv_denot E (pi_shx x) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E x sb v Hx H26 Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (pi_shx x))). f_equal.
change (U E (pi_shx x) = sb + v / 8). unfold pi_shx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, H26.
assert (Ux : U E x = v) by (unfold U; rewrite Hx; apply unsigned_lit_small; lia). rewrite Ux.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ================================================================================================== *)
(* THE FRAME LIBRARY of the reader predicates (PRH_Reader.v), over two readers that agree on a set F of addresses:
   the R-form of the plain lib/Prog/PjStruct.v pj_hdr_eq / pj_cstr_eq / pj_items_mono / pj_mems_mono / pj_node_frame,
   restated over val_mem / garr8 / writable_at. *)
(* the same, with pi_shx unfolded, as the run leaves it *)
Lemma pi_denot_shx' : forall E n cst sb v, sv_denot E (SOff n cst) = Z_to_bv 64 v -> ew E 26 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n cst) (SLit 3)) (SOff 26 0)) = Z_to_bv 64 (sb + v / 8).
Proof. intros E n cst sb v. exact (pi_denot_shx E (SOff n cst) sb v). Qed.

(* the shadow address as the run leaves it in a register (prreg's normal form) *)
Lemma hd_alu_shx : forall (wv sb : word) v s, wv = Z_to_bv 64 v -> sb = Z_to_bv 64 s ->
  0 <= v < 2 ^ 63 -> 0 <= s < 2 ^ 32 ->
  alu64 ALU_ADD (alu64 ALU_SRL wv (Z_to_bv 64 3)) sb = Z_to_bv 64 (s + v / 8).
Proof.
intros wv sb v s -> -> Hv Hs.
rewrite !zalu64_sound. unfold zalu64. cbn [zalu_raw].
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id s) by (unfold M64; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite (zcanon_id (v / 8)) by (unfold M64; lia).
f_equal. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* prreg without the normalisation, for a register the run leaves as a shadow address *)
Ltac prregx HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Section fr.
Variable segs : list Segment.

Definition pi_agr (F : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, F a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).

Lemma pi_agr_mono : forall (F G : Z -> Prop) m m', pi_agr F m m' -> (forall a, G a -> F a) -> pi_agr G m m'.
Proof. intros F G m m' H HGF a Ha. exact (H a (HGF a Ha)). Qed.

Lemma pi_val_agr : forall F m m' a n v, pi_agr F m m' -> (forall k, (k < n)%nat -> F (a + Z.of_nat k)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros F m m' a n v HA HF HV k Hk. unfold mbyte. rewrite (HA _ (HF k Hk)). exact (HV k Hk). Qed.

Lemma pi_wr_agr : forall F m m' a, pi_agr F m m' -> F a -> writable_at segs m a -> writable_at segs m' a.
Proof. intros F m m' a HA Ha H. unfold writable_at, wview in *. rewrite (HA a Ha). exact H. Qed.

Lemma pi_rw_agr : forall F m m' a n, pi_agr F m m' -> (forall x, a <= x < a + n -> F x) ->
  rd_rw segs m a n -> rd_rw segs m' a n.
Proof. intros F m m' a n HA HF H x Hx. apply (pi_wr_agr F m m' x HA (HF x Hx)). exact (H x Hx). Qed.

Lemma pi_garr8_agr : forall F m m' a l, pi_agr F m m' -> (forall x, a <= x < a + Z.of_nat (length l) -> F x) ->
  garr8 segs m a l -> garr8 segs m' a l.
Proof.
intros F m m' a l HA HF H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pi_val_agr F m m'); [exact HA | | exact Hv]. intros k Hk. apply HF. lia.
Qed.

Lemma pi_u64_agr : forall F m m' a v, pi_agr F m m' -> (forall x, a <= x < a + 8 -> F x) ->
  rd_u64 segs m a v -> rd_u64 segs m' a v.
Proof.
intros F m m' a v HA HF [H0 H]. split; [exact H0|]. apply (pi_val_agr F m m'); [exact HA | | exact H].
intros k Hk. apply HF. lia.
Qed.

Lemma pi_u32_agr : forall F m m' a v, pi_agr F m m' -> (forall x, a <= x < a + 4 -> F x) ->
  rd_u32 segs m a v -> rd_u32 segs m' a v.
Proof.
intros F m m' a v HA HF [H0 H]. split; [exact H0|]. apply (pi_val_agr F m m'); [exact HA | | exact H].
intros k Hk. apply HF. lia.
Qed.

Lemma pi_hdrR_agr : forall F m m' p ty num str kids keys n cap, pi_agr F m m' -> (forall x, p <= x < p + 56 -> F x) ->
  pj_hdrR segs m p ty num str kids keys n cap -> pj_hdrR segs m' p ty num str kids keys n cap.
Proof.
intros F m m' p ty num str kids keys n cap HA HF ((Hal & Hrw) & T & N & S & K & Y & C & P).
split; [split; [exact Hal | apply (pi_rw_agr F m m'); [exact HA | exact HF | exact Hrw]]|].
split; [apply (pi_u32_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact T]|].
split; [apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact N]|].
split; [apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact S]|].
split; [apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact K]|].
split; [apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact Y]|].
split; [apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact C]|].
apply (pi_u64_agr F m m'); [exact HA | intros x Hx; apply HF; lia | exact P].
Qed.

Lemma pi_cstrR_agr : forall F m m' lblk a k s, pi_agr F m m' -> (forall x, a <= x < a + k -> F x) ->
  pj_cstrR segs m lblk a k s -> pj_cstrR segs m' lblk a k s.
Proof.
intros F m m' lblk a k s HA HF (Hl & Hk & Hn & Hf & Hg). split; [exact Hl|]. split; [exact Hk|]. split; [exact Hn|].
split; [exact Hf|].
apply (pi_garr8_agr F m m'); [exact HA | | exact Hg]. intros x Hx. apply HF. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma pi_itemsR_mono : forall (P Q : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall i u D1, (i < length l)%nat -> In u l -> incl D1 D ->
     P (a + 56 * Z.of_nat i) u D1 -> Q (a + 56 * Z.of_nat i) u D1) ->
  pj_itemsR P a l D -> pj_itemsR Q a l D.
Proof.
intros P Q l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *.
- exact Hl.
- destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2. split; [exact E|]. split.
  + specialize (H 0%nat u D1). replace (a + 56 * Z.of_nat 0) with a in H by lia.
    apply H; [cbn; lia | left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact HP].
  + apply (IH (a + 56) D2); [|exact HR].
    intros i v D3 Hi Hv Hinc HP3.
    replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
    apply H; [cbn; lia | right; exact Hv | subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb | exact HP3].
Qed.

Lemma pi_memsR_mono : forall m m' lblk (P Q : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall i nm u x k D1, (i < length l)%nat -> In (nm, u) l -> In (x, k) D -> incl D1 D ->
     rd_u64 segs m (ka + 8 * Z.of_nat i) x -> pj_cstrR segs m lblk x k nm -> P (a + 56 * Z.of_nat i) u D1 ->
     rd_u64 segs m' (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m' lblk x k nm /\ Q (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m' lblk Q a ka l D.
Proof.
intros m m' lblk P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [pj_memsR] in *.
- exact Hl.
- destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
  assert (G : rd_u64 segs m' ka x /\ pj_cstrR segs m' lblk x k nm /\ Q a u D1).
  { specialize (H 0%nat nm u x k D1).
    replace (ka + 8 * Z.of_nat 0) with ka in H by lia. replace (a + 56 * Z.of_nat 0) with a in H by lia.
    apply H; [cbn; lia | left; reflexivity | subst D; left; reflexivity
             | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hx | exact Hc | exact HP]. }
  destruct G as (Hx' & Hc' & HQ).
  exists x, k, D1, D2. split; [exact E|]. split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HQ|].
  apply (IH (a + 56) (ka + 8) D2); [|exact HR].
  intros i nm' v x' k' D3 Hi Hv Hxk Hinc Hx3 Hc3 HP3.
  replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx3 |- * by lia.
  replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
  apply H; [cbn; lia | right; exact Hv | subst D; right; apply in_or_app; right; exact Hxk
           | subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb
           | exact Hx3 | exact Hc3 | exact HP3].
Qed.

(* the node predicate reads only the node's 56 bytes and the blocks of D (its footprint pj_footR) *)
Lemma pi_nodeR_agr : forall t F m m' lblk p D, pi_agr F m m' -> (forall x, pj_footR p D x -> F x) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m' lblk p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros F m m' lblk p D HA HM H; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [apply (pi_hdrR_agr F m m'); [exact HA | intros x Hx; apply HM; left; exact Hx | exact Hh]|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pi_cstrR_agr F m m'); [exact HA | | exact Hc].
  intros x Hx. apply HM. right. exists (str, k). split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (pi_cstrR_agr F m m'); [exact HA | | exact Hc].
  intros x Hx. apply HM. right. exists (str, k). split; [subst D; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
  { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pi_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk)); [|exact Hi].
  intros i u D1 Hil Hu Hinc HP.
  assert (Hp : 0 < cap) by lia.
  rewrite Forall_forall in IH.
  apply (IH u Hu F m m' lblk _ D1 HA); [|exact HP].
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (pi_memsR_mono m m' lblk (pj_nodeR segs m lblk) (pj_nodeR segs m' lblk)); [|exact Hi].
  intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
  assert (Hp : 0 < cap) by lia.
  split; [|split].
  + apply (pi_u64_agr F m m'); [exact HA | | exact Hx]. intros y Hy. apply HM. right. exists (keys, 8 * cap).
    split; [apply (proj2 (Hin Hp)) | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply (pi_cstrR_agr F m m'); [exact HA | | exact Hcs].
    intros y Hy. apply HM. right. exists (x, k). split; [apply HDi; exact Hxk | unfold pj_holdsR; cbn [fst snd]; exact Hy].
  + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH F m m' lblk _ D1 HA); [|exact HP].
    intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
    * right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holdsR; cbn [fst snd]; lia].
    * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

End fr.

(* a reader agreement at the restricted memory gives the aview agreement the shadow and window clauses read *)
Lemma pi_aview_agr : forall {fx : YK11.FPState} {rc : YM05.RunCeil} segs F (H : word -> bool) (m m' : word -> option byte) a,
  pi_agr F (mrestrict H m) (mrestrict H m') -> F a -> aview segs H m' a = aview segs H m a.
Proof. intros fx rc segs F H m m' a HA Ha. unfold aview, mbyte. rewrite (HA a Ha). reflexivity. Qed.

Lemma pi_ra_agr : forall {fx : YK11.FPState} {rc : YM05.RunCeil} segs F (H : word -> bool) (m m' : word -> option byte) a n,
  pi_agr F (mrestrict H m) (mrestrict H m') -> (forall x, a <= x < a + n -> F (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof.
intros fx rc segs F H m m' a n HA HF HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s.
rewrite (pi_aview_agr segs F H m m' _ HA (HF x Hx)). auto.
Qed.

(* a frame region stays as the epilogue reads it when the readers agree on its 104 bytes and on the window bytes
   outside FP, and sp, gp, tp are the same registers *)
Lemma pi_frame_kept : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}
  (F : Z -> Prop) (regs0 regs regs' : bvmap 5 word) (W : world pa_segs) mem Wc memc memc' e q v,
  pi_frame regs0 regs W mem Wc memc e q v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  pi_agr F (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall a, spZ regs0 - 104 <= a < spZ regs0 -> F a) ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a -> F a) ->
  pi_frame regs0 regs' W mem Wc memc' e q v.
Proof.
intros fx rc L PA F regs0 regs regs' W mem Wc memc memc' e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fra & Fe0 & Fe16)
  Hsp H3 H4 HA HF1 HF2.
unfold PI_FRAME in Fsp.
assert (VK : forall o w, 40 <= o -> o + 8 <= 144 ->
  val_mem pa_segs (mrestrict (w_H Wc) memc) (spZ regs + o) 8 w -> val_mem pa_segs (mrestrict (w_H Wc) memc') (spZ regs' + o) 8 w).
{ intros o w Ho1 Ho2 Hv. rewrite Hsp. apply (pi_val_agr pa_segs F _ _ _ _ _ HA); [|exact Hv]. intros kk Hk. apply HF1. lia. }
split; [unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
split; [apply VK; [lia | lia | exact V1]|]. split; [apply VK; [lia | lia | exact V2]|].
split; [apply VK; [lia | lia | exact V3]|]. split; [apply VK; [lia | lia | exact V4]|].
split; [apply VK; [lia | lia | exact V5]|]. split; [apply VK; [lia | lia | exact V6]|].
split; [apply VK; [lia | lia | exact V7]|]. split; [apply VK; [lia | lia | exact V8]|].
split; [apply VK; [lia | lia | exact V9]|]. split; [apply VK; [lia | lia | exact V10]|].
split; [apply VK; [lia | lia | exact V11]|]. split; [apply VK; [lia | lia | exact V12]|].
split; [apply VK; [lia | lia | exact V13]|].
split; [|exact (conj Fra (conj Fe0 Fe16))].
intros a Ha Hn. rewrite (pi_aview_agr pa_segs F (w_H Wc) memc memc' a HA (HF2 a Ha Hn)). exact (Fw a Ha Hn).
Qed.

(* a field of a region of a symbolic state (skip_ws_x.v's skw_field, over any segment list) *)
Lemma pi_field : forall {fx : YK11.FPState} segs E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros fx segs E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.

Lemma pi_region_nth : forall {fx : YK11.FPState} segs val E ss ms i r,
  st_ok_pi segs val E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros fx segs val E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

(* ---- the ledger and placement facts at image B ---- *)
Section agl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* the node may lie in a live harness block, a live allocator block, a live fake frame, or the caller's window
   (PRH_FnReader.v prhReader_at); in each case its bytes are inside the address space *)
Lemma cl_at_bounds : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 ->
  YM05.alloc_ceiling <= ly_stk_lo ly -> ly_stk_lo ly <= spZ regs0 -> spZ regs0 + e <= 2 ^ 47 ->
  4096 <= v /\ v + 56 <= 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLG HAT Hlo Hsp Hhi.
pose proof HLG as HB. apply prh_ledger_blocks in HB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
assert (RS : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia);
assert (RS0 : forall n, 0 <= req_size n \/ req_size n = n) by (intros n; unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct HAT as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (Hk0 & Hab & _ & _ & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & B2 & B3 & _).
  assert (HX : 0 <= k + cf_head) by lia. pose proof (RS (k + cf_head) HX). lia.
- destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & B2 & B3 & _).
  assert (Hm : 56 <= m) by lia. assert (HX : 0 <= m) by lia. pose proof (RS m HX). lia.
- destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as (_ & Hf).
  pose proof (proj1 (Forall_forall _ _) Hf (cid, pos) Hin) as [F1 F2]. cbn [fst snd] in F1, F2. lia.
- lia.
Qed.

(* the ledger reads only the statics and the hidden heads, all below the allocation ceiling (ex_ws_x.v's
   exw_ledger_kept, over pi_agr) *)
Lemma cl_ledger_agr : forall (F : Z -> Prop) ly S Hp (W : world SEGS) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> F a) ->
  pi_agr F (rdW W mem) (rdW W mem') ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros F ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HF HA HLG.
(* every fact of the ledger by its named projection (PRH_Base.v Section ledger_proj) *)
pose proof HLG as HND. apply prh_ledger_nodup in HND.
pose proof HLG as HB. apply prh_ledger_blocks in HB.
pose proof HLG as HP. apply prh_ledger_heads in HP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
assert (RS : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia);
assert (RS0 : forall n, 0 <= req_size n \/ req_size n = n) by (intros n; unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (VK : forall a n w, 0 <= a -> a + Z.of_nat n <= YM05.alloc_ceiling ->
  val_mem SEGS (rdW W mem) a n w -> val_mem SEGS (rdW W mem') a n w).
{ intros a n w Ha Hn. apply (pi_val_agr SEGS F _ _ _ _ _ HA). intros kk Hk. apply HF. clear - Ha Hn Hk; lia. }
unfold prh_ledger. refine (conj _ (conj HND (conj _ HP))).
- (* the glob, cell by cell: each val_mem cell is a static in low memory (VKs; its address and width computed at
     prh_img_B), each bound is the bounds projection's or the cell's own *)
  pose proof HLG as G1. apply prh_ledger_live in G1.
  pose proof HLG as G2. apply prh_ledger_peak in G2.
  pose proof HLG as G3. apply prh_ledger_count in G3.
  pose proof HLG as G4. apply prh_ledger_fail in G4.
  pose proof HLG as G5. apply prh_ledger_ran in G5.
  pose proof HLG as G6. apply prh_ledger_most in G6. destruct G6 as (G6 & M1 & M2).
  pose proof HLG as G7. apply prh_ledger_own in G7. destruct G7 as (G7 & O1).
  pose proof HLG as GB. apply prh_ledger_bounds in GB.
  destruct GB as ((L1 & L2) & L3 & (L4 & L5) & (L6 & L7) & L8).
  assert (VKs : forall a n w, 0 <= a -> a + Z.of_nat n <= kLowMemEnd ->
    val_mem SEGS (rdW W mem) a n w -> val_mem SEGS (rdW W mem') a n w).
  { intros a n w Ha Hn. apply VK; [exact Ha | clear - Hn C1 C5; lia]. }
  unfold prh_glob, prh_most, prh_own.
  repeat split; try assumption;
  (apply VKs; [apply Z.leb_le; reflexivity | apply Z.leb_le; reflexivity | assumption]).
- revert HB. apply Forall_impl. intros [a k] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
  refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Kin) as (B1 & B2 & B3 & _).
  pose proof alloc_ceiling_val as (AC1 & AC2).
  assert (HU : exists u, a - cf_head = 16 * u)
    by (exists ((a - cf_head) / 16); rewrite (Z.div_mod (a - cf_head) 16) at 1 by discriminate; rewrite B1, Z.add_0_r; reflexivity).
  assert (HV : exists u, YM05.alloc_ceiling = 4096 * u)
    by (exists (YM05.alloc_ceiling / 4096); rewrite (Z.div_mod YM05.alloc_ceiling 4096) at 1 by discriminate; rewrite AC2, Z.add_0_r; reflexivity).
  destruct HU as [u Hu]. destruct HV as [u2 Hu2].
  apply (VK (a - cf_head) 8%nat k); [lia | change (Z.of_nat 8) with 8 | exact Kv].
  revert B3. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; intros B3; lia.
Qed.

(* every block the subtree owns lies below the allocation ceiling (its base is a harness block of the ledger) *)
Lemma cl_D_bounds : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> 4096 <= b /\ b + m <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLG Hin.
pose proof HLG as HB. apply prh_ledger_blocks in HB.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (proj1 (Forall_forall _ _) HB (b, m) Hin) as (Hk0 & Hab & _ & _ & _). cbn [fst snd] in Hk0, Hab.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & B2 & B3 & _).
assert (RS : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia);
assert (RS0 : forall n, 0 <= req_size n \/ req_size n = n) by (intros n; unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (HX : 0 <= m + cf_head) by lia. pose proof (RS (m + cf_head) HX). lia.
Qed.

(* the ledger is a reader predicate: it survives any memory with the same restricted reader *)
Lemma cl_ledger_rdeq : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own,
  rdW W m' = rdW W m ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own Heq H.
unfold prh_ledger, prh_glob, prh_most, prh_own, prh_hblock in H |- *. rewrite Heq. exact H.
Qed.

End agl.
