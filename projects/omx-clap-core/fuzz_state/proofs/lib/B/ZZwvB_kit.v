(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_kit.v (a working branch
   1a5dc5b2e7c): same lemma names, statements and proofs; imports point at lib/B's image files and walk kit (YB1v, YB1w,
   FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer, FSH_Fn_alloc, FSW_K, FSW_K3, FSW_ret, FSW_rres, FSW_rd, FSW_pj, YF0x and
   FSW_write_value_entry, which holds the names of image A's FSW_writer_tbl); the image-agnostic FSupoison, FSupoisonU,
   FSH_YC20, FSH_Gen, FSupoisonStack stay lib/A's; FSH_Fn_reader is lib/B's (Required, used qualified: lib/B's
   FSH_Fn_writer states the root node with lib/B's FSH_Fn_reader.pobj). lib/B has no FSW_writer_model / FSW_writer_kit;
   this file uses no name of either.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B.
   write_value's CONTAINER arms (fs.asan-ubsan image B, write_value 0x84010): the TRANSPORT kit the arms' call sites
   use to carry the tree, the root object, the live list, arodata and the writer's statics across a callee's journal
   and across a run that writes write_value's own frame only.
   PROVENANCE (copied, not imported): every lemma below is a Theorem Labs lane's; image B's copies are
   lib/B/FSW_pj_write.v's pjw_avb .. pjw_j_arodata_journalU, pjw_p_stack_not_ush, pjw_p_zbytes_avb, pjw_p_above_kept
   (:867-1420, :1936-1970), the same proofs over the same lib/B kit; here renamed pjw_ -> zwk_ as image A's
   lib/A/ZZwv_kit.v names them, so that this file and FSW_pj_write.v can be imported together, proofs unchanged.
   pj_write's own lemmas are not copied. Rule 24: no function proved here (write_value's lookup: lane record
   (internal path), CHECKER CONFIRM a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSupoisonStack.
(* lib/B's FSW_rd is loaded before lib/B's FSH_Fn_writer, so the short name FSH_Fn_reader (loaded by FSW_rd as lib/B's
   and by FSH_Fn_writer as lib/A's) resolves to lib/A's module, the one lib/B's writer statement names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_pj
FSH_Fn_writer FSW_write_value_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Definition zwk_avb (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

(* ---- helpers ---- *)
(* a restricted byte below alloc_ceiling and off the image: aview equality is raw (restricted) equality *)
Lemma zwk_t_mrZ : forall (W : world tfibsegs) m m' a, zwk_avb W m m' -> 0 <= a < alloc_ceiling ->
  ~ in_img tfibsegs a -> mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros W m m' a Hv Ha Hn. pose proof alloc_ceiling_lt as Hc.
pose proof (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' a (Hv a Ha)) as X. unfold mbyte in X.
rewrite (seg_rom_none tfibsegs a ltac:(lia) Hn) in X.
destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.
Lemma zwk_t_mr : forall (W : world tfibsegs) m m' (x : word), zwk_avb W m m' -> bv_unsigned x < alloc_ceiling ->
  ~ in_img tfibsegs (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x.
Proof.
intros W m m' x Hv Hx Hn. pose proof (u64_range x) as Hr.
assert (E : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite E. apply zwk_t_mrZ; [exact Hv | lia | exact Hn].
Qed.
Lemma zwk_t_val_mem : forall (W : world tfibsegs) m m' a (n : nat) v, zwk_avb W m m' ->
  0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v Hv H0 Hn Hm k Hk.
rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' (a + Z.of_nat k)); [exact (Hm k Hk)|].
apply Hv. lia.
Qed.
Lemma zwk_t_range_addressable : forall (W : world tfibsegs) m m' p n, zwk_avb W m m' ->
  0 <= p -> p + n <= alloc_ceiling ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n ->
  range_addressable (aview tfibsegs (w_H W) m') SHADOW_OFF p n.
Proof.
intros W m m' p n Hv Hp Hn Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (Hx' : 0 <= x < alloc_ceiling) by lia.
rewrite (Hv _ (fsw_shadow_below x Hx')). exact Es.
Qed.
(* the root node's 56 bytes are off the image (a live fake frame or a live heap block) *)
Lemma zwk_t_pobj_img : forall ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> forall a, v <= a < v + 56 -> ~ in_img tfibsegs a.
Proof.
intros ly S W mx md m v HAR HP a Ha. pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HP as ([((cid & pos & Hin & Hc & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] & _).
- apply (frm_img tfibsegs B LAWS ly S W mx md cid pos a HAR Hin). lia.
- apply (blk_img tfibsegs B LAWS ly S W mx md b n a HAR Hin). unfold HEAD in *. lia.
Qed.
(* every block of a node's list is one of lblk's (pj_node states lblk of each entry it adds) *)
Lemma zwk_t_items_in : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (R : Z * Z -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall b, In b D1 -> R b) ->
  PjStruct.pj_items P a l D -> forall b, In b D -> R b.
Proof.
intros P R l. induction l as [|u r IH]; intros a D H Hl b Hb; cbn [PjStruct.pj_items] in Hl.
- subst D. destruct Hb.
- destruct Hl as (D1 & D2 & E & HP & HR). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + exact (H a u D1 (or_introl eq_refl) HP b Hb).
  + apply (IH (a + 56) D2); [|exact HR | exact Hb].
    intros a' u' D3 Hu HP3 b' Hb'. exact (H a' u' D3 (or_intror Hu) HP3 b' Hb').
Qed.
Lemma zwk_t_mems_in : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (R : Z * Z -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall b, In b D1 -> R b) ->
  (forall x k, lblk x k -> R (x, k)) ->
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> forall b, In b D -> R b.
Proof.
intros m lblk P R l. induction l as [|[nm u] r IH]; intros a ka D H HL Hl b Hb; cbn [PjStruct.pj_mems] in Hl.
- subst D. destruct Hb.
- destruct Hl as (x & k & D1 & D2 & E & _ & Hc & HP & HR). subst D. destruct Hb as [Hb|Hb].
  + subst b. apply HL. exact (proj1 Hc).
  + apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    * exact (H a nm u D1 (or_introl eq_refl) HP b Hb).
    * apply (IH (a + 56) (ka + 8) D2); [| exact HL | exact HR | exact Hb].
      intros a' nm' u' D3 Hu HP3 b' Hb'. exact (H a' nm' u' D3 (or_intror Hu) HP3 b' Hb').
Qed.
Lemma zwk_t_node_lblk : forall t m lblk p D, PjStruct.pj_node tfibsegs m lblk p t D ->
  forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H b Hb; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hd).
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & ED). subst D. destruct Hb.
- destruct Hd as (_ & _ & _ & _ & _ & k & Hc & ED). subst D. destruct Hb as [Hb|[]]. subst b. exact (proj1 Hc).
- destruct Hd as (_ & _ & _ & _ & k & Hc & ED). subst D. destruct Hb as [Hb|[]]. subst b. exact (proj1 Hc).
- destruct Hd as (_ & _ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hb as [Hb|[]]. subst b. cbn [fst snd].
    destruct Hcap as [(Hc0 & _)|(_ & L)]; [lia | exact L].
  + apply (zwk_t_items_in (PjStruct.pj_node tfibsegs m lblk) (fun b => lblk (fst b) (snd b)) items kids Di);
      [| exact Hi | exact Hb].
    intros a' u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. exact (IH u Hu m lblk a' D1 HP b' Hb').
- destruct Hd as (_ & _ & _ & Hcap & Di & ED & Hi). subst D. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hcap as [(Hc0 & _)|(_ & L0 & L1)]; [lia|].
    destruct Hb as [Hb|[Hb|[]]]; subst b; cbn [fst snd]; assumption.
  + apply (zwk_t_mems_in m lblk (PjStruct.pj_node tfibsegs m lblk) (fun b => lblk (fst b) (snd b))
      members kids keys Di); [| | exact Hi | exact Hb].
    * intros a' nm u D1 Hu HP b' Hb'. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      exact (IH m lblk a' D1 HP b' Hb').
    * intros x k Hx. exact Hx.
Qed.

(* ---- the eight transports ---- *)
Lemma zwk_avb_of_same_below : forall W m m', same_below m m' alloc_ceiling -> zwk_avb W m m'.
Proof. intros W m m' Hs a Ha. exact (aview_below (w_H W) m m' alloc_ceiling a Hs Ha). Qed.

Lemma zwk_avb_trans : forall W m1 m2 m3, zwk_avb W m1 m2 -> zwk_avb W m2 m3 -> zwk_avb W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Lemma zwk_fs_glob_avb : forall W m m' live peak cnt fail, zwk_avb W m m' ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hv (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hm. exact (zwk_t_val_mem W m m' a 8 v Hv Ha Hb Hm). }
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.

Lemma zwk_arodata_avb : forall W m m', zwk_avb W m m' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' Hv HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (Hv a Hb). exact (HR a Ha Ho He).
Qed.

Lemma zwk_rblock_avb : forall ly S W m m' mx md p n, AR tfibsegs B ly S W mx md -> zwk_avb W m m' ->
  fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S W m' p n.
Proof.
intros ly S W m m' mx md p n HAR Hv Hb. pose proof Hb as (Hin & Hal & Hn & Hm).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
apply (zwk_t_val_mem W m m' (p - HEAD) 8 n Hv); [unfold HEAD in *; lia | | exact Hm].
change (Z.of_nat 8) with 8. unfold HEAD in *. lia.
Qed.

Lemma zwk_ublocks_avb : forall ly S W m m' mx md UL, AR tfibsegs B ly S W mx md -> zwk_avb W m m' ->
  ublocks_ok B tfibsegs ly S W m UL -> ublocks_ok B tfibsegs ly S W m' UL.
Proof.
intros ly S W m m' mx md UL HAR Hv H a k Hak. exact (zwk_rblock_avb ly S W m m' mx md a k HAR Hv (H a k Hak)).
Qed.

Lemma zwk_pobj_avb : forall ly S W m m' mx md v, AR tfibsegs B ly S W mx md -> zwk_avb W m m' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> FSH_Fn_reader.pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' mx md v HAR Hv HP.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2).
pose proof (zwk_t_pobj_img ly S W mx md m v HAR HP) as HNI.
destruct HP as [Hpl Hw]. split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right].
  + split; [exact Hf|]. split; [exact Ha|].
    exact (zwk_t_range_addressable W m m' v 56 Hv ltac:(lia) L2 Hr).
  + split; [exact Hb|]. split; [exact Ha|].
    exact (zwk_t_range_addressable W m m' v 56 Hv ltac:(lia) L2 Hr).
- intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) m) (mrestrict (w_H W) m') (v + i)); [|exact (Hw i Hi)].
  apply zwk_t_mrZ; [exact Hv | lia | apply HNI; lia].
Qed.

Lemma zwk_pj_node_avb : forall ly S W m m' mx md lblk v t D UL, AR tfibsegs B ly S W mx md -> zwk_avb W m m' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a k, In (a, k) D -> In (a, k) UL) ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m) lblk v t D ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m') lblk v t D.
Proof.
intros ly S W m m' mx md lblk v t D UL HAR Hv HP HU HD HN.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) lblk (mrestrict (w_H W) m') lblk v D HN).
- intros a k Hak. exact (zwk_t_node_lblk t (mrestrict (w_H W) m) lblk v D HN (a, k) Hak).
- intros x Hx. apply (zwk_t_mr W m m' x Hv).
  + destruct Hx as [Hx|((a & k) & Hb & Hx)].
    * destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2). lia.
    * destruct (HU a k (HD a k Hb)) as (Hin & _ & _ & _).
      destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
      unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx. unfold HEAD in *. lia.
  + destruct Hx as [Hx|((a & k) & Hb & Hx)].
    * exact (zwk_t_pobj_img ly S W mx md m v HAR HP _ Hx).
    * destruct (HU a k (HD a k Hb)) as (Hin & _ & _ & _).
      destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
      unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
      apply (blk_img tfibsegs B LAWS ly S W mx md (a - HEAD) (k + HEAD) (bv_unsigned x) HAR Hin).
      unfold HEAD in *. lia.
Qed.

(* ---- from FSW_zwk_jr.v (a Theorem Labs lane), pasted unchanged ---- *)

(* ---- every block of a node's list satisfies the node's block relation ---- *)
Lemma zwk_j_items_lblk : forall (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  Forall (fun u => forall a' D', P a' u D' -> forall x k, In (x, k) D' -> lblk x k) l ->
  PjStruct.pj_items P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros lblk P l. induction l as [|u r IH]; intros a D HF Hl x k Hin; cbn [PjStruct.pj_items] in Hl.
- subst D. destruct Hin.
- destruct Hl as (D1 & D2 & -> & HP & HR). apply Forall_cons_iff in HF as [Hu HF].
  apply in_app_or in Hin as [Hin|Hin]; [exact (Hu _ _ HP x k Hin) | exact (IH (a + 56) D2 HF HR x k Hin)].
Qed.
Lemma zwk_j_mems_lblk : forall m (lblk : Z -> Z -> Prop) (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  Forall (fun nu : list Z * PjTree.jv => forall a' D', P a' (snd nu) D' -> forall x k, In (x, k) D' -> lblk x k) l ->
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D HF Hl x k Hin; cbn [PjStruct.pj_mems] in Hl.
- subst D. destruct Hin.
- destruct Hl as (x0 & k0 & D1 & D2 & -> & _ & (Hlb & _ & _) & HP & HR). apply Forall_cons_iff in HF as [Hu HF].
  destruct Hin as [E|Hin]; [injection E as <- <-; exact Hlb|].
  apply in_app_or in Hin as [Hin|Hin]; [exact (Hu _ _ HP x k Hin) | exact (IH (a + 56) (ka + 8) D2 HF HR x k Hin)].
Qed.
Lemma zwk_j_node_lblk : forall t m lblk p D, PjStruct.pj_node tfibsegs m lblk p t D ->
  forall a k, In (a, k) D -> lblk a k.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H a k Hin; cbn [PjStruct.pj_node] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb).
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & ->). destruct Hin.
- destruct Hb as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
- destruct Hb as (_ & _ & _ & _ & Hcap & Di & -> & Hi).
  apply in_app_or in Hin as [Hin|Hin].
  + revert Hin. destruct (Z.eqb_spec cap 0) as [E0|E0]; [intros []|]. intros [E|[]]. injection E as <- <-.
    destruct Hcap as [(Hc & _)|(_ & Hl)]; [lia | exact Hl].
  + apply (zwk_j_items_lblk lblk (PjStruct.pj_node tfibsegs m lblk) items kids Di); [|exact Hi|exact Hin].
    eapply Forall_impl; [|exact IH]. intros u Hu a' D' HP x k' Hx. exact (Hu m lblk a' D' HP x k' Hx).
- destruct Hb as (_ & _ & _ & Hcap & Di & -> & Hi).
  apply in_app_or in Hin as [Hin|Hin].
  + revert Hin. destruct (Z.eqb_spec cap 0) as [E0|E0]; [intros []|].
    destruct Hcap as [(Hc & _)|(_ & Hl1 & Hl2)]; [lia|].
    intros [E|[E|[]]]; injection E as <- <-; assumption.
  + apply (zwk_j_mems_lblk m lblk (PjStruct.pj_node tfibsegs m lblk) members kids keys Di); [|exact Hi|exact Hin].
    eapply Forall_impl; [|exact IH]. intros nu Hu a' D' HP x k' Hx. exact (Hu m lblk a' D' HP x k' Hx).
Qed.

(* ---- an app byte of a block or a frame is never a user-poisoned shadow byte ---- *)
Lemma zwk_j_app_not_ush : forall ly S U (W : world tfibsegs) m md a lo len, ARU tfibsegs B ly S U W m md ->
  in_app lo len -> lo <= a < lo + len -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly S U W m md a lo len HARU Happ Ha.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in *; lia).
rewrite (wz _ Ha64) in E.
destruct (ush_facts tfibsegs B ly S U W m md a HARU E) as (_ & L1 & L2).
unfold in_app, kLowShadowBeg, SHADOW_OFF, ASAN_CEIL in *. lia.
Qed.

(* ---- an app byte off the image whose unpoisoned view is kept is kept on the machine's own memories ---- *)
Lemma zwk_j_view_kept : forall ly S U (W : world tfibsegs) m md ly' S' U' (W' : world tfibsegs) m' md' a lo len,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  in_app lo len -> lo <= a < lo + len -> ~ in_img tfibsegs a ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros ly S U W m md ly' S' U' W' m' md' a lo len HARU HARU' Happ Ha Hni E.
rewrite (aview_unpoison_out tfibsegs _ U' m' a (zwk_j_app_not_ush ly' S' U' W' m' md' a lo len HARU' Happ Ha)) in E.
rewrite (aview_unpoison_out tfibsegs _ U m a (zwk_j_app_not_ush ly S U W m md a lo len HARU Happ Ha)) in E.
split; [exact E|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold in_app, kLowShadowBeg, ASAN_CEIL in *; lia).
pose proof (mbyte_of_aview tfibsegs _ _ _ _ a E) as Em.
pose proof (seg_rom_none tfibsegs a Ha64 Hni) as Hr.
unfold mbyte in Em. rewrite Hr in Em.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.

(* ---- a byte of a block live at both ends, outside FP, is kept ---- *)
Lemma zwk_j_blk_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k p n a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n -> ~ inFP FP a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k p n a HJ HARU HARU' H1 H2 Ha Hnf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (proj1 HARU) as HAR.
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U m) md p n HAR H1) as (_ & _ & _ & Happ & _).
apply (zwk_j_view_kept ly S U W m md ly' S' U' W' m' md' a p (req_size n) HARU HARU' Happ Ha).
- exact (blk_img tfibsegs B LAWS ly S W (unpoison U m) md p n a HAR H1 Ha).
- pose proof (F2 p n (a - p) H1 H2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hnf)) as E.
  replace (p + (a - p)) with a in E by lia. exact E.
Qed.

(* ---- a byte of a frame of frames S, outside FP, is kept ---- *)
Lemma zwk_j_frm_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k
  cid pos a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  ~ inFP FP a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k cid pos a HJ HARU HARU' Hin Ha Hnf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
pose proof (proj1 HARU) as HAR.
destruct (al_frames tfibsegs B LAWS ly S W (unpoison U m) md cid pos HAR Hin) as (_ & Happ & _).
apply (zwk_j_view_kept ly S U W m md ly' S' U' W' m' md' a _ _ HARU HARU' Happ Ha).
- exact (frm_img tfibsegs B LAWS ly S W (unpoison U m) md cid pos a HAR Hin Ha).
- apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnf].
Qed.

(* ---- every byte of the tree's footprint is kept ---- *)
Lemma zwk_j_foot_kept : forall STK sp0 FP ly S U (W : world tfibsegs) m md own ly' S' U' (W' : world tfibsegs) m' md' k
  v D UL a,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  PjStruct.pj_foot v D a ->
  aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a /\
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL a HJ HARU HARU' HP HUL HD HLIVE HFP Hf.
pose proof (HFP a Hf) as Hnf. pose proof Hf as Hf0.
destruct Hf as [Hv | ((a0 & kk) & Hb & Hx)].
- destruct HP as ([((cid & pos & Hin & Hc & Hal & H1 & H2) & _ & _) | ((b & mm & Hin & H1 & H2) & _ & _)] & _).
  + exact (zwk_j_frm_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k cid pos a HJ HARU HARU' Hin
      ltac:(lia) Hnf).
  + assert (Hba : b <= a < b + req_size mm) by (unfold HEAD in *; lia).
    exact (zwk_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k b mm a HJ HARU HARU' Hin
      (HLIVE b mm a Hin Hba Hf0) Hba Hnf).
- unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
  destruct (HUL a0 kk (HD a0 kk Hb)) as (Hin & _ & Hk & _).
  pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
  assert (Hba : a0 - HEAD <= a < a0 - HEAD + req_size (kk + HEAD)) by (unfold HEAD in *; lia).
  exact (zwk_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k (a0 - HEAD) (kk + HEAD) a HJ HARU HARU'
    Hin (HLIVE _ _ a Hin Hba Hf0) Hba Hnf).
Qed.

(* ================= 1. the tree across the journal ================= *)
Lemma zwk_pj_node_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k lblk v t D UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W) m) lblk v t D ->
  PjStruct.pj_node tfibsegs (mrestrict (w_H W') m') lblk v t D.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k lblk v t D UL HJ HARU HARU' HP HUL HD HLIVE HFP HN.
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) lblk (mrestrict (w_H W') m') lblk v D HN).
- exact (zwk_j_node_lblk t _ lblk v D HN).
- intros x Hx.
  pose proof (proj2 (zwk_j_foot_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL (bv_unsigned x)
    HJ HARU HARU' HP HUL HD HLIVE HFP Hx)) as E.
  rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* ================= 2. the root object across the journal =================
   The same premises as 1 (the root's block, when it is one, stays live: the liveness premise covers every byte of
   pj_foot v D, the root's 56 bytes included; a root frame stays live because frames S' = own ++ frames S), plus two
   facts about SHADOW bytes, which no journal clause keeps for a block and clause F4 keeps for a frame only off FP:
   - fs_heads at the end: every user-poisoned range of U' is the 16-byte head at the start of a live block, so none
     covers the root's 56 bytes (a root in a block lies past its head; any other block is disjoint), hence the raw
     shadow reads as AR's (YCbq.range_addressable_of_block);
   - FP misses the shadow region (YCbq.range_addressable_entry_frame's premise form), for a root in a frame. *)
Lemma zwk_pobj_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  FSH_Fn_reader.pobj tfibsegs B ly S W m v -> ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) D -> In (a, kk) UL) ->
  (forall b n x, In (b, n) (ablocks B ly S) -> b <= x < b + req_size n -> PjStruct.pj_foot v D x ->
     In (b, n) (ablocks B ly' S')) ->
  (forall x, PjStruct.pj_foot v D x -> ~ inFP FP x) ->
  fs_heads B ly' S' U' ->
  (forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
  FSH_Fn_reader.pobj tfibsegs B ly' S' W' m' v.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL HJ HARU HARU' HP HUL HD HLIVE HFP HH HFPS.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof (proj1 HARU) as HAR. pose proof (proj1 HARU') as HAR'.
assert (Hkept : forall i, 0 <= i < 56 ->
  mrestrict (w_H W') m' (Z_to_bv 64 (v + i)) = mrestrict (w_H W) m (Z_to_bv 64 (v + i))).
{ intros i Hi. refine (proj2 (zwk_j_foot_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k v D UL (v + i)
    HJ HARU HARU' HP HUL HD HLIVE HFP _)). left. lia. }
pose proof HP as [Hpl Hw]. split.
2: { intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) m)); [exact (Hkept i Hi) | exact (Hw i Hi)]. }
destruct Hpl as [((cid & pos & Hin & Hc & Hal & H1 & H2) & Hv8 & Hra) | ((b & mm & Hin & H1 & H2) & Hv8 & Hra)].
- (* a root in a live fake frame *)
  left.
  assert (Efa : frame_addr ly' cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U m) md cid pos HAR Hin) as (Hf0 & Hfc & _).
  split; [exists cid, pos; rewrite Efa; repeat split; assumption|].
  split; [exact Hv8|].
  (* the frame's shadow bytes are no block's, at either end, so unpoison does not touch them *)
  assert (NB : forall ly0 S0 U0 (W0 : world tfibsegs) m0 md0 x, ARU tfibsegs B ly0 S0 U0 W0 m0 md0 ->
    In (cid, pos) (frames S0) -> frame_addr ly0 cid pos = frame_addr ly cid pos -> v <= x < v + 56 ->
    aview tfibsegs (w_H W0) m0 (shadow_of_addr SHADOW_OFF x) =
    aview tfibsegs (w_H W0) (unpoison U0 m0) (shadow_of_addr SHADOW_OFF x)).
  { intros ly0 S0 U0 W0 m0 md0 x HARU0 Hin0 Efa0 Hx. symmetry. apply aview_unpoison_out.
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (ARU_shadow_out_block tfibsegs B ly0 S0 U0 W0 m0 md0 x HARU0); [unfold ASAN_CEIL in *; lia|].
    intros p n Hpn Hpx.
    pose proof (sep_block_frame tfibsegs B LAWS ly0 S0 W0 (unpoison U0 m0) md0 p n cid pos (proj1 HARU0) Hpn Hin0)
      as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa0 in Hd. lia. }
  apply (range_addressable_agree (aview tfibsegs (w_H W') (unpoison U' m'))).
  { intros x Hx. exact (NB ly' S' U' W' m' md' x HARU' Hin' Efa Hx). }
  apply (range_addressable_entry_frame tfibsegs B LAWS STK sp0 FP ly S W (unpoison U m) md own ly' S' W'
    (unpoison U' m') md' k cid pos v 56 HJ Hin Hc H1 H2 Hal HFPS HAR).
  apply (range_addressable_agree (aview tfibsegs (w_H W) m)); [|exact Hra].
  intros x Hx. symmetry. exact (NB ly S U W m md x HARU Hin eq_refl Hx).
- (* a root in a live heap block, past its head *)
  right.
  assert (Hba : forall x, v <= x < v + 56 -> b <= x < b + req_size mm) by (intros x Hx; unfold HEAD in *; lia).
  assert (Hin' : In (b, mm) (ablocks B ly' S')).
  { apply (HLIVE b mm v Hin (Hba v ltac:(lia))). left. lia. }
  split; [exists b, mm; split; [exact Hin'|]; split; assumption|].
  split; [exact Hv8|].
  apply (range_addressable_agree (aview tfibsegs (w_H W') (unpoison U' m'))).
  2: { exact (range_addressable_of_block tfibsegs B LAWS ly' S' W' (unpoison U' m') md' b mm v 56 HAR' Hin'
         ltac:(unfold HEAD in *; lia) H2). }
  intros x Hx. symmetry. apply aview_unpoison_out.
  destruct (in_ush U' (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))) eqn:E; [|reflexivity]. exfalso.
  destruct (al_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' b mm HAR' Hin') as (_ & Hb4 & Hbc & _).
  assert (Hx0 : 0 <= x < alloc_ceiling) by (pose proof (Hba x Hx); lia).
  assert (Hs64 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
  { unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
  rewrite (wz _ Hs64) in E.
  apply in_ush_spec in E as (r & Hr & Hs).
  destruct (HH r Hr) as (Hsn & m0 & Hb0 & Hq0).
  rewrite Hsn in Hs. replace (16 / 8) with 2 in Hs by reflexivity.
  destruct (al_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' (fst r) m0 HAR' Hb0) as (Hr16 & _).
  assert (Hrx : fst r <= x < fst r + 16).
  { unfold shadow_addr, shadow_of_addr in Hs.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
    pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as Dr. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as Mr.
    assert (Er : fst r mod 8 = 0).
    { apply Z.mod_divide in Hr16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((2 * q) * 8) by lia.
      apply Z_mod_mult. }
    lia. }
  destruct (Z.eq_dec (fst r) b) as [Eb|Eb].
  + unfold HEAD in *. lia.
  + assert (Ne : (fst r, m0) <> (b, mm)) by (intros Eq; injection Eq as E1 E2; exact (Eb E1)).
    pose proof (sep_blocks tfibsegs B LAWS ly' S' W' (unpoison U' m') md' (fst r) m0 b mm HAR' Hb0 Hin' Ne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (Hba x Hx). lia.
Qed.

(* ================= 3. the live list across the journal ================= *)
Lemma zwk_ublocks_journal : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k UL,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  ublocks_ok B tfibsegs ly S W m UL ->
  (forall a kk, In (a, kk) UL -> In (a - HEAD, kk + HEAD) (ablocks B ly' S')) ->
  (forall a kk i, In (a, kk) UL -> 0 <= i < 8 -> ~ inFP FP (a - HEAD + i)) ->
  ublocks_ok B tfibsegs ly' S' W' m' UL.
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k UL HJ HARU HARU' HUL HLIVE HFP a kk Hak.
destruct (HUL a kk Hak) as (Hin & Hal & Hk & Hv).
split; [exact (HLIVE a kk Hak)|]. split; [exact Hal|]. split; [exact Hk|].
intros j Hj. rewrite <- (Hv j Hj).
pose proof (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
destruct (zwk_j_blk_kept STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k (a - HEAD) (kk + HEAD)
  (a - HEAD + Z.of_nat j) HJ HARU HARU' Hin (HLIVE a kk Hak) ltac:(unfold HEAD in *; lia)
  (HFP a kk (Z.of_nat j) Hak ltac:(lia))) as (_ & E).
unfold mbyte. rewrite E. reflexivity.
Qed.

(* ---- the read-only range is image bytes, all below SHADOW_OFF ---- *)
Lemma zwk_j_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) && (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
(* below SHADOW_OFF the raw memory is the unpoisoned one *)
Lemma zwk_j_mrestrict_low : forall ly S U (W : world tfibsegs) m md (H : word -> bool) x,
  ARU tfibsegs B ly S U W m md -> 0 <= x < SHADOW_OFF ->
  mrestrict H (unpoison U m) (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x).
Proof.
intros ly S U W m md H x HARU Hx. unfold mrestrict. destruct (H (Z_to_bv 64 x)); [reflexivity|].
apply (ARU_mem_low tfibsegs B ly S U W m md _ HARU). rewrite wz by (unfold SHADOW_OFF in *; lia). lia.
Qed.
(* arodata over the raw memory and over the unpoisoned one are the same fact under ARU *)
Lemma zwk_j_arodata_unpoison : forall ly S U (W : world tfibsegs) m md, ARU tfibsegs B ly S U W m md ->
  (arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) <->
   arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m))).
Proof.
intros ly S U W m md HARU.
assert (E : forall a, in_roP tfibsegs FS_RLO FS_RHI a ->
  aview tfibsegs (w_H W) (unpoison U m) a = aview tfibsegs (w_H W) m a).
{ intros a Hro. pose proof (fs_segs_img a (zwk_j_roP_img a Hro)) as Hl.
  unfold aview, mbyte. rewrite (zwk_j_mrestrict_low ly S U W m md (w_H W) a HARU)
    by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
  reflexivity. }
split; intros H a Hro Ho He; [rewrite (E a Hro) | rewrite <- (E a Hro)]; exact (H a Hro Ho He).
Qed.

(* ================= 4. the "\n" literal at any ARU state with arodata =================
   The arodata premise is over the UNPOISONED memory (the form fs_img_facts takes); zwk_j_arodata_unpoison turns the
   raw-memory form (fpreU's) into it. *)
Lemma zwk_ro_lit_kept : forall ly S U W m md, ARU tfibsegs B ly S U W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U m)) ->
  fs_img_facts tfibsegs B -> In (0x21040, [10]) FS_RO_STRS -> zbytes_at tfibsegs W m 0x21040 [10].
Proof.
intros ly S U W m md HARU HRO HIMG Hin.
unfold fs_img_facts, fs_img_facts_at in HIMG. destruct HIMG as (_ & HI).
destruct (HI ly S W (unpoison U m) md (proj1 HARU) HRO) as (_ & _ & HS & _).
pose proof (proj1 (Forall_forall _ _) HS _ Hin) as (((Hg & _) & _) & _).
intros j Hj. destruct j as [|j]; [|cbn in Hj; lia].
destruct (Hg 0%nat ltac:(cbn; lia)) as (Hv & Hb). split; [|exact Hb].
intros kk Hkk. etransitivity; [|exact (Hv kk Hkk)].
assert (Hkk0 : kk = 0%nat) by lia. subst kk.
unfold mbyte. rewrite (zwk_j_mrestrict_low ly S U W m md (w_H W)) by (exact HARU || (unfold SHADOW_OFF; cbn; lia)).
reflexivity.
Qed.

(* ================= 5. arodata across the journal =================
   No existing lemma has this core's form: A/ACeg.v arodata_ok_journal is stated over the donor's in_ro_tfa / YCe5
   journal. This core's image clause (YCbq.v:361-362) keeps an image byte that is not runtime-owned, not errno and
   fp_spares FP; the read-only range is image bytes (zwk_j_roP_img), so the premise is fp_spares FP over it (a caller
   with ~ YI16.sink_open_fp FP, e.g. every FP whose ranges start above 0 (YCbq.sink_closed_pos), has it by
   YCbq.fp_spares_closed). Stated over the journal's own memories, then in the walk's raw-memory form. *)
(* FP-keyed core (S0 400b2a240b3): the image clause spares an image byte that is not runtime-owned, not errno,
   NOT in FP and fp_spares FP, so the caller states both FP premises over the read-only range. *)
Lemma zwk_arodata_journal : forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' (W' : world tfibsegs) mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> fp_spares FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HNFP HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (zwk_j_roP_img a Hro) Ho He (HNFP a Hro) (HFP a Hro)). exact (HR a Hro Ho He).
Qed.
Lemma zwk_j_arodata_journalU : forall STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k ->
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> fp_spares FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') m').
Proof.
intros STK sp0 FP ly S U W m md own ly' S' U' W' m' md' k HJ HARU HARU' HNFP HFP HR.
apply (proj2 (zwk_j_arodata_unpoison ly' S' U' W' m' md' HARU')).
apply (zwk_arodata_journal STK sp0 FP ly S W (unpoison U m) md own ly' S' W' (unpoison U' m') md' k HJ HNFP HFP).
exact (proj1 (zwk_j_arodata_unpoison ly S U W m md HARU) HR).
Qed.

(* a stack byte is never a user-poisoned shadow byte: every range of U sits below kHighMemBeg *)
Lemma zwk_p_stack_not_ush : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  alloc_ceiling <= a < 2 ^ 64 -> in_ush U (bv_unsigned (Z_to_bv 64 a)) = false.
Proof.
intros ly S U W m md a HARU Ha.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity]. exfalso.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (wz a ltac:(lia)) in E.
destruct (ush_facts tfibsegs B ly S U W m md a HARU E) as (_ & _ & L2). lia.
Qed.
(* a byte run below alloc_ceiling rides across on zwk_avb *)
Lemma zwk_p_zbytes_avb : forall (W : world tfibsegs) m m' p l, zwk_avb W m m' ->
  0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling ->
  zbytes_at tfibsegs W m p l -> zbytes_at tfibsegs W m' p l.
Proof.
intros W m m' p l Hv Hp Hl H j Hj. destruct (H j Hj) as (Hval & Hb). split; [|exact Hb].
apply (zwk_t_val_mem W m m' (p + Z.of_nat j) 1 (nth j l 0) Hv); [lia | cbn [Z.of_nat]; lia | exact Hval].
Qed.
(* hence a stack byte whose unpoisoned view the journal keeps is kept on the machine's own memories *)
Lemma zwk_p_above_kept : forall ly S U (W : world tfibsegs) m md ly' S' U' (W' : world tfibsegs) m' md' a,
  ARU tfibsegs B ly S U W m md -> ARU tfibsegs B ly' S' U' W' m' md' ->
  alloc_ceiling <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W') (unpoison U' m') a = aview tfibsegs (w_H W) (unpoison U m) a ->
  mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a).
Proof.
intros ly S U W m md ly' S' U' W' m' md' a HARU HARU' Ha E.
pose proof fs_segs_low as HSL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (aview_unpoison_out tfibsegs _ U' m' a (zwk_p_stack_not_ush ly' S' U' W' m' md' a HARU' Ha)) in E.
rewrite (aview_unpoison_out tfibsegs _ U m a (zwk_p_stack_not_ush ly S U W m md a HARU Ha)) in E.
assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (HSL a Hi) as HL; unfold kLowMemEnd in *; lia).
pose proof (mbyte_of_aview tfibsegs _ _ _ _ a E) as Em.
unfold mbyte in Em. rewrite (seg_rom_none tfibsegs a ltac:(lia) Hni) in Em.
destruct (mrestrict (w_H W') m' (Z_to_bv 64 a)), (mrestrict (w_H W) m (Z_to_bv 64 a)); congruence.
Qed.

End K.
