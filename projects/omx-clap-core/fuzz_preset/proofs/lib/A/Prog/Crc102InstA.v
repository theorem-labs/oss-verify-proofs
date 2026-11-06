(* fuzz_preset, image A' (the #102 asan image, pinned 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the walk
   of check_reject_clean (Wcrc102.v) at the listing instance PI_prog_A (lib/A/PAImg_prog.v blob 505a51ff7d08, the
   #102 listing of record) and the PrhImg prh_img_A (lib/A/PRH_Img.v blob 934516a622e8, generated from the twin).
   A PORT of h-hpreset-7's S911ImgA.v / S911InstA.v (origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2).
   rule 24: proves function check_reject_clean (ported; no #102 copy exists).
   THE IMAGE PREMISES of the walk, each with its INSTANCE WITNESS here (unit ruling 16:4xZ):
   - IMG (Crc102Kit.v c102_img) is PROVED at PI_prog_A by computation (c102_img_A): the body is the image's (the
     table read from tfibsegs, which PI_prog_A's pa_segs Img0.rsegs is by conversion), the listing's three entries
     equal the generated Crc102Syms.v numbers (the generator and the listing agree), and the 56 bytes of `empty` are
     zero bytes of the image's first, read-only segment;
   - EMPTY_ZS / EMPTY_B follow from the unit's image binding TfibSyms B (owner a Theorem Labs lane), whose ts_zsh / ts_owned / ts_errno
     make them the TfibB facts proved here by computation (c102_empty_zs_A / c102_empty_b_A). WITNESS of TfibSyms:
     AD2l.TfibB_syms;
   - EMPTY_HULL follows from YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover (lib/Reusable/YImgShadowCoverCf.v) under S9_CF (the allocator
     relation implies ARcf). WITNESS of S9_CF: at h-pre-b1's ec_ARx = ARcf /\ xs_placed_cf, proj1
     (check_reject_clean_holds_A102_inst below). The hull of `empty` at A' is 8 shadow bytes, the shadow of app
     [0x20fc0, 0x21000) (computed below, not typed).
   Kept as premises: TS, S9_CF (image binding / allocator relation; both witnessed), LAWS (the engine's laws; discharged
   at ec_ARx by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf), BCMP (the bcmp row, the bcmp realizer's lane) and
   LIVE (K0's tfuzz_alloc_live_specX; its A' walk is h-w6rep-2's relocation).
   Numerals: 56 (LENGTH: struct pj), 8 (LENGTH: word); no ADDRESS is typed here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog CfImgA AF0m AImgShadowVisCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v PRH_Base PRH_Img PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crc102Syms Crc102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Wcrc102.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- IMG at PI_prog_A (S911ImgA.v, at the #102 numbers) ---- *)
(* the 56 bytes of `empty`, as one computed check *)
Definition c102_empty_chk : bool :=
  forallb (fun k => match seg_rom rsegs (Z_to_bv 64 (A102_crc_empty + Z.of_nat k)) with
                    | Some b => Z.eqb (bv_unsigned b) 0 | None => false end) (seq 0 56).
Lemma c102_empty_chk_ok : c102_empty_chk = true.
Proof. vm_compute. reflexivity. Qed.

(* the image's first segment is read-only and holds the 56 bytes of `empty` *)
Lemma c102_rseg0 : exists sg, In sg rsegs /\ seg_writable sg = false /\
  Z.of_N (seg_base sg) <= A102_crc_empty /\ A102_crc_empty + 56 <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
assert (P : match rsegs with sg :: _ => (seg_writable sg, Z.of_N (seg_base sg) <=? A102_crc_empty,
  A102_crc_empty + 56 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) | [] => (true, false, false) end = (false, true, true))
  by (vm_compute; reflexivity).
destruct rsegs as [|sg rest]; [discriminate|].
injection P as P1 P2 P3. apply Z.leb_le in P2. apply Z.leb_le in P3.
exists sg. split; [left; reflexivity|]. split; [exact P1|]. split; assumption.
Qed.

Section A. Context {rc : YM05.RunCeil}.
Theorem c102_img_A : c102_img PI_prog_A.
Proof.
constructor.
- exact tbl_crc102_img.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- intros i Hi. split.
  + left. destruct c102_rseg0 as (sg & Hin & Hw & Hlo & Hhi). exists sg. split; [exact Hin|]. split; [exact Hw|]. lia.
  + pose proof c102_empty_chk_ok as C. unfold c102_empty_chk in C.
    pose proof (proj1 (forallb_forall _ _) C (Z.to_nat i) ltac:(apply in_seq; lia)) as Ck. cbv beta in Ck.
    rewrite Z2Nat.id in Ck by lia.
    change (seg_rom _ (Z_to_bv 64 (A102_crc_empty + i))) with (seg_rom rsegs (Z_to_bv 64 (A102_crc_empty + i))).
    destruct (seg_rom rsegs (Z_to_bv 64 (A102_crc_empty + i))) as [b|]; [|discriminate].
    apply Z.eqb_eq in Ck. f_equal. apply bv_eq. rewrite Ck. reflexivity.
Qed.
End A.

(* ---- EMPTY_ZS / EMPTY_B at image A's asyms TfibB (Wcheck_reject_clean.v :114-137, at the #102 numbers) ---- *)
Lemma c102_in_of_existsb : forall (r : Z * Z) l,
  existsb (fun x => (fst x =? fst r) && (snd x =? snd r))%bool l = true -> In r l.
Proof.
intros [a n] l H. apply existsb_exists in H as ([a' n'] & Hin & Hb). apply andb_true_iff in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma c102_empty_zs_A : In (A102_crc_empty, 56) (as_zero_shadow AD2l.TfibB).
Proof. apply c102_in_of_existsb. vm_compute. reflexivity. Qed.
Lemma c102_empty_b_A : forall i, 0 <= i < 56 ->
  ~ Exists (in_zr (A102_crc_empty + i)) (as_owned_static AD2l.TfibB) /\
  ~ (as_errno AD2l.TfibB <= A102_crc_empty + i < as_errno AD2l.TfibB + 4).
Proof.
assert (C : forallb (fun i : nat => let a := A102_crc_empty + Z.of_nat i in
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r))%bool (as_owned_static AD2l.TfibB)) &&
  negb ((as_errno AD2l.TfibB <=? a) && (a <? as_errno AD2l.TfibB + 4)))%bool (seq 0 56) = true) by (vm_compute; reflexivity).
intros i Hi. rewrite forallb_forall in C. specialize (C (Z.to_nat i) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in C by lia. cbv zeta in C. apply andb_true_iff in C as [C1 C2]. apply negb_true_iff in C1, C2. split.
- intros Hx. apply Exists_exists in Hx as (r & Hr & Hz). unfold in_zr in Hz.
  assert (Hb : existsb (fun r => (fst r <=? A102_crc_empty + i) && (A102_crc_empty + i <? fst r + snd r))%bool
    (as_owned_static AD2l.TfibB) = true)
    by (apply existsb_exists; exists r; split; [exact Hr | apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia]).
  rewrite Hb in C1. discriminate.
- intros He. assert (Hb : ((as_errno AD2l.TfibB <=? A102_crc_empty + i) && (A102_crc_empty + i <? as_errno AD2l.TfibB + 4))%bool = true)
    by (apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite Hb in C2. discriminate.
Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive} {ci : CfImg}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the unit's standard image binding of B (owner a Theorem Labs lane); WITNESS: AD2l.TfibB_syms *)
Hypothesis TS : TfibSyms B.
(* the allocator relation implies h-mani-a8's ARcf (owner h-mani-a8); WITNESS: at ec_ARx, proj1 (below) *)
Hypothesis S9_CF : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> ARcf rsegs B ly S Hp W mem md.
(* the engine's laws (YCbqG.v AR_laws_x); at ec_ARx: YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (below) *)
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
(* CALLEE: the bcmp row with the memnorm keep (Reusable/YGcallMxmn.v:280); owner: the bcmp realizer's lane, a Theorem Labs lane
   (its po_memcmp_cf row with the nested bcmp row, Reusable/YGcallCmp.v:7-10) *)
Hypothesis BCMP : YGcallMxmn.abcmp_realizes_xm rsegs B ARx (A_prog_sigma AS___wrap_bcmp).
(* CALLEE: K0's text of fuzz_alloc_live (PRH_FnAlloc.v:137); its A' walk is a Theorem Labs lane's relocation *)
Hypothesis LIVE : tfuzz_alloc_live_specX (PI := prh_img_A) (PA := PI_prog_A) B ARx SK.

(* `empty` is one zero-shadow range of the image, at any B bound to image A *)
Lemma c102_empty_zs_B : In (A102_crc_empty, 56) (as_zero_shadow B).
Proof. rewrite (ts_zsh B TS), <- (ts_zsh _ AD2l.TfibB_syms). exact c102_empty_zs_A. Qed.
(* no byte of `empty` is a runtime-owned static or errno, at any B bound to image A *)
Lemma c102_empty_b_B : forall i, 0 <= i < 56 ->
  ~ Exists (in_zr (A102_crc_empty + i)) (as_owned_static B) /\ ~ (as_errno B <= A102_crc_empty + i < as_errno B + 4).
Proof.
rewrite (ts_owned B TS), (ts_errno B TS), <- (ts_owned _ AD2l.TfibB_syms), <- (ts_errno _ AD2l.TfibB_syms).
exact c102_empty_b_A.
Qed.
(* the shadow hull of `empty` is mapped in every ARx state: each of its bytes is shadow_addr a of an image address a,
   which YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover covers under ARcf (the bounds computed, not typed) *)
Lemma c102_empty_hull_B : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md ->
  shadow_hull_vis (aview rsegs (w_H W) mem) A102_crc_empty 56.
Proof.
intros ly S Hp W mem md HAR s Hs.
lazymatch type of Hs with ?lo <= _ < ?hi =>
  let l := eval vm_compute in lo in let h := eval vm_compute in hi in change lo with l in Hs; change hi with h in Hs end.
assert (Ea : shadow_addr ((s - SHADOW_OFF) * 8) = s)
  by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
rewrite <- Ea.
apply (YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover (ci := ci) (cp := cp) rsegs B Tfib_zero_shadow Tfib_const_shadow
  (@cf_img_lo CfImg_A) (@cf_img_top CfImg_A) AImgShadowVis.tfib_img_shadow_cover
  (AImgShadowVis.tfib_zsh_incl B (ts_zsh B TS)) (AImgShadowVis.tfib_const_shadow_incl B (ts_const B TS))
  ly S Hp W mem md _ (S9_CF _ _ _ _ _ _ HAR)).
lazymatch goal with |- ?lo <= _ < ?hi =>
  let l := eval vm_compute in lo in let h := eval vm_compute in hi in change lo with l; change hi with h end.
unfold SHADOW_OFF. lia.
Qed.

Theorem check_reject_clean_holds_A102 : tcheck_reject_clean_specX (PI := prh_img_A) (PA := PI_prog_A) B ARx SK.
Proof.
eapply (Wcrc102.check_reject_clean_holds102 (PA := PI_prog_A)).
all: first [exact c102_img_A | exact c102_empty_zs_B | exact c102_empty_b_B | exact c102_empty_hull_B | eassumption].
Qed.
End I.

(* ---- THE INSTANCE COROLLARY at the seam's instance (h-pre-b1's request, 18:27Z): B := AD2l.TfibB, the allocator
   relation h-pre-b1's ec_ARx (origin/cold/h-pre-b1-llvm102 lib/A/Ent102CutsA.v, Section E: ARcf /\ xs_placed_cf at
   the CfParams of the seam, here CfParamsPreset.CfParams_preset), PI := prh_img_A, PA := PI_prog_A. This file does not
   Require lib/A/Ent102CutsA.v (ec_ARx at :198), so the relation is written out with ec_ARx's body word for word (c102_ARx; ec_ARx at
   cp := CfParams_preset, B := AD2l.TfibB, PA := PI_prog_A unfolds to it, so the consumer applies the corollary by
   conversion). TS is AD2l.TfibB_syms, S9_CF is proj1, LAWS is YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf.
   Only BCMP (the bcmp realizer's lane, c-libc-stdio) and LIVE (K0's tfuzz_alloc_live_specX; h-w6rep-2's A'
   relocation) remain. THE SINK HEAD IS QUANTIFIED (forall SK), not fixed at preset_sink_head: that name lives in
   lib/A/PresetCfnA.v (:251), which did not build at the #102 pins build of e1edc1af2c (log of 2026-10-29T18:44:11Z,
   line 1945: PresetCfnA.v:417 applied prh_ledger to eleven arguments, the decff kit's has thirteen); on this tree it is in
   the library build (lib/dune) and PRH_Refute.v:47 Requires it. The corollary at every SK includes SK := preset_sink_head;
   no text's FP opens the sink (PRH_Base.v:794-795), so nothing in it depends on SK's value. ---- *)
Definition c102_ARx {rc : YM05.RunCeil} {ci : CfImg} (ly : alayout) (S : astate) (Hp : list Z) (W : world rsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  ARcf (cp := CfParamsPreset.CfParams_preset) rsegs AD2l.TfibB ly S Hp W mem md /\ xs_placed_cf ly S.

Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Theorem check_reject_clean_holds_A102_inst : forall SK : YI16.sink_head,
  YGcallMxmn.abcmp_realizes_xm rsegs AD2l.TfibB c102_ARx (A_prog_sigma AS___wrap_bcmp) ->
  tfuzz_alloc_live_specX (cp := CfParamsPreset.CfParams_preset) (PI := prh_img_A) (RL := RL) (PA := PI_prog_A)
    AD2l.TfibB c102_ARx SK ->
  tcheck_reject_clean_specX (cp := CfParamsPreset.CfParams_preset) (PI := prh_img_A) (RL := RL) (PA := PI_prog_A)
    AD2l.TfibB c102_ARx SK.
Proof.
intros SK BCMP LIVE.
exact (check_reject_clean_holds_A102 (cp := CfParamsPreset.CfParams_preset) (RL := RL) AD2l.TfibB c102_ARx SK
  AD2l.TfibB_syms
  (fun ly S Hp W mem md (H : c102_ARx ly S Hp W mem md) => proj1 H)
  (YGcallcf.AR_laws_x_xs (cp := CfParamsPreset.CfParams_preset) rsegs AD2l.TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParamsPreset.CfParams_preset) rsegs AD2l.TfibB))
  BCMP LIVE).
Qed.
End C.

(* ---- the Qed report (unit rule 16:5xZ): the elaborated statements, every implicit shown, and the assumptions ---- *)
Set Printing Implicit.
Unset Printing Notations.
Print check_reject_clean_holds_A102.
Print check_reject_clean_holds_A102_inst.
Unset Printing Implicit.
Set Printing Notations.
Print Assumptions check_reject_clean_holds_A102.
Print Assumptions check_reject_clean_holds_A102_inst.
