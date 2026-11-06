(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   KEY segment pfs_LK_holds: from the cut pf_LK (+0xf0, the return site of the recursive call) through slot i's key to
   the cut pf_LC (+0x130) (lib/B/Prog/pj_free_lcut.v pfs_LK), then the continuation premise.
     +0xf0  .. +0xf4   ASan check of v+32's cell (decided: shadow entry mkSHE 8 0 56)
     +0xf8  .. +0xfc   keys := v->keys; `beqz keys` decided by the seat: an ARRAY (ks = false, keys = 0, the chunk holds
                       the literal 0) goes to +0x130 with nothing freed (Dk = []); an OBJECT (ks = true) has keys >= 4096
     +0x100 .. +0x104  UBSan `bltu ~keys, 8 i`: REFUTED (keys + 8 i <= the keys block's end < 2 ^ 64; YI08.U_not)
     +0x108 .. +0x110  UBSan alignment of keys + 8 i: decided (atom 33 = keys + 8 i by the alias keys + s9, 8-aligned)
     +0x114 .. +0x124  ASan check of keys + 8 i: decided (shadow entry mkSHE 33 0 8: the slot is in the keys block, a
                       harness block live in the current ledger, so addressable)
     +0x128            a0 := keys[i] (atom 34, the key x of pj_keyR)
     +0x12c            jal fuzz_free (B 0x86b50), stepped concretely, then the instrumented text tfuzz_free_specO by
                       YCbqGcallW.v aj_call_xWR at callee window e1 = 0 (p = x; x = 0, or x's block (x, kx) in the
                       ledger and Dk = [(x, kx)]); its trace by prh_univ_closure_lit at F_pj_free / RT_fuzz_free (the
                       return site 0x86b54 is pi_ret_sites' first); PB from pf_safe along the order so far
   The walk's relation is wle' SEGS RZ_cf (pj_free_defs.v): the R runners (YC1fPx paj_run_xR / paj_run_to_xR,
   YSRrG.paj_branchR) and the R call rule, with the journal at it; the text concludes SRr' SEGS RZ_cf, its post the
   R form fpostmR at it, read as the call rule's callee post by YCbqGcallW.fpostW_x_of_apostR.
   After the call (pj_free_keep.v): the accounts (pfk_acct_null / pfk_acct_free, the order Fd ++ Dk), v's node
   (pfk_vnode), the slots i+1 .. n-1 (pfk_items), the frame (pfk_frame); the callee-saved registers by aregs_preserved.
   proves no function (kind: segment lemma). Section hypotheses: AR_laws_x at cf_head; ARx_frame_hull_vis (MARKED kit
   fact, YGcfFsVis.v; the instance's ARx_frame_hull_vis_cf_ok).
   Numerals: 300 / 304 (DERIVED: listing slot differences times 4, pj_free_lcut.v PJF_LC), 128 (LENGTH: pj_free's
   frame), 56 / 8 / 32 (LENGTH: struct pj, a key pointer, the keys field); 2 ^ 46 / 2 ^ 47 / 2 ^ 45 / 4096 (DERIVED
   bounds of the seat's atoms); atom numbers 32 .. 34 (the first atoms after the registers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI08.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_keep pj_free_lcut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the seated state at +0xf0: s0 = v (atom 8), s7 = the shadow offset (atom 23), s9 = 8 i (atom 25);
   s3 / s1 / s2 = v + 24 / v + 32 / v + 40, s11 / s4 / s6 their ASan cells, s5 = 56; v's keys word at v + 32: atom 32
   (an object, ks = true) or the literal 0 (an array); for an object also keys + 8 i (atom 33, an alias of keys + s9)
   and the key keys[i] there (atom 34) ---- *)
Definition pfk_cell (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) (SOff 23 0).
Definition pfk_sregs : list sv :=
  Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 20%bv (pfk_cell (SOff 8 32))) 21%bv (SLit 56))
    22%bv (pfk_cell (SOff 8 40))) 27%bv (pfk_cell (SOff 8 24)).
Lemma pfk_sregs_eq : pfk_sregs =
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    9%bv (SOff 8 32)) 18%bv (SOff 8 40)) 19%bv (SOff 8 24)) 20%bv (pfk_cell (SOff 8 32))) 21%bv (SLit 56))
    22%bv (pfk_cell (SOff 8 40))) 27%bv (pfk_cell (SOff 8 24)).
Proof. vm_compute. reflexivity. Qed.
Definition pfk_vhdr (ks : bool) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 32 (CVal 8 (if ks then SOff 32 0 else SLit 0))].
Definition pfk_kslot : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition pfk_mem (ks : bool) : smem := if ks then [pfk_vhdr true; pfk_kslot] else [pfk_vhdr false].
Definition pfk_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 0 (2 ^ 45) 3)].
Definition pfk_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 32 0) (SOff 25 0), SOff 33 0); (SAlu ALU_ADD (SOff 25 0) (SOff 32 0), SOff 33 0)].
Definition pfk_facts (ks : bool) : facts :=
  if ks then mkFacts ((32%nat, mkAF 4096 (2 ^ 47 - 4096) 4) :: (33%nat, mkAF 4096 (2 ^ 47 - 8) 3) :: pfk_atoms) []
    pfk_alias
  else mkFacts pfk_atoms [] [].
Definition pfk_ss (ks : bool) (pc : Z) : sstate := mkSS pc pfk_sregs (pfk_mem ks) None (pfk_facts ks).
Definition PFK_Bx : sv := SOff 23 0.
Definition PFK_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pfk_SH (ks : bool) : list shent := if ks then [mkSHE 8 0 56; mkSHE 33 0 8] else [mkSHE 8 0 56].
Ltac pfk_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Lemma pfk_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the segment's stretches store nothing: every region of their states is read-only (pj_free_seg_lc.v pfl_awr /
   pfl_mm) *)
Ltac pfk_awr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  unfold awr_ok; intros a (r & Hin & Ha); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]); destruct Hin.
Ltac pfk_mm HF M :=
  lazymatch type of HF with frame_of _ _ ?m ?m' =>
    assert (M : m' = m);
    [ apply functional_extensionality; let x := fresh "x" in intros x; apply HF;
      let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
      intros (r & Hin & Ha); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]); destruct Hin
    | ] end.

Ltac pfk_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
(* NoDup bookkeeping (stdpp's NoDup, the one pf_node states; pj_free_seg_loop.v pfl_nd_app / pfl_ndr / pfl_nd_perm /
   pfl_lam_now) *)
Lemma pfk_nd_app : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x HN H1 H2; [destruct H1|].
cbn [app] in HN. inversion HN as [|y' l' Hy HN']; subst.
destruct H1 as [<- | H1]; [apply Hy; apply list_elem_of_In; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
Lemma pfk_ndr : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l2.
Proof. induction l1 as [|y l1 IH]; intros l2 HN; [exact HN|]. cbn [app] in HN. inversion HN; subst. apply IH. assumption. Qed.
Lemma pfk_nd_perm : forall (l l' : list (Z * Z)), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros l l' HP HN. rewrite <- HP. exact HN. Qed.
Lemma pfk_lam_now : forall (L0 Fd Lam : list (Z * Z)) b, Permutation L0 (Fd ++ Lam) -> In b L0 -> ~ In b Fd -> In b Lam.
Proof.
intros L0 Fd Lam b HP Hb Hn. pose proof (Permutation_in _ HP Hb) as H2.
apply in_app_or in H2 as [H2|H2]; [contradiction | exact H2].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VISF : ARx_frame_hull_vis SEGS B ARx.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the footprint of harness blocks (pj_free_seg_loop.v pfl_inFP_hbl) *)
Lemma pfk_inFP_hbl : forall (D : list (Z * Z)) a k x, In (a, k) D ->
  a - cf_head <= x < a - cf_head + req_size (k + cf_head) -> inFP (ablocks_fp (prhPj_hbl D)) x.
Proof.
intros D a k x Hin Hx. exists (a - cf_head, a - cf_head + req_size (k + cf_head)). split; [|cbn [fst snd]; lia].
unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
Qed.
(* a return-address write keeps every callee-saved register *)
Lemma pfk_pres_ra : forall (rg : bvmap 5 word) ra, aregs_preserved rg (regupd rg 1%bv ra).
Proof.
intros rg ra r Hr. apply getr_other.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
repeat (destruct Hr' as [-> | Hr']; [pfk_regne|]); subst r; pfk_regne.
Qed.
(* the segment's environment: the registers, then keys, keys + 8 i and the key (atoms 32 .. 34) *)
Definition PFK_E (regs : bvmap 5 word) (keys ka x : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs [w64 keys; w64 ka; w64 x]).

(* what the seat needs of the keys block: an object's keys + 8 i is a readable, addressable slot holding the key, apart
   from v's node and from the shadow; an array's keys word is 0 *)
Definition pfk_kfacts (ks : bool) (W : world SEGS) (mem : word -> option byte) (v keys i x : Z) : Prop :=
  if ks then
    4096 <= keys <= 2 ^ 47 - 4096 /\ keys mod 16 = 0 /\ keys + 8 * i + 8 <= 2 ^ 47 /\
    rd_u64 SEGS (rdW W mem) (keys + 8 * i) x /\
    range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (keys + 8 * i) 8 /\
    (forall y, keys + 8 * i <= y < keys + 8 * i + 8 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) /\
    (keys + 8 * i + 8 <= v \/ v + 56 <= keys + 8 * i)
  else keys = 0.

Lemma pfk_seat : forall en i (ks : bool) keys x (W : world SEGS) regs mem pc,
  pf_vregs en regs -> pf_lregs en regs i ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= fe_v en <= 2 ^ 47 - 64 -> fe_v en mod 8 = 0 -> 0 <= i < 2 ^ 42 ->
  rd_u64 SEGS (rdW W mem) (fe_v en + 32) keys ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fe_v en) 56 -> amem_range (fe_v en) 56 ->
  pfk_kfacts ks W mem (fe_v en) keys i x ->
  (st_ok_pi SEGS VAL (PFK_E regs keys (keys + 8 * i) x) (pfk_ss ks pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
   sh_ok SEGS PFK_Bx (pfk_SH ks) (PFK_E regs keys (keys + 8 * i) x) (mrestrict (w_H W) mem)) /\
  regs_ok (PFK_E regs keys (keys + 8 * i) x) pfk_sregs regs.
Proof.
intros en i ks keys x W regs mem pc HVR HLR Hsp Hal Hv Hv8 Hi Hkeys Hra Hamr HKF.
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HLR as (R20 & R21 & R24 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v := fe_v en) in *.
set (E := PFK_E regs keys (keys + 8 * i) x).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 keys; w64 (keys + 8 * i); w64 x] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (E32 : ew E 32 = w64 keys) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = w64 (keys + 8 * i)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = w64 x) by exact (EX 2%nat ltac:(lia)).
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = v + c).
{ intros c Hc. apply (U_atom_off E 8 v c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U23 : U E (SOff 23 0) = SHADOW_OFF).
{ apply (U_atom E 23 SHADOW_OFF); [rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | unfold SHADOW_OFF; lia]. }
assert (U25 : U E (SOff 25 0) = 8 * i).
{ apply (U_atom E 25 (8 * i)); [rewrite (Er 25%nat 25%bv) by (first [lia | reflexivity]); exact R25 | lia]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Er 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v).
{ rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]). rewrite R8. apply unsigned_lit_small. lia. }
assert (Hcell : forall c, 0 <= c <= 56 -> U E (pfk_cell (SOff 8 c)) = (v + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pfk_cell. apply pfg_U_cell; [apply U8; lia | exact U23 | lia]. }
assert (HRG : regs_ok E pfk_sregs regs).
{ rewrite pfk_sregs_eq.
  apply regs_ok_pin; [|pfk_regne|rewrite R27, pfk_denot_U, Hcell by lia; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R22, pfk_denot_U, Hcell by lia; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R21, pfk_denot_U, U_SLit; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R20, pfk_denot_U, Hcell by lia; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R19, pfk_denot_U, U8 by lia; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R18, pfk_denot_U, U8 by lia; reflexivity].
  apply regs_ok_pin; [|pfk_regne|rewrite R9, pfk_denot_U, U8 by lia; reflexivity].
  unfold E, PFK_E. apply regs_ok_Eimg_Ereg. }
clearbody E.
split; [|exact HRG].
assert (HAT : atoms_ok E pfk_atoms).
{ unfold pfk_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv.
  rewrite (Er 23%nat 23%bv), (Er 25%nat 25%bv) by (first [lia | reflexivity]).
  rewrite R23, R25. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal; try exact Hv8; try lia.
  all: Z.div_mod_to_equations; lia. }
assert (SH8 : shent_ok SEGS PFK_Bx E (mrestrict (w_H W) mem) (mkSHE 8 0 56)).
{ apply (shent_ok_of_range SEGS (w_H W) mem E PFK_Bx 8 v 56 v 0 56 Hra).
  + unfold PFK_Bx. exact U23.
  + rewrite U8 by lia. lia.
  + lia. + lia.
  + intros y Hy. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia. }
destruct ks; cbn [pfk_kfacts] in HKF.
- (* an object: the keys slot *)
  destruct HKF as (Hk1 & Hk16 & Hkc & Hx & Hkra & Hkapp & Hkv).
  assert (Uk : U E (SOff 32 0) = keys) by (apply (U_atom E 32 keys); [exact E32 | lia]).
  assert (Uka : U E (SOff 33 0) = keys + 8 * i) by (apply (U_atom E 33 (keys + 8 * i)); [exact E33 | lia]).
  assert (Uka' : bv_unsigned (ew E 33) = keys + 8 * i) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  + rewrite restrict_mkst_fx. unfold pfk_ss, pfk_mem, pfk_facts.
    apply pa_entry_st_ok_full; [exact HRG | vm_compute; reflexivity | | | ].
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- unfold region_ok, pfk_vhdr.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         apply Forall_cons; [|apply Forall_nil].
         apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 32 0) keys);
           [rewrite pfk_denot_U, Uk; reflexivity | cbn; exact (proj1 Hkeys) | cbn; lia | exact (proj2 Hkeys)].
      -- unfold region_ok, pfk_kslot.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uka'.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         apply Forall_cons; [|apply Forall_nil].
         apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) x);
           [rewrite pfk_denot_U, (U_atom E 34 x); [reflexivity | exact E34 | exact (proj1 Hx)]
           | cbn; exact (proj1 Hx) | cbn; lia | rewrite Z.add_0_r; exact (proj2 Hx)].
    * cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, pfk_vhdr, pfk_kslot, base_val.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite Uv, Uka'. split; [split; [lia | exact I] | split; [exact I | exact I]].
    * split; [|split; [exact I|]].
      -- cbn [atoms_ok]. split; [|split; [|exact HAT]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
         ++ rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16. lia.
         ++ rewrite Uka'. change (2 ^ 3) with 8. split; [lia|]. split; [Z.div_mod_to_equations; lia | lia].
      -- unfold pfk_alias. cbn [alias_ok].
         split; [|split; [|exact I]]; apply U_inj; rewrite pfg_U_add, Uk, U25, Uka; rewrite Z.mod_small by lia; lia.
  + unfold sh_ok, pfk_SH. constructor; [exact SH8|]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem E PFK_Bx 33 (keys + 8 * i) 8 (keys + 8 * i) 0 8 Hkra).
    * unfold PFK_Bx. exact U23.
    * exact Uka.
    * lia. * lia.
    * intros y Hy. apply Hkapp. lia.
- (* an array: keys = 0 *)
  subst keys.
  split.
  + rewrite restrict_mkst_fx. unfold pfk_ss, pfk_mem, pfk_facts.
    apply pa_entry_st_ok_full; [exact HRG | vm_compute; reflexivity | | | ].
    * apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, pfk_vhdr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 32 8 (SLit 0) 0);
        [rewrite pfk_denot_U, U_SLit; reflexivity | cbn; lia | cbn; lia | exact (proj2 Hkeys)].
    * cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    * split; [exact HAT | split; exact I].
  + unfold sh_ok, pfk_SH. constructor; [exact SH8 | constructor].
Qed.

(* ---- the registers a run keeps, and those a call keeps ---- *)
Lemma pfk_vlregs : forall en i E ss (ms : machine_state) regs (H : word -> bool),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> regs_ok E pfk_sregs regs ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get pfk_sregs r))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] = true ->
  pf_vregs en regs -> pf_lregs en regs i ->
  pf_vregs en (ms_regs ms) /\ pf_lregs en (ms_regs ms) i /\ spZ (ms_regs ms) = spZ regs /\
  getr (ms_regs ms) 3 = getr regs 3 /\ getr (ms_regs ms) 4 = getr regs 4.
Proof.
intros en i E ss ms regs H HS HR Hb HV HL.
assert (K : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
  26%bv; 27%bv] -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), (HR r).
  f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) Hb r Hr). }
pose proof HV as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HL as (R20 & R21 & R24 & R25 & R26 & R27).
unfold pf_vregs, pf_lregs, spZ.
rewrite !K by (cbn [In]; repeat first [left; reflexivity | right]).
repeat split; assumption.
Qed.
Lemma pfk_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Lemma pfk_pres_vlregs : forall en i rg rg2, aregs_preserved rg rg2 -> pf_vregs en rg -> pf_lregs en rg i ->
  pf_vregs en rg2 /\ pf_lregs en rg2 i /\ spZ rg2 = spZ rg /\ getr rg2 3 = getr rg 3 /\ getr rg2 4 = getr rg 4.
Proof.
intros en i rg rg2 HP HV HL.
pose proof HV as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HL as (R20 & R21 & R24 & R25 & R26 & R27).
unfold pf_vregs, pf_lregs, spZ.
rewrite !(pfk_pres rg rg2 _ HP) by pfk_cs.
repeat split; assumption.
Qed.

(* ---- two distinct harness blocks: the user bytes of one miss the allocator block of the other
   (pj_free_seg_loop.v pfl_hb_apart) ---- *)
Lemma pfk_hb_apart : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> (a, k) <> (a', k') -> a <= x < a + k ->
  ~ (a' - cf_head <= x < a' - cf_head + req_size (k' + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x HAR HL H1 H2 Hne Hx Hx'.
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL H1) as (Hk0 & Ha0 & Hak & _ & Hab & _).
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL H2) as (Hk0' & Ha0' & Hak' & _ & Hab' & _).
assert (Hne' : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)).
{ intros E. injection E as E1 E2. apply Hne. f_equal; lia. }
pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hab' Hne') as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq1 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq1) as [_ Hr1].
lia.
Qed.

(* ---- v's node misses the allocator block of every harness block of D in the ledger
   (pj_free_seg_loop.v pfl_v_apart) ---- *)
Lemma pfk_v_apart : forall en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  pf_vnode B en nd ly S Lam W mem -> ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> YM05.alloc_ceiling <= fe_sp0 en ->
  In (a, k) Lam -> In (a, k) (fe_D en) -> a - cf_head <= x < a - cf_head + req_size (k + cf_head) ->
  ~ (fe_v en <= x < fe_v en + 56).
Proof.
intros en nd ly S Hp W mem md Lam peak cnt fail ran most own a k x HVN HAR HL Hceil Hin HinD Hx Hv.
pose proof HVN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hplace).
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & _).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq2 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq2) as [_ Hr1].
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & _).
destruct Hplace as [(a' & k' & Hin' & HnD & Ha' & Hk') | [(b & m & Hb & Hnl & Hb1 & Hb2) |
  [(cid & pos & Hf & Hf1 & Hf2) | (Hw1 & Hw2)]]].
- assert (Hne : (a', k') <> (a, k)) by (intros E; rewrite E in HnD; exact (HnD HinD)).
  exact (pfk_hb_apart ly S Hp W mem md Lam peak cnt fail ran most own a' k' a k x HAR HL Hin' Hin Hne ltac:(lia) Hx).
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
  { intros E. injection E as E1 E2. apply Hnl.
    replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hb Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. assert (Hrq5 : 0 <= m) by lia. pose proof (req_size_pos (m) Hrq5) as [_ Hr2]. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* ---- a harness block's user bytes: addressable, in application memory (pj_free_seg_loop.v pfl_hb_vis) ---- *)
Lemma pfk_hb_vis : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x n,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  a <= x -> x + n <= a + k -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\ amem_range x n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x n HAR HL Hin H1 H2 Hn.
destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HL Hin) as (Hk0 & Ha0 & Hak & _ & Hab & Hhp).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hrq3 : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hrq3) as [_ Hr1].
destruct (alx_hshadow SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab Hhp) as (Hbs & _).
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hcb & Happ & _).
replace (a - cf_head + cf_head) with a in Hbs by lia.
split; [eapply block_shadow_range; [exact Hbs | lia | lia]|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold in_app, amem_range, kLowShadowBeg, ASAN_CEIL in *. lia.
Qed.

Theorem pfs_LK_holds : forall PB FX CTX0 d',
  pf_texts (SK := SK) B ARx PB FX -> pfs_LK (SK := SK) B ARx PB FX CTX0 d'.
Proof.
intros PB FX CTX0 d' TXT en nd i ly S Hp W regs mem md k HPRE HND HLK KLC.
destruct TXT as (FFREE & _).
pose proof HLK as (En & Hi & HFR & HSP & HVR & HLR & Fd & Lam & Dk & Dr & Fr & HAC & HVN & HPD & HKEY & HIT).
pose proof HFR as (HJ & HWIN & Hsp & HSV & HPRES & H3 & H4 & HROD & HMN).
pose proof HVR as (R8 & R9 & R18 & R19 & R23 & R22).
pose proof HLR as (R20 & R21 & R24 & R25 & R26 & R27).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HPRE as (HFPRE0 & HUNIV & _ & _ & HWIN0 & _ & HSAFE0 & HLED0).
pose proof (HSAFE0 ltac:(lia)) as HSAFE.
pose proof HFPRE0 as (HAFN0 & HROD0 & HSTKHI0).
(* fpre's FRM0-ENTRY conjunct: pj_free runs no float instruction, so its callee gets pj_free's own *)
pose proof HFPRE0 as (_ & _ & _ & _ & HFRM0).
pose proof HAFN0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HND as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
assert (Hceil0 : YM05.alloc_ceiling <= fe_sp0 en) by (unfold fe_sp0 in *; rewrite ESTK in *; lia).
(* the kids block: n slots fit in it, so i is small *)
assert (Hkk : exists kk, In (fn_kids nd, kk) (fe_Lam en) /\ 56 * fn_n nd <= kk /\ fn_Dk nd = [(fn_kids nd, kk)] /\
  4096 <= fn_kids nd /\ fn_kids nd + kk <= YM05.alloc_ceiling).
{ destruct HKIDSn as [(_ & Hn0 & _) | (kk & Hin & Hkn & HDk)]; [lia|].
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HLED0 Hin) as (Hk0 & Ha0 & Hak & Ha16 & _).
  exists kk. repeat split; first [assumption | lia]. }
destruct Hkk as (kk & Hkkin & Hkkn & HDkk & Hkk4 & Hkkc).
assert (Hi42 : 0 <= i < 2 ^ 42) by (clear - Hi Hkkn Hkk4 Hkkc C1; lia).
assert (Hsp1 : spZ regs = fe_sp0 en - 128) by (rewrite Hsp; unfold fe_sp1, PJF_FR; lia).
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0).
{ rewrite Hsp1. unfold fe_sp0 in *. rewrite ESTK in *. split; [lia|]. Z.div_mod_to_equations. lia. }
unfold pf_cfg, SRr'.
set (R := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS RZ_cf).
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (RUNTO := @paj_run_to_xR fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fx) (rc := rc) (L := B_prog_listing) (PI := PA) R).
destruct HKEYSn as [(Ekeys & Eks & EDy) | (Eks & ky & Hky & Hkyn & EDy)].
- (* ======== an array: keys = NULL, the beqz goes to +0x130 ======== *)
  rewrite Eks in HKEY. cbn [pj_keyR] in HKEY. subst Dk.
  destruct (pfk_seat en i false (fn_keys nd) 0 W regs mem PJF_LK HVR HLR (proj1 Hspr) (proj2 Hspr) ltac:(lia) Hv8 Hi42
    Hkeys Hvra Hamr Ekeys) as [[HS SHOK] HRG].
  set (E := PFK_E regs (fn_keys nd) (fn_keys nd + 8 * i) 0) in HS, SHOK, HRG.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, PFK_E; apply Eimg_env).
  clearbody E.
  paj_run_to_tok_x RUNTO HS HJ SHOK PFK_Bspan PJF_LC.
  { unfold awr_ok. intros a (r & Hin & Ha). unfold pfk_ss, pfk_mem in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | []]. unfold pfk_vhdr in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  (* the run stores nothing: the memory is the cut's *)
  assert (Em : ms_mem msA = mem).
  { apply functional_extensionality. intros a. apply HF. intros (r & Hin & Ha). unfold pfk_ss, pfk_mem in Hin.
    cbn [ss_mem In] in Hin. destruct Hin as [<- | []]. unfold pfk_vhdr in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  destruct (pfk_vlregs en i E _ msA regs _ HS HRG ltac:(vm_compute; reflexivity) HVR HLR)
    as (HVR1 & HLR1 & Esp1 & E31 & E41).
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) ?mm _; cfg_model := ?dd |} _ =>
    replace pc with PJF_LC by (vm_compute; reflexivity); set (md1 := dd) in * end.
  rewrite Em in HJ |- *.
  apply (KLC ly S Hp W (ms_regs msA) mem md1 k).
  split; [exact En|]. split; [exact Hi|].
  split.
  { split; [exact HJ|]. split; [exact HWIN|]. split; [unfold spZ in Esp1 |- *; rewrite Esp1; exact Hsp|].
    split; [exact HSV|]. split; [exact HPRES|]. split; [rewrite E31; exact H3|]. split; [rewrite E41; exact H4|].
    split; [exact HROD | exact HMN]. }
  split; [exact HSP|]. split; [exact HVR1|]. split; [exact HLR1|].
  exists Fd, Lam, Dr, Fr. split; [exact HAC|]. split; [exact HVN|]. split; [exact HPD|]. exact HIT.
- (* ======== an object: keys <> NULL ======== *)
  assert (HyD : In (fn_keys nd, ky) (fe_D en)).
  { apply (Permutation_in _ (Permutation_sym HPDn)). rewrite EDy, !in_app_iff. cbn [In]. tauto. }
  assert (ND : NoDup (Fd ++ Dk ++ Dr ++ fn_own nd)) by exact (pfk_nd_perm _ _ HPD HNDD).
  assert (NDr : NoDup (Dk ++ Dr ++ fn_own nd)) by exact (pfk_ndr _ _ ND).
  assert (HinD : forall b, In b (Fd ++ Dk ++ Dr ++ fn_own nd) -> In b (fe_D en))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPD) Hb)).
  assert (HyOwn : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite EDy, !in_app_iff; cbn [In]; tauto).
  assert (HkOwn : In (fn_kids nd, kk) (fn_own nd)) by (unfold fn_own; rewrite HDkk; left; reflexivity).
  assert (HyLam : In (fn_keys nd, ky) Lam).
  { apply (pfk_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
    apply (pfk_nd_app Fd _ _ ND Hf). rewrite !in_app_iff. tauto. }
  assert (HkLam : In (fn_kids nd, kk) Lam).
  { apply (pfk_lam_now (fe_Lam en) Fd Lam _ HPL Hkkin). intros Hf.
    apply (pfk_nd_app Fd _ _ ND Hf). rewrite !in_app_iff. tauto. }
  assert (HownDk : forall b, In b (fn_own nd) -> ~ In b Dk).
  { intros b Ho Hk. apply (pfk_nd_app Dk (Dr ++ fn_own nd) b NDr Hk). apply in_or_app; right; exact Ho. }
  assert (HDrDk : forall b, In b Dr -> ~ In b Dk).
  { intros b Hr Hk. apply (pfk_nd_app Dk (Dr ++ fn_own nd) b NDr Hk). apply in_or_app; left; exact Hr. }
  assert (HDkD : forall b, In b Dk -> In b (fe_D en)).
  { intros b Hb. apply HinD. apply in_or_app; right; apply in_or_app; left; exact Hb. }
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HyLam) as (Hky0 & Hk4 & Hkc & Hk16 & Hyab & Hyhp).
  rewrite Eks in HKEY. cbn [pj_keyR] in HKEY. destruct HKEY as (x & Hxu & Hxc).
  (* the key: NULL (no block) or a harness block of the ledger, one of D's *)
  assert (HXK : exists kx, (x = 0 /\ Dk = []) \/ (x <> 0 /\ In (x, kx) Lam /\ Dk = [(x, kx)])).
  { destruct Hxc as [(Ex & EDk) | (kx & Hkx & EDk)]; [exists 0; left; split; assumption|].
    exists kx. right. unfold prh_lin in Hkx.
    destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkx) as (_ & Hx4 & _).
    split; [lia|]. split; assumption. }
  destruct HXK as (kx & HXK). clear Hxc.
  assert (HDkL : forall b, In b Dk -> In b Lam).
  { intros b Hb. destruct HXK as [(_ & EDk) | (_ & Hkx & EDk)]; rewrite EDk in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. exact Hkx. }
  destruct (pfk_hb_vis ly S Hp W mem md Lam _ _ _ _ _ _ (fn_keys nd) ky (fn_keys nd + 8 * i) 8 HAR HLED HyLam
    ltac:(lia) ltac:(lia) ltac:(lia)) as (Hkra & Hkamr).
  assert (Hkapp : forall y, fn_keys nd + 8 * i <= y < fn_keys nd + 8 * i + 8 ->
    ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
  { intros y Hy. unfold amem_range in Hkamr. unfold SHADOW_OFF. lia. }
  pose proof (HAPD (fn_keys nd, ky) (fn_keys nd + 8 * i) HyD ltac:(unfold pj_holdsR; cbn [fst snd]; lia)) as A1.
  pose proof (HAPD (fn_keys nd, ky) (fn_keys nd + 8 * i + 7) HyD ltac:(unfold pj_holdsR; cbn [fst snd]; lia)) as A2.
  destruct (pfk_seat en i true (fn_keys nd) x W regs mem PJF_LK HVR HLR (proj1 Hspr) (proj2 Hspr) ltac:(lia) Hv8 Hi42
    Hkeys Hvra Hamr) as [[HS SHOK] HRG].
  { cbn [pfk_kfacts]. split; [lia|]. split; [exact Hk16|]. split; [lia|]. split; [exact Hxu|].
    split; [exact Hkra|]. split; [exact Hkapp|]. lia. }
  set (E := PFK_E regs (fn_keys nd) (fn_keys nd + 8 * i) x) in HS, SHOK, HRG.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, PFK_E; apply Eimg_env).
  assert (E32 : ew E 32 = w64 (fn_keys nd)).
  { unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E34 : ew E 34 = w64 x).
  { unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  assert (U25 : U E (SOff 25 0) = 8 * i).
  { apply (U_atom E 25 (8 * i)); [|lia]. unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 25 25%bv) by reflexivity. exact R25. }
  clearbody E.
  (* +0xf0 .. +0x100: the ASan check of v+32 and keys <> NULL are decided; stop at the UBSan `bltu ~keys, 8 i` *)
  paj_run_to_tok_x RUNTO HS HJ SHOK PFK_Bspan (PJF_PC + 300); [pfk_awr|].
  pfk_mm HF M1. clear HF HFr. rename HG into G1.
  (* +0x104: UBSan `bltu ~keys, 8 i`: refuted (keys + 8 i < 2 ^ 64) *)
  psrr_branch_tok RUN BR HS SHOK PFK_Bspan.
  { exfalso. rewrite branch_ltu_U, (YI08.U_not E 32 (fn_keys nd) E32 ltac:(lia)), U25 in Hc.
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* +0x108 .. +0x128: the UBSan alignment check (keys + 8 i, atom 33), its ASan check (shadow entry mkSHE 33 0 8),
     the load of the key (atom 34); stop at the `jal fuzz_free` (+0x12c) *)
  paj_run_to_tok_x RUNTO HS HJ SHOK PFK_Bspan (PJF_PC + 300); [pfk_awr|].
  pfk_mm HF M2. clear HF HFr. rename HG into G2.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  pfg_reg HS (10%bv : bv 5) Q10.
  destruct (pfk_vlregs en i E _ msA regs _ HS HRG ltac:(vm_compute; reflexivity) HVR HLR)
    as (HVR1 & HLR1 & Esp1 & E31 & E41).
  pmkst HS.
  rewrite M2, M1 in HJ |- *.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _; cfg_model := ?dd |} _ =>
    replace pc with (PJF_PC + 300) by (vm_compute; reflexivity); set (rg0 := rg) in *; set (md0 := dd) in * end.
  (* ---- +0x12c: jal fuzz_free ---- *)
  pfg_fd (PJF_PC + 300) Hl1 Hd1.
  eapply (pfg_step_jal fx R W rg0 mem md0 _ (PJF_PC + 300) _ _ _ (1%bv : bv 5) (Z_to_bv 64 (BASE + PJF_LC))
    (Z_to_bv 64 (SIGMA AS_fuzz_free)) Hl1 Hd1).
  { vm_compute. reflexivity. }
  { apply bv_eq. vm_compute. reflexivity. }
  { apply bv_eq. vm_compute. reflexivity. }
  { apply bv_eq. vm_compute. reflexivity. }
  intros X1.
  pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hsegs R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ)
    as HJ1.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ => set (regsc := r) in *; set (mdc := m) in * end.
  (* the call state's registers *)
  destruct (pfk_pres_vlregs en i rg0 regsc (pfk_pres_ra rg0 _) HVR1 HLR1) as (HVRc & HLRc & Espc & E3c & E4c).
  assert (HSPC : spZ regsc = fe_sp1 en) by (rewrite Espc, Esp1; exact Hsp).
  assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite E3c, E31, H3; exact Hgp0).
  assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite E4c, E41, H4; exact Htp0).
  assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + PJF_LC)) by (unfold regsc; apply getr_same; pfk_regne).
  assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + PJF_LC))).
  { apply (YC1fP.ret_ok_codeptr_v (PI := PA)); [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity |].
    vm_compute. reflexivity. }
  assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + PJF_LC))) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
  { unfold s0Z. pose proof HVRc as (R8c & _). rewrite R8c. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (HSPO : spZ regsc = fe_sp0 en + fe_d en + (-128 - fe_d en)) by (rewrite HSPC; unfold fe_sp1, PJF_FR; lia).
  assert (Hal' : (-128 - fe_d en) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hneg : -128 - fe_d en <= 0) by lia.
  assert (HSTKF : 0 <= STK_fuzz_free) by (rewrite pfg_stk_ff; lia).
  assert (Hbud : STK_fuzz_free - (-128 - fe_d en) <= STK_pj_free (fe_n en) + fe_d en)
    by (rewrite pfg_stk_ff, ESTK; lia).
  assert (He0 : 0 <= 0) by lia.
  assert (Hetop : -128 - fe_d en + 0 <= 0) by lia.
  assert (HA10 : getr regsc 10 = w64 x).
  { unfold regsc. rewrite getr_other by pfk_regne. rewrite Q10, pfk_denot_U, (U_atom E 34 x E34 (proj1 Hxu)).
    reflexivity. }
  (* the free's trace: [pc0] or pc0 and the return site +0x130 (B 0x86b54), one of pj_free's fuzz_free sites: a FIXED
     trace (prh_univ_closure's clauses 1-2), the premise of the instrumented text (PjFreeCommon.v tfuzz_free_specO) *)
  assert (HTRf : In (call_trace ly (pc_free_ra0 (as_code B)) regsc []) (u_fix (as_universe B))).
  { unfold call_trace. destruct (frame0_ok ly regsc).
    - change (In (prh_trace (prh_pc0 B RT_fuzz_free) (raZ regsc) []) (u_fix (as_universe B))).
      apply (prh_univ_closure_lit B CTX0 F_pj_free RT_fuzz_free (raZ regsc) HUNIV).
      unfold raZ. rewrite HRA1. vm_compute. left. reflexivity.
    - destruct HUNIV as (HU1 & _). exact (HU1 RT_fuzz_free). }
  (* PB at the call: the order so far reached it *)
  assert (HPBS : PB S) by exact (pf_safe_here FX PB _ ly S (pf_safe_after FX PB _ _ _ _ _ _ HSAFE HRE)).
  assert (HPKX : x = 0 \/ In (x, kx) Lam) by (destruct HXK as [(Ex & _) | (_ & Hkx & _)]; [left | right]; assumption).
  (* the callee's footprint: the key's block, or nothing *)
  set (FP1 := if x =? 0 then [] else ablocks_fp [(x - cf_head, kx + cf_head)]).
  assert (HFPD : forall y, inFP FP1 y ->
    exists a' k', In (a', k') Dk /\ a' - cf_head <= y < a' - cf_head + req_size (k' + cf_head)).
  { intros y Hy. unfold FP1 in Hy. destruct HXK as [(Ex & EDk) | (Ex & Hkx & EDk)].
    - rewrite Ex, Z.eqb_refl in Hy. destruct Hy as (r & Hr & _). destruct Hr.
    - apply Z.eqb_neq in Ex. rewrite Ex in Hy. destruct Hy as (r & Hr & Hry).
      cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hry.
      exists x, kx. split; [rewrite EDk; left; reflexivity | lia]. }
  assert (Hv0 : (fe_v en =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (HSH : spZ regsc + 64 <= ly_stk_hi ly) by (rewrite HSPC, Eshi; unfold fe_sp1, PJF_FR, fe_sp0 in *; lia).
  (* fpre's return-address bound: the jal's return pc +0x130, a text literal below the ceiling *)
  assert (HRAc : raZ regsc < YM05.alloc_ceiling).
  { pose proof asan_consts as (C1' & _). unfold raZ. rewrite HRA1. eapply Z.lt_le_trans; [|apply (proj1 C1')].
    apply Z.ltb_lt. vm_compute. reflexivity. }
  eapply (SRrG_bind SEGS R Rt).
  { eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W regsc mem (SIGMA AS_fuzz_free)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STK_fuzz_free 0 FP1 (-128 - fe_d en) (Z_to_bv 64 (BASE + PJF_LC)) [] _
      HJ1 HSPO Hal' Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
    - (* the callee: the instrumented fuzz_free text at the key x (SRr' SEGS RZ_cf, its post fpostmR at R) *)
      intros HPRE1 HWIN1.
      eapply (SRrG_mono SEGS R); [exact (FFREE (fe_most en) (fe_own en) ly S Hp W regsc mem mdc [] x kx Lam (fe_peak en)
        (fe_cnt en) (fe_fail en) (fe_ran en) (conj HPRE1 (conj HROD (conj HSH (conj HRAc HFRM0)))) HROOM HPBS HTRf
        HA10 HPKX HLED)|].
      intros W' c' _ HQ. exact (fpostW_x_of_apostR (SK := SK) SEGS B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ HQ).
    - (* the footprint: the key's block, one of D's *)
      intros a Ha. left. destruct (HFPD a Ha) as (a' & k' & HinDk & Hr).
      unfold fe_FP. rewrite Hv0. apply inFP_cons. right. exact (pfk_inFP_hbl _ a' k' a (HDkD _ HinDk) Hr). }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP2 & HK).
  cbv beta in HK. unfold fQmn in HK. destruct HK as ((HFX & HROOM2 & HKK) & HMN2).
  apply (KLC ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
  (* ---- the accounts after the free ---- *)
  assert (POST : exists Lam2, pf_acct B FX en ly2 S2 Hp2 W2 mem2 (Fd ++ Dk) (Fr ++ fn_own nd) Lam2 /\
    prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) /\
    (forall b, In b Lam -> ~ In b Dk -> In b Lam2) /\ (forall b, In b Lam2 -> In b Lam) /\
    (forall b, In b (ablocks B ly S) -> ~ In b (ablocks B ly2 S2) ->
       exists a k0, In (a, k0) Dk /\ b = (a - cf_head, k0 + cf_head))).
  { destruct HXK as [(Ex & EDk) | (Ex & Hkx & EDk)].
    - (* fuzz_free (NULL) *)
      subst Dk. rewrite Ex, Z.eqb_refl in HFX.
      destruct HKK as [(_ & EHp & Eab & HLED2) | (Hx0 & _)]; [|exfalso; exact (Hx0 Ex)].
      exists Lam. rewrite app_nil_r. split; [|split; [exact HLED2|]].
      + exact (pfk_acct_null B FX en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam ly2 S2 Hp2 W2 mem2 HAC HFX HROOM2 Eab HLED2).
      + split; [intros b Hb _; exact Hb|]. split; [intros b Hb; exact Hb|].
        intros b Hb Hn. rewrite Eab in Hn. contradiction.
    - (* the key's block *)
      subst Dk. pose proof Ex as Ex'. apply Z.eqb_neq in Ex'. rewrite Ex' in HFX.
      destruct HKK as [(Hx0 & _) | (_ & EHp & Eab & l1 & l2 & ELam & HLED2)]; [exfalso; exact (Ex Hx0)|].
      exists (l1 ++ l2). split; [|split; [exact HLED2|]].
      + exact (pfk_acct_free B FX en ly S Hp W mem Fd (x, kx) (Fr ++ fn_own nd) Lam ly2 S2 Hp2 W2 mem2 l1 l2 HAC HFX
          HROOM2 ELam Eab HLED2).
      + split.
        { intros b Hb Hn. rewrite ELam in Hb. apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | [<- | Hb]]; [left; exact Hb | exfalso; apply Hn; left; reflexivity | right; exact Hb]. }
        split.
        { intros b Hb. rewrite ELam. apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | Hb]; [left; exact Hb | right; right; exact Hb]. }
        intros b Hb Hn. destruct Eab as (b1 & b2 & Eb1 & Eb2). rewrite Eb1 in Hb. rewrite Eb2 in Hn.
        apply in_app_or in Hb. destruct Hb as [Hb | [<- | Hb]].
        * exfalso. apply Hn. apply in_or_app. left. exact Hb.
        * exists x, kx. split; [left; reflexivity | reflexivity].
        * exfalso. apply Hn. apply in_or_app. right. exact Hb. }
  destruct POST as (Lam2 & HAC2 & HLED2 & HL2a & HL2b & HAB).
  (* ---- what the call kept ---- *)
  pose proof (ajxR_ar HJ1) as HARc.
  replace (fe_sp0 en + fe_d en + (-128 - fe_d en) + 0) with (fe_sp1 en + 0) in HJc by (unfold fe_sp1, PJF_FR; lia).
  assert (HFRc : pf_frameR (SK := SK) B ARx R en ly S Hp W regsc mem mdc k).
  { split; [exact HJ1|]. split; [exact HWIN|]. split; [exact HSPC|]. split; [exact HSV|]. split; [exact HPRES|].
    split; [rewrite E3c, E31; exact H3|]. split; [rewrite E4c, E41; exact H4|]. split; [exact HROD | exact HMN]. }
  destruct (pfk_pres_vlregs en i regsc regs2 HP2 HVRc HLRc) as (HVR2 & HLR2 & Esp2 & E32' & E42').
  assert (HSINK : ~ YI16.sink_open_fp FP1).
  { unfold FP1. destruct (x =? 0) eqn:Ex0.
    - exact (sink_closed_ablocks_fp [] (Forall_nil _)).
    - apply sink_closed_ablocks_fp. constructor; [|constructor]. cbn [fst].
      destruct HXK as [(Ex & _) | (_ & Hkx & _)]; [apply Z.eqb_neq in Ex0; contradiction|].
      destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkx) as (_ & Hx4 & _). lia. }
  assert (HFPblk : forall y, inFP FP1 y -> exists b m, In (b, m) (ablocks B ly S) /\ b <= y < b + req_size m).
  { intros y Hy. destruct (HFPD y Hy) as (a' & k' & HinDk & Hr).
    destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED (HDkL _ HinDk)) as (_ & _ & _ & _ & Hab & _).
    exists (a' - cf_head), (k' + cf_head). split; [exact Hab | exact Hr]. }
  assert (HFPLOW : forall y, inFP FP1 y -> y < YM05.alloc_ceiling).
  { intros y Hy. destruct (HFPblk y Hy) as (b & m & Hb & Hr).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & _ & Hcb & _). lia. }
  (* a harness block of Lam that is not the key's: its user bytes miss FP1 *)
  assert (HNFP : forall a0 k0 y, In (a0, k0) Lam -> ~ In (a0, k0) Dk -> a0 <= y < a0 + k0 -> ~ inFP FP1 y).
  { intros a0 k0 y Hin Hn Hy Hfp. destruct (HFPD y Hfp) as (a' & k' & HinDk & Hr).
    assert (Hne : (a0, k0) <> (a', k')) by (intros Ee; rewrite Ee in Hn; exact (Hn HinDk)).
    exact (pfk_hb_apart ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 a' k' y HAR HLED Hin (HDkL _ HinDk) Hne Hy Hr). }
  assert (He8 : 0 <= 0 <= 8) by lia.
  destruct (pfk_frame B ARx R R PB FX CTX0 en ly S Hp W regsc mem mdc k STK_fuzz_free 0 FP1 ly2 S2 Hp2 W2 regs2 mem2
    md2 k1 HPRE HFRc HSP HJc HJ2 HSTKF He8 HSINK HFPLOW Esp2 E32' E42' HMN2) as [HFR2 HSP2].
  split; [exact En|]. split; [exact Hi|]. split; [exact HFR2|]. split; [exact HSP2|].
  split; [exact HVR2|]. split; [exact HLR2|].
  exists (Fd ++ Dk), Lam2, Dr, Fr.
  split; [exact HAC2|].
  split.
  { apply (pfk_vnode B ARx LAWS VISF R en nd ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 (STK_fuzz_free + 0)
      (fe_sp1 en + 0) FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en) (fe_fail en)
      (fe_ran en) (fe_most en) (fe_own en) HVN HARc HLED HJc HLED2).
    - intros y Hy. destruct (HFPD y Hy) as (a' & k' & HinDk & Hr).
      exact (pfk_v_apart en nd ly S Hp W mem md Lam _ _ _ _ _ _ a' k' y HVN HAR HLED Hceil0 (HDkL _ HinDk) (HDkD _ HinDk) Hr).
    - intros b Hb Hnb. destruct (HAB b Hb Hnb) as (a & k0 & HinDk & ->).
      exists a, k0. split; [exact (HDkD _ HinDk)|]. split; [exact (HDkL _ HinDk) | reflexivity].
    - intros a0 k0 Hin Hn. apply HL2a; [exact Hin|]. intros H1. exact (Hn (HDkD _ H1)).
    - intros a0 k0 Hin. exact (HL2b _ Hin).
    - exact Hceil0.
    - exact HFPblk. }
  split; [rewrite <- app_assoc; exact HPD|].
  (* the slots i + 1 .. n - 1 *)
  apply (pfk_items B ARx LAWS R d' ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 (STK_fuzz_free + 0) (fe_sp1 en + 0)
    FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
    _ _ _ _ Dr Fr HARc HLED HJc HLED2 HIT).
  + intros y Hy. unfold pf_ofoot in Hy. rewrite Z2Nat.id in Hy by lia.
    destruct Hy as [Hy | [(Hks & Hy) | ((bx & bk) & Hb & Hh)]].
    * assert (HkDk : ~ In (fn_kids nd, kk) Dk) by exact (HownDk _ HkOwn).
      split; [exact (HNFP _ _ y HkLam HkDk ltac:(lia))|].
      exists (fn_kids nd), kk. split; [exact HkLam|]. split; [exact (HL2a _ HkLam HkDk) | lia].
    * assert (HyDk : ~ In (fn_keys nd, ky) Dk) by exact (HownDk _ HyOwn).
      split; [exact (HNFP _ _ y HyLam HyDk ltac:(lia))|].
      exists (fn_keys nd), ky. split; [exact HyLam|]. split; [exact (HL2a _ HyLam HyDk) | lia].
    * unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
      pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT bx bk Hb) as HbL. unfold prh_lin in HbL.
      split; [exact (HNFP _ _ y HbL (HDrDk _ Hb) Hh)|].
      exists bx, bk. split; [exact HbL|]. split; [exact (HL2a _ HbL (HDrDk _ Hb)) | exact Hh].
  + intros x0 k0 Hin. pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT x0 k0 Hin) as HbL. unfold prh_lin in HbL.
    exact (HL2a _ HbL (HDrDk _ Hin)).
Qed.
End k.
