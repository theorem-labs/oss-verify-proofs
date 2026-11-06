(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the memnorm-keeping form of the realloc(p, n) end rule with the caller's room
   at the entry (YGcfInstReallocK.v arealloc_realizes_cf_k).  rule 24: proves no function (kind: invariant lemma).
   WHAT: the end rule with the leaf strengthened by `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` at
   the leaf's end configuration (at_mem_cf), as ONE extra last conjunct after the plain leaf, the shape of
   YGcfMallocComposeKeep.v's malloc_leaf_cf_keep:
   - realloc_leaf_cf_rh_keep: YG0dcfR.realloc_leaf_cf_rh (the primed leaf of arealloc_realizes_cf_k) with the keep;
   - arealloc_realizes_cf_k_keep: the text of YGcfInstReallocK.arealloc_realizes_cf_k with that leaf;
   - arealloc_realizes_cf_rp_h_rh_keep: YGcfReallocComposeRh.arealloc_realizes_cf_rp_h_rh with that leaf.
   THE RECORD: arealloc_realizes_cf_k_of_parts takes the PRIMED walk record YGcfReallocComposeRh.wrap_realloc_walk_cf_rh
   (S3 over Deallocate's primed post free_dpost_cf_rh).  wrap_realloc_walk_keep_cf_rh is that record with the keep in
   each segment's post, at the positions of YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf (whose S3 is over the
   released post, which the primed post does not imply); wrap_realloc_walk_keep_cf_rh_of builds it from
   wrap_realloc_walk_keep_cf and a primed S3 with the keep, wrap_realloc_walk_cf_rh_of_keep projects it to the plain
   primed record.
   THE COMPOSITIONS: arealloc_realizes_cf_rp_rh_of_parts_keep (YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts
   with the keep record) and arealloc_realizes_cf_k_of_parts_keep (YGcfInstReallocK.arealloc_realizes_cf_k_of_parts
   with the keep record), each by the original's steps with the keep threaded; the _of_keep lemmas project the keep
   forms to the plain ones.
   No image constant; no Section hypothesis. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfTok YG06bcf YG07cf YGcfRoomPre YG03cf YG03dcf YGcfApath YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
AllocG DeallocG ReallocG ReallocP RGtop YGcfRmodel YAkMemnorm ErrnoGcf YGcfRealloc YG0s YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomStep YGcfReallocCompose YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase YGcfImgRows YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRodata YGcfRehidePost YG0dcfR YGcfMallocComposeERh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstRealloc YGcfReallocComposeRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocK.
(* stdpp, through the LPS modules, shadows several list names; In and remove here are Stdlib's, as in YGcfRealloc.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* 1. The leaf and the end rules with the keep.                                 *)

(* YG0dcfR.realloc_leaf_cf_rh with the keep at its end configuration. *)
Definition realloc_leaf_cf_rh_keep (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : sptr) (n_old n : Z) (r : sptr * astate) (W' : world segs) (c' : config)
: Prop :=
realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c' /\
at_mem_cf segs c' (fun mem' => YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem').

(* YGcfInstReallocK.arealloc_realizes_cf_k with that leaf. *)
Definition arealloc_realizes_cf_k_keep (Hp : list Z) (pc : Z) (k : nat) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_realloc + k) ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
cf_hull_adm S n ->
amreal' segs RZ_cf (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => (realloc_leaf_cf_rh_keep ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> ReallocP.mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))) /\
 ROOM_cf_k (snd r) k).

(* YGcfReallocComposeRh.arealloc_realizes_cf_rp_h_rh with that leaf. *)
Definition arealloc_realizes_cf_rp_h_rh_keep (RP : astate -> Prop) (Hp : list Z) (pc : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> RP S ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
(forall trc r S', apath (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S)
  trc (r, S') -> cf_hull_ok S') ->
amreal' segs RZ_cf (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => realloc_leaf_cf_rh_keep ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> ReallocP.mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))).

(* ---------------------------------------------------------------------------- *)
(* 2. The primed walk record with the keep.                                     *)
Section R.
(* YGcfReallocCompose's Section R variables, in its order. *)
Variables (nmax al atp acf atpD : Z).
Local Abbreviation K1r_t := (YGcfReallocCompose.K1r_t segs).
Local Abbreviation K2r_t := (YGcfReallocCompose.K2r_t segs).
Local Abbreviation rtr_cf := YGcfReallocCompose.rtr_cf.
Local Abbreviation rentry_cf := (YGcfReallocCompose.rentry_cf segs B).
Local Abbreviation realloc_dpre_cf := (YGcfReallocCompose.realloc_dpre_cf segs B atpD).
Local Abbreviation ikeep_mn_cf := (YGcfMallocComposeKeep.ikeep_mn_cf segs B).
Local Abbreviation free_dpost_cf_rh := (YGcfReallocComposeRh.free_dpost_cf_rh segs B).

(* YGcfReallocComposeRh.wrap_realloc_walk_cf_rh with the keep in each segment's post: every field is
   YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf's, token for token, except S3 (rwkh_ret), which is over
   Deallocate's primed post free_dpost_cf_rh, with the keep at the position of rwk_ret's. *)
Record wrap_realloc_walk_keep_cf_rh (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t) : Prop := {
rwkh_pre : forall ly S Hp W regs mem md p n_old n ch,
  rentry_cf ly S Hp W regs mem md p n_old n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
  YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  amreal segs (free_cf PNull (rtr_cf ly regs ch) S) W (cfg_at segs cf_pc_wrap_realloc regs mem md)
  (fun r W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (rtr_cf ly regs ch) (snd r) ->
     malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly (snd r) W1 regsA memA mdA n (rtr_cf ly regs ch)) /\
    wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_mn_cf ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    K1 ly S Hp W regs mem md p n_old n ch (snd r) W1 regsA memA mdA);
rwkh_mid_a : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> q <> PNull -> In (q, n) (blocks S2) -> q <> p -> qtight S2 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W3 c3 => exists regsM memM mdM,
    c3 = cfg_at segs cf_pc_memcpy regsM memM mdM /\
    ReallocG.rmemcpy_pre segs W3 regsM memM (sptr_addr B ly2 q) (sptr_addr B ly p) (Z.min (req_size n_old) n) /\
    (forall i, 0 <= i < Z.min (req_size n_old) n ->
     aview segs (w_H W3) memM (sptr_addr B ly p + i) = aview segs (w_H W) mem (sptr_addr B ly p + i)) /\
    (forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> 0 <= a < 2 ^ 64 /\ ~ ascratch B ASTACK regs a) /\
    same_io md2 mdM /\ RGtop.rkeep segs B regs W2 mem2 W3 memM /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs memM) /\
    errno_kept_cf B mem2 memM /\
    K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM);
rwkh_memcpy : forall (W : world segs) regs mem md d s n,
  ReallocG.rmemcpy_pre segs W regs mem d s n ->
  SRr segs W (cfg_at segs cf_pc_memcpy regs mem md)
  (fun W' c' => (W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (s + i)) /\
    (forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')));
rwkh_mid_b : forall ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K2 ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM ->
  In (p, n_old) (blocks S2) -> rpreD_free_cf B S2 n_old -> admits (as_universe B) (rtr_cf ly regs ch) S2 ->
  ly_bot ly + 4096 < spZ regs ->
  aregs_preserved regsM regs3 -> same_but_materialized mdM md3 ->
  (forall i, 0 <= i < Z.min (req_size n_old) n ->
   aview segs (w_H W3) mem3 (sptr_addr B ly2 q + i) = aview segs (w_H W3) memM (sptr_addr B ly p + i)) ->
  (forall x : word, ~ (sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + Z.min (req_size n_old) n) ->
   mem3 x = memM x) ->
  (forall a, apresent (w_H W3) memM a -> apresent (w_H W3) mem3 a) ->
  SRr segs W3 (cfg_at segs (raZ regsM) regs3 mem3 md3)
  (fun W4 c4 => exists inst so bp regsD memD mdD,
    c4 = cfg_at segs cf_pc_deallocate regsD memD mdD /\
    realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) /\
    same_io md3 mdD /\ RGtop.rin regs (spZ regsD) DeallocG.DFSTACK_G /\
    RGtop.rkeep segs B regs W3 mem3 W4 memD /\ RGtop.rwin segs regs W4 memD /\
    (YAkMemnorm.memnorm segs mem3 -> YAkMemnorm.memnorm segs memD) /\
    errno_kept_cf B mem3 memD /\
    K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD);
rwkh_ret : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf_rh ARX Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep segs B regs W5 mem5 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem5 -> YAkMemnorm.memnorm segs mem') /\
    errno_kept_cf B mem5 mem');
rwkh_nret : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K1 ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => PNull <> PNull /\ sptr_addr B ly2 PNull <= a < sptr_addr B ly2 PNull + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 PNull) -> qtight S2 ->
  val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1 ->
  In (p, n_old) (blocks S1) -> In (p, n_old) (blocks S2) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
    val_mem segs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1)
}.

(* The released keep record and a primed S3 with the keep give the primed keep record (the keep form of
   YGcfReallocComposeRh.wrap_realloc_walk_cf_rh_of). *)
Lemma wrap_realloc_walk_keep_cf_rh_of : forall ARX K1 K2 K3,
YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf segs B nmax al atp acf atpD ARX K1 K2 K3 ->
(forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf_rh ARX Hp' inst ly2 S2 W4 regsD memD mdD
    (fun a => p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old) ly3 S3 W5 regs5 mem5 md5 ->
  qtight S3 ->
  SRr segs W5 (cfg_at segs (raZ regsD) regs5 mem5 md5)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp' inst ly3 S3 W' mem' md' /\ same_io md5 md' /\
    RGtop.rkeep segs B regs W5 mem5 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem5 -> YAkMemnorm.memnorm segs mem') /\
    errno_kept_cf B mem5 mem')) ->
wrap_realloc_walk_keep_cf_rh ARX K1 K2 K3.
Proof.
intros ARX K1 K2 K3 [P MA MC MB _ NR] RET.
exact (Build_wrap_realloc_walk_keep_cf_rh ARX K1 K2 K3 P MA MC MB RET NR).
Qed.

(* The primed keep record implies the plain primed one. *)
Lemma wrap_realloc_walk_cf_rh_of_keep : forall ARX K1 K2 K3,
wrap_realloc_walk_keep_cf_rh ARX K1 K2 K3 ->
YGcfReallocComposeRh.wrap_realloc_walk_cf_rh segs B nmax al atp acf atpD ARX K1 K2 K3.
Proof.
intros ARX K1 K2 K3 [WPRE WMIDA WMEM WMIDB WRET WNRET]. constructor.
- intros ly S Hp W regs mem md p n_old n ch ENT HBOT HXS RP HN.
  eapply amreal_mono; [|exact (WPRE ly S Hp W regs mem md p n_old n ch ENT HBOT HXS RP HN)].
  intros r W1 c1 (inst & so & bp & regsA & memA & mdA & E & PRE & WLE & IO & RIN & KP & ER & KK).
  exists inst, so, bp, regsA, memA, mdA.
  exact (conj E (conj PRE (conj WLE (conj IO (conj RIN
    (conj (YGcfMallocComposeKeep.ikeep_cf_of_mn segs B _ _ _ _ _ _ _ KP) (conj ER KK))))))).
- intros ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT KK APRE APO A0 HQ QB QP LP B1 B2 RD.
  eapply SRr_mono; [exact (WMIDA ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2
    regs2 mem2 md2 ENT KK APRE APO A0 HQ QB QP LP B1 B2 RD)|].
  intros W3 c3 _ (regsM & memM & mdM & E & MP & SRC & NB & IO & RK & _ & ER & K2H).
  exists regsM, memM, mdM.
  exact (conj E (conj MP (conj SRC (conj NB (conj IO (conj RK (conj ER K2H))))))).
- intros W regs mem md d s n PRE.
  eapply SRr_mono; [exact (WMEM W regs mem md d s n PRE)|].
  intros W' c' _ (EW & regs' & mem' & md' & E & CS & SBM & CPY & FR & PR & _).
  split; [exact EW|]. exists regs', mem', md'.
  exact (conj E (conj CS (conj SBM (conj CPY (conj FR PR))))).
- intros ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
    ENT KK B2 RD UA HB CS SBM CPY FR PR.
  eapply SRr_mono; [exact (WMIDB ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
    ENT KK B2 RD UA HB CS SBM CPY FR PR)|].
  intros W4 c4 _ (inst & so & bp & regsD & memD & mdD & E & DP & IO & RIN & RK & RW & _ & ER & K3H).
  exists inst, so, bp, regsD, memD, mdD.
  exact (conj E (conj DP (conj IO (conj RIN (conj RK (conj RW (conj ER K3H))))))).
- intros ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5
    ENT KK DP DPO QT.
  eapply SRr_mono; [exact (WRET ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD
    ly3 S3 W5 regs5 mem5 md5 ENT KK DP DPO QT)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & A0 & AX & IO & RK & RW & _ & ER).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj A0 (conj AX (conj IO (conj RK (conj RW ER))))))).
- intros ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
    ENT KK APRE APO A0 QT OOM B1 B2.
  eapply SRr_mono; [exact (WNRET ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2
    regs2 mem2 md2 ENT KK APRE APO A0 QT OOM B1 B2)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & A0' & AX & IO & RK & RW & _ & EV & OV).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj A0' (conj AX (conj IO (conj RK (conj RW (conj EV OV)))))))).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The compositions with the keep.                                           *)
(* Each is the original's proof re-run with the keep threaded: the entry segment's ikeep_mn_cf, Allocate's keep (the
   second conjunct of its at_mem_cf post), the primed Deallocate leaf's own memnorm_keep conjunct, and the keep of each
   later segment (the keep record), composed at the leaf's end memory.  WHY NOT FROM THE PLAIN COMPOSITION: SRr and
   amreal' are continuation-passing (YA0n.v SRr, YG0dH.v amreal'), and the plain composition's post is the plain leaf,
   which keeps of the memory only a frame, so no instance of it carries the memory keep to the leaf. *)
Local Abbreviation vm_rd32_cf := (YGcfReallocCompose.vm_rd32_cf segs).
Local Abbreviation vm_byte1_cf := (YGcfReallocCompose.vm_byte1_cf segs).
Local Abbreviation sptr_addr_block_cf := (YGcfReallocCompose.sptr_addr_block_cf B).
Local Abbreviation pw_snoc_cf := YGcfReallocCompose.pw_snoc_cf.
Local Abbreviation realloc_hp_nn_cf := (YGcfReallocCompose.realloc_hp_nn_cf B).
Local Abbreviation aowned_mid_cf := (YGcfReallocCompose.aowned_mid_cf B).
Local Abbreviation realloc_dpre_free := (YGcfReallocCompose.realloc_dpre_free segs B atpD).
Local Abbreviation ci_malloc_cf := YGcfReallocCompose.ci_malloc_cf.

(* YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts with the keep: its premises, wrap_realloc_walk_cf_rh
   replaced by the keep record, concluding the primed contract with the keep leaf. *)
Theorem arealloc_realizes_cf_rp_rh_of_parts_keep :
forall (RP : astate -> Prop) (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t),
YGcfReallocCompose.acall_prefix_cf segs B -> YGcfReallocCompose.acall_xs_cf segs B ->
YGcfReallocCompose.errno_word_cf B -> relro_seg_t segs -> errno_relro_t B ->
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX -> YGcfReallocCompose.ARX_qmh segs ARX ->
YGcfReallocComposeRh.realloc_room_rp segs B RP ARX ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
wrap_realloc_walk_keep_cf_rh ARX K1 K2 K3 ->
forall Hp, arealloc_realizes_cf_rp_h_rh_keep RP Hp cf_pc_wrap_realloc.
Proof.
intros RPe ARX K1 K2 K3 HPFX HXSP HEW RS ER HNM HAR HXS HQM BRP HAM HDM [WPRE WMIDA WMEM WMIDB WRET WNRET] Hp.
intros ly S W regs mem md p n_old n ch PRE RPS Hin H10 NIN H11 Hn Hlive Htr HADM.
pose proof (aalloc_realizes_cf_em_of_m segs B nmax al atp acf ARX HAM) as HA.
assert (ENT : rentry_cf ly S Hp W regs mem md p n_old n ch)
  by exact (conj PRE (conj Hin (conj H10 (conj NIN (conj H11 (conj Hn (conj Hlive Htr))))))).
pose proof (HPFX ly S Hp W regs mem md ch PRE) as HBOT.
pose proof (HXSP ly S Hp W regs mem md ch PRE) as HXS0.
pose proof (rpre_cfr_of_pre segs B ly S Hp W regs mem md ch n PRE) as RP.
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 PRE))) as WF0.
set (tr := call_trace ly cf_pc_realloc_ra0 regs ch) in *.
unfold ReallocP.realloc_tree_with.
(* S1: the entry step free_cf PNull, to Allocate's entry *)
eapply (amreal'_mbind segs RZ_cf);
  [exact (amreal_amreal' segs RZ_cf _ _ _ _ (RGtop.rg_apath_gflag segs _ _ _ _ (WPRE ly S Hp W regs mem md p n_old n ch ENT HBOT HXS0 RP HN)))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(inst & so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & RIN1 & (KV1 & KR1 & KM1) & ER1 & HK1) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
pose proof (conj KV1 KR1) as KP1.
destruct (YGcfRmodel.rmodel_ok_cf_wf B) as [MO1 MO2].
destruct (MO1 S n tr trc1 S1 RP Hn Hlive Htr HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
pose proof RA1 as (HU & WF1 & (HSA1 & HER1 & HBR1) & _).
assert (BLK1 : In (p, n_old) (blocks S1)) by (rewrite BL1; exact Hin).
pose proof (YGcfRmodel.cfr_null_state tr S trc1 S1 HP1) as ES1.
assert (CH1 : st_chunks S1 = st_chunks S) by (rewrite ES1; reflexivity).
assert (II1 : st_internal_inited S1 = true) by (rewrite ES1; reflexivity).
assert (FR1 : frames S1 = frames S) by (rewrite ES1; reflexivity).
assert (XO : forall a, ~ aowned B ly S a -> ~ Exists (in_zr a) (xs_cf ly S) -> ~ AOXm_cf B ly S1 a).
{ intros a N1 N2 X. destruct (AOX1 ly a X) as [Y|Y]; [exact (N1 Y) | exact (N2 Y)]. }
assert (XSA : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN1) (proj2 RIN1) X))).
(* Allocate, with arodata_ok_cf at its entry memory memA, as in the original *)
pose proof (YGcfReallocCompose.acall_pre_cf_ro segs B ly S Hp W regs mem md ch PRE) as HROa0.
assert (ROa : arodata_ok_cf segs B memA).
{ pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LOa.
  assert (STKa : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
  apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HROa0].
  - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
  - intros a Ha NO. destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
    split; [unfold kImgLo, kImgEnd in R; lia|].
    intros [X|X]; [exact (NA0 X) | exact (relro_not_scratch_cf B ly ASTACK regs a LOa STKa ER Ha R X)]. }
eapply (amreal'_mbind segs RZ_cf);
  [exact (amreal_amreal' segs RZ_cf _ _ _ _ (HA Hp inst so bp ly S1 W1 regsA memA mdA n tr APR ROa))|].
intros q S2 W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA MNA].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP Hn Hlive Htr HP1 HG1 HP2 HG2) as (UD2 & QB2 & PB2).
destruct (PB2 p n_old Hin) as (BLK2 & RD2 & QP2).
pose proof (malloc_cf_apath_post (as_universe B) S1 n tr trc2 (q, S2) HU WF1 ltac:(lia) BB1 UA1 HSA1 HER1 HBR1 HP2) as MPOST.
destruct MPOST as (WF2 & _ & SX2 & FRM2 & MBL2 & _).
assert (LLE02 : layout_le (length (st_secs S)) ly ly2) by exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2).
pose proof (YGcfXs.cfx_ipost_apath _ _ trc2 (q, S2) (ci_malloc_cf n tr S1) HP2) as CM. cbn [fst snd] in CM.
destruct CM as [CMi CMc].
destruct (RGtop.rg_null_dec q) as [EQ | HQ].
- (* the NULL-return arm *)
  subst q. cbv beta iota.
  eapply (YGcfReallocComposeRh.amreal'_SRr_pre_w segs); [exact (WNRET ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 LP2 (OOM eq_refl) BLK1 BLK2)|].
  intros W' c' WLE3 (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & MN' & ERV & OMV). subst c'.
  apply (amreal'_ret segs RZ_cf).
  split.
  + split.
    2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
        exact (MN' (MNA (KM1 MN0))). }
    apply realloc_leaf_cf_rh_of. exists ly2, regs', mem', md'. cbn [fst snd YGcfRealloc.realloc_hp_cf].
    split; [reflexivity|].
    split.
    { split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE02|].
      split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
      split; [exact CS'|].
      split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
      split; [|exact WN'].
      intros a Ha NA NA2 NS NE.
      assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
      assert (NX2 : ~ Exists (in_zr a) (xs_cf ly2 S2)) by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
      rewrite (proj1 KP' a Ha NS).
      rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XSA a NS)
        ltac:(intros [X _]; exact (X eq_refl))).
      exact (proj1 KP1 a Ha NA NS). }
    split; [rewrite A0'; reflexivity|].
    split; [exact LP2|].
    split; [intros X; exfalso; exact (X eq_refl)|].
    split; [intros _; exact (conj (vm_rd32_cf _ _ _ _ ERV) (vm_byte1_cf _ _ _ OMV))|].
    split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
    split; [intros X; exfalso; exact (X eq_refl)|].
    intros x NA NA2 NS NE.
      assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S))
        by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
      assert (NX2 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly2 S2))
        by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
      rewrite (proj2 KP' x NS).
      rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XSA _ NS)
        ltac:(intros [X _]; exact (X eq_refl))).
      exact (proj2 KP1 x NA NS).
  + intros _. exists S1, trc1, trc2. exact (conj HP1 (conj HG1 (conj HP2 HG2))).
- (* a block q: the copy, the free of the old block, the return *)
  assert (RK : forall s, (match q with PNull => YG00.ret PNull | _ => YG00.bind (free_cf p tr) (fun _ => YG00.ret q) end) s
    = YG00.bind (free_cf p tr) (fun _ => YG00.ret q) s)
    by (intros s; destruct q; [exfalso; exact (HQ eq_refl) | reflexivity | reflexivity | reflexivity]).
  cbv beta. rewrite RK.
  assert (II2 : st_internal_inited S2 = true) by (rewrite CMi; exact II1).
  (* the batch class's room after the inner malloc, from the caller's entry predicate (realloc_room_rp) *)
  pose proof (BRP ly S Hp W regs mem md ch tr trc1 S1 n trc2 q S2 inst ly2 W2 mem2 md2 PRE RPS HP1 HP2 ARX2) as BR2.
  (* the hull admission at S2, before the inner Deallocate, as in the original *)
  destruct (YGcfReallocCompose.inner_free_path_cf (as_universe B) S2 p n_old tr HU WF2 BR2 BLK2 (UD2 HQ))
    as (trc3' & S3' & HP3').
  pose proof (HADM _ q S3' (YGcfReallocCompose.realloc_tree_path_cf p n tr S trc1 S1 trc2 q S2 trc3' S3' HQ HP1 HP2 HP3')) as HO3.
  destruct (YGcfSecsStep.secs_free_step p tr S2 trc3' S3' HP3') as [SN ST].
  pose proof (cf_hull_counts S2 S3' SN ST HO3) as HO2.
  assert (RDF2 : rpreD_free_cf B S2 n_old)
    by exact (conj (RD2 HQ) (conj (HQM _ _ _ _ _ _ _ ARX2 HO2) (conj II2 (conj BR2 HO2)))).
  (* S2a, the copy routine, S2b *)
  eapply (YGcfReallocComposeRh.amreal'_SRr_pre_w segs); [exact (WMIDA ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT HK1 APR APO A02 HQ (QB2 HQ) (QP2 HQ) LP2 BLK1 BLK2 RDF2)|].
  intros W3 c3 WLE23 (regsM & memM & mdM & Ec3 & MPRE & SRC & NBLK & IO3 & KP3 & MNM & ER3 & HK2). subst c3.
  eapply (YGcfReallocComposeRh.amreal'_SRr_pre_w segs); [exact (WMEM W3 regsM memM mdM _ _ _ MPRE)|].
  intros W3' c3' _ (EW3 & regs3 & mem3 & md3 & Ec3' & CS3 & IO3' & CPY3 & FR3 & PR3 & MN3). subst W3' c3'.
  eapply (YGcfReallocComposeRh.amreal'_SRr_pre_w segs); [exact (WMIDB ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
    ENT HK2 BLK2 RDF2 (UD2 HQ) HBOT CS3 IO3' CPY3 FR3 PR3)|].
  intros W4 c4 WLE34 (inst' & so' & bp' & regsD & memD & mdD & Ec4 & DPR & IO4 & RIN4 & KP4 & WN4 & MN4 & ER4 & HK3). subst c4.
  (* Deallocate, at Hp: the old base is not hidden *)
  assert (AP2 : sptr_addr B ly2 p = sptr_addr B ly p) by exact (sptr_addr_block_cf _ ly ly2 S p n_old WF0 Hin LLE02).
  assert (DPRF : free_dpre_cf segs B atpD ARX Hp inst' so' bp' ly2 S2 W4 regsD memD mdD p n_old tr)
    by (apply realloc_dpre_free; [exact DPR | rewrite AP2; exact NIN]).
  (* arodata_ok_cf at Deallocate's entry memory memD, as in the original *)
  pose proof (YGcfReallocCompose.acall_pre_cf_ro segs B ly S Hp W regs mem md ch PRE) as HRO0.
  assert (ROd : arodata_ok_cf segs B memD).
  { pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LO0.
    assert (STK0 : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
    assert (ARS1 : ARcf segs B ly S1 Hp W1 memA mdA) by exact (HAR _ _ _ _ _ _ _ (proj1 APR)).
    assert (STKA : ly_stk_lo ly + AllocG.AFSTACK_G <= spZ regsA)
      by (destruct APR as (_ & _ & _ & _ & _ & STK & _); exact STK).
    assert (ARS2 : ARcf segs B ly2 S2 Hp W2 mem2 md2) by exact (HAR _ _ _ _ _ _ _ ARX2).
    pose proof (blocks_chunk_cf S2 q n (QB2 HQ)) as QK.
    assert (RF : forall a, aro_addr_cf a -> ~ Exists (in_zr a) (as_owned_static B) ->
      0 <= a < 2 ^ 64 /\ ~ aowned B ly S a /\ ~ AOXm_cf B ly S1 a /\ ~ AOXm_cf B ly2 S2 a /\
      ~ ascratch B ASTACK regs a /\ ~ ascratch B AllocG.AFSTACK_G regsA a /\
      ~ (sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
    { intros a Ha NO.
      destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
      destruct (relro_apart_cf segs B ly S1 Hp W1 memA mdA a ARS1 RS Ha NO) as (_ & _ & NA1 & NX1).
      destruct (relro_apart_cf segs B ly2 S2 Hp W2 mem2 md2 a ARS2 RS Ha NO) as (_ & I2 & NA2 & NX2).
      split; [unfold kImgLo, kImgEnd in R; lia|]. split; [exact NA0|].
      split; [intros [X|X]; [exact (NA1 X) | exact (NX1 X)]|].
      split; [intros [X|X]; [exact (NA2 X) | exact (NX2 X)]|].
      split; [exact (relro_not_scratch_cf B ly ASTACK regs a LO0 STK0 ER Ha R)|].
      split; [exact (relro_not_scratch_cf B ly AllocG.AFSTACK_G regsA a LO0 STKA ER Ha R)|].
      exact (relro_not_block_cf B ly2 S2 Hp _ q n a (proj1 ARS2) QK I2). }
    assert (RO1 : arodata_ok_cf segs B memA).
    { apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HRO0].
      - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & NA0 & _ & _ & NS & _). split; [exact H64|].
        intros [X|X]; [exact (NA0 X) | exact (NS X)]. }
    assert (RO2 : arodata_ok_cf segs B mem2).
    { apply (arodata_frame_cf segs B (fun a => AOXm_cf B ly S1 a \/ AOXm_cf B ly2 S2 a \/
        ascratch B AllocG.AFSTACK_G regsA a \/ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n))
        memA mem2); [| |exact RO1].
      - intros x NX. first [apply FR2w | symmetry; apply FR2w]; intros Y; apply NX; cbv beta; tauto.
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & N1 & N2 & _ & NSA & NB). split; [exact H64|].
        intros [X|[X|[X|[_ X]]]]; [exact (N1 X) | exact (N2 X) | exact (NSA X) | exact (NB X)]. }
    assert (ROM : arodata_ok_cf segs B memM).
    { apply (arodata_frame_cf segs B (fun a => ascratch B ASTACK regs a) mem2 memM); [| |exact RO2].
      - intros x NX. exact (proj2 KP3 x NX).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & NS & _). exact (conj H64 NS). }
    assert (RO3 : arodata_ok_cf segs B mem3).
    { apply (arodata_frame_cf segs B (fun a => sptr_addr B ly2 q <= a < sptr_addr B ly2 q + Z.min (req_size n_old) n)
        memM mem3); [| |exact ROM].
      - intros x NX. exact (FR3 x NX).
      - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & _ & _ & NB). split; [exact H64|].
        intros X. apply NB. pose proof (RGtop.rg_req_size_ge n). lia. }
    apply (arodata_frame_cf segs B (fun a => ascratch B ASTACK regs a) mem3 memD); [| |exact RO3].
    - intros x NX. exact (proj2 KP4 x NX).
    - intros a Ha NO. destruct (RF a Ha NO) as (H64 & _ & _ & _ & NS & _). exact (conj H64 NS). }
  (* Deallocate, primed: its post may re-hide inside dead_shadow_new ly2 S2 S3; its leaf carries the keep *)
  eapply (amreal'_mbind segs RZ_cf); [exact (HDM Hp inst' so' bp' ly2 S2 W4 regsD memD mdD p n_old tr DPRF ROd)|].
  intros [] S3 W5 c5 DLEAF.
  unfold dealloc_leaf_raw_em_rh in DLEAF.
  destruct DLEAF as (ly3 & regs5 & mem5 & md5 & Ec5 & DPO & ERD & MND & LP3 & (trc3 & HP3 & HG3)). subst c5. cbn [snd] in *.
  unfold MemnormT.memnorm_keep in MND.
  pose proof DPO as ((ARX3 & LLE3 & WLE45 & CS5 & IO5 & FR5 & PR5) & FR5w).
  pose (INC := fun a => YGcfReallocIx.realloc_dead_ix_of_paths _ ly ly2 S S1 S2 S3 n p q tr tr tr trc1 trc2 trc3 a
    WF0 HP1 HP2 (QP2 HQ) HP3 LLE02).
  (* S3 *)
  eapply (YGcfReallocComposeRh.amreal'_SRr_pre_w segs); [exact (WRET ly S Hp Hp W regs mem md p n_old n ch q ly2 S2 W4 inst' so' bp' regsD memD mdD
    ly3 S3 W5 regs5 mem5 md5 ENT HK3 DPR DPO LP3)|].
  intros W' c' WLE5' (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & MN' & ER'). subst c'.
  cbv beta. apply (amreal'_ret segs RZ_cf).
  (* the model after the free: blocks and frames *)
  assert (AF : atok_cf true (free_cf p tr S2) (free_post_ycf (as_universe B) S2 p n_old)).
  { eapply ml_free_cf; first [exact HU | exact WF2 | exact BR2 | (right; exact BLK2) | exact (UD2 HQ)]. }
  destruct (atok_cf_apath _ _ _ _ _ AF HP3) as [ns3 FP3].
  destruct FP3 as (WF3 & _ & _ & FRM3 & (l1 & l2 & HL12 & BL3) & _).
  cbn [snd] in WF3, FRM3, BL3.
  assert (BL3S2 : forall b, In b (blocks S3) -> In b (blocks S2)).
  { intros b Hb. rewrite BL3 in Hb. destruct HL12 as [(_ & E) | E].
    - rewrite <- E. exact Hb.
    - rewrite E. apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left; exact Hb | right; right; exact Hb]. }
  assert (QB3 : In (q, n) (blocks S3)).
  { pose proof (QB2 HQ) as Q2. rewrite BL3. destruct HL12 as [(_ & E) | E].
    - rewrite E. exact Q2.
    - rewrite E in Q2. apply in_app_iff in Q2 as [Q2|[Q2|Q2]]; apply in_app_iff.
      + left. exact Q2.
      + exfalso. injection Q2 as Eq _. exact (QP2 HQ (eq_sym Eq)).
      + right. exact Q2. }
  assert (MBL2' : blocks S2 = blocks S1 ++ [(q, n)])
    by (destruct q; [exfalso; exact (HQ eq_refl) | exact (proj1 MBL2) | exact (proj1 MBL2) | exact (proj1 MBL2)]).
  (* layouts and addresses *)
  assert (AQ3 : sptr_addr B ly3 q = sptr_addr B ly2 q) by exact (sptr_addr_block_cf _ ly2 ly3 S2 q n WF2 (QB2 HQ) LLE3).
  pose proof (proj1 SX2) as SL12.
  assert (LLE03 : layout_le (length (st_secs S)) ly ly3)
    by exact (layout_le_trans (length (st_secs S)) (length (st_secs S2)) ly ly2 ly3 ltac:(lia) LLE02 LLE3).
  (* the owned set of the middle state, at one layout (aowned_mid_cf) *)
  pose proof (YG0scf.AR_layout_law_ok_cf segs B) as LAYL.
  assert (OWN0 : forall a, aowned B ly3 S a <-> aowned B ly S a)
    by exact (proj2 (proj2 (LAYL ly S Hp W mem md ly3 (proj1 PRE) LLE03))).
  assert (OWN2 : forall a, aowned B ly3 S2 a <-> aowned B ly2 S2 a)
    by exact (proj2 (proj2 (LAYL ly2 S2 Hp W2 mem2 md2 ly3 (HAR _ _ _ _ _ _ _ ARX2) LLE3))).
  assert (MID : forall a, ~ aowned B ly S a -> ~ aowned B ly3 S3 a -> ~ aowned B ly2 S2 a).
  { intros a NA NA3 O2.
    apply (aowned_mid_cf ly3 S S2 S3 q n a).
    - intros k Hk. destruct (CMc k Hk) as [X|X]; [left; rewrite <- CH1; exact X | right; exact X].
    - intros [b1 b2] Hb. exact (proj1 (PB2 b1 b2 Hb)).
    - rewrite FRM2. exact FR1.
    - exact QB3.
    - exact BL3S2.
    - exact FRM3.
    - exact (proj2 (OWN2 a) O2).
    - intros X. exact (NA (proj1 (OWN0 a) X)).
    - exact NA3. }
  (* the errbuf extent of the middle state is the end state's *)
  assert (XS23 : forall a, Exists (in_zr a) (xs_cf ly2 S2) -> Exists (in_zr a) (xs_cf ly3 S3)).
  { intros a X. rewrite <- (YGcfXs.xs_cf_layout ly2 ly3 S2 LLE3) in X.
    rewrite <- (proj1 (YGcfXs.free_cf_frame p tr S2 trc3 S3 HP3) ly3) in X. exact X. }
  (* the new block: apart from the old one at S2, and client bytes at S2 and S3 *)
  pose proof (YG0scf.AR_blocks_law_ok_cf segs B) as LAWB.
  assert (QA2 : In (sptr_addr B ly2 q, n) (ablocks B ly2 S2))
    by exact (in_map (fun b => (sptr_addr B ly2 (fst b), snd b)) _ _ (QB2 HQ)).
  destruct (LAWB ly2 S2 Hp W2 mem2 md2 _ _ (HAR _ _ _ _ _ _ _ ARX2) QA2) as (_ & _ & _ & QIA2 & QOWN2 & PW & _).
  assert (QA3 : In (sptr_addr B ly3 q, n) (ablocks B ly3 S3))
    by exact (in_map (fun b => (sptr_addr B ly3 (fst b), snd b)) _ _ QB3).
  destruct (LAWB ly3 S3 Hp W5 mem5 md5 _ _ (HAR _ _ _ _ _ _ _ ARX3) QA3) as (_ & _ & _ & _ & QOWN3 & _ & _).
  assert (DJ : sptr_addr B ly2 p + req_size n_old <= sptr_addr B ly2 q \/ sptr_addr B ly2 q + req_size n <= sptr_addr B ly2 p).
  { unfold ablocks in PW. rewrite MBL2' in PW. rewrite !map_app in PW. cbn [map fst snd] in PW.
    assert (D : zdisjoint (sptr_addr B ly2 p, req_size n_old) (sptr_addr B ly2 q, req_size n)).
    { eapply pw_snoc_cf; [exact PW|]. apply in_map_iff. exists (sptr_addr B ly2 p, n_old). split; [reflexivity|].
      apply in_map_iff. exists (p, n_old). split; [reflexivity | exact BLK1]. }
    unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
  assert (NOWN2 : forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> ~ aowned B ly2 S2 a)
    by (intros a Ha; exact (proj2 (QOWN2 a Ha))).
  assert (NOWN3 : forall a, sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n -> ~ aowned B ly3 S3 a)
    by (intros a Ha; rewrite <- AQ3 in Ha; exact (proj2 (QOWN3 a Ha))).
  assert (XSD : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B DeallocG.DFSTACK_G regsD a)
    by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsD DeallocG.DFSTACK_G a (proj1 RIN4) (proj2 RIN4) X))).
  pose proof (RGtop.rg_req_size n (proj1 Hn)) as RQ.
  pose proof (RGtop.rg_req_size_ge n_old) as RQO.
  (* the leaf, with the keep composed at its end memory *)
  split; [|intros X; exfalso; exact (HQ X)].
  split.
  2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
      exact (MN' (MND (MN4 (MN3 (MNM (MNA (KM1 MN0))))))). }
  exists ly3, regs', mem', md'. cbn [fst snd].
  rewrite (realloc_hp_nn_cf ly p q Hp HQ). rewrite notin_remove; [|exact NIN].
  split; [reflexivity|].
  split.
  { split; [exact (HAR _ _ _ _ _ _ _ ARX')|]. split; [exact LLE03|].
    (* the world: strict before and after the inner free, inside the inner free's dead set across it *)
    split.
    { intros x Hx. destruct (WLE45 x (WLE5' x Hx)) as [H4 | HD4].
      - left. exact (WLE1 x (WLE2 x (WLE23 x (WLE34 x H4)))).
      - right. exact (INC _ HD4). }
    split; [exact CS'|].
    split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _
      (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO3)
      (RGtop.rg_sbm_io _ _ IO3')) IO4) IO5) IO')|].
    split; [|exact WN'].
    intros a Ha NA NA3 NS NE NDS.
    assert (NEn : ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n))
      by (rewrite <- AQ3; intros X; apply NE; left; exact X).
    assert (NEo : ~ (p <> PNull /\ sptr_addr B ly2 p <= a < sptr_addr B ly2 p + req_size n_old))
      by (rewrite AP2; intros [_ X]; apply NE; right; left; exact (conj HQ X)).
    assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
    assert (NX3 : ~ Exists (in_zr a) (xs_cf ly3 S3)) by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
    pose proof (MID a NA NA3) as NA2.
    rewrite (proj1 KP' a Ha NS).
    rewrite (FR5 a Ha NA2 NA3 (XSD a NS) NEo (fun X => NDS (INC _ X))).
    rewrite (proj1 KP4 a Ha NS).
    rewrite (RGtop.rg_aview_same segs (w_H W3) memM mem3 a
      (FR3 _ ltac:(rewrite (RGtop.rg_unsigned_small a Ha); intros X; apply NEn; split; [exact HQ | lia]))).
    rewrite (proj1 KP3 a Ha NS).
    rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX3 (XS23 a X))]) (XSA a NS) NEn).
    exact (proj1 KP1 a Ha NA NS). }
  split; [rewrite AQ3; exact A0'|].
  split; [exact LP3|].
  split.
  { intros _ i Hi.
    assert (Hi' : 0 <= i < Z.min (req_size n_old) n) by lia.
    assert (Hq : sptr_addr B ly2 q <= sptr_addr B ly2 q + i < sptr_addr B ly2 q + req_size n) by lia.
    destruct (NBLK _ Hq) as [Ra NS].
    rewrite AQ3.
    rewrite (proj1 KP' _ Ra NS).
    rewrite (FR5 _ Ra (NOWN2 _ Hq) (NOWN3 _ Hq) (XSD _ NS) ltac:(intros [_ X]; lia)
      (dead_shadow_new_app ly2 S2 S3 _ (in_app_addr _ _ _ QIA2 Hq))).
    rewrite (proj1 KP4 _ Ra NS), (CPY3 i Hi'), (SRC i Hi'). reflexivity. }
  split; [intros X; exfalso; exact (HQ X)|].
  split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
  split.
  { intros _ i Hi.
    rewrite (ER' i Hi), (ERD i Hi), (ER4 i Hi).
    assert (EM : mem3 (w64 (as_errno B + i)) = memM (w64 (as_errno B + i))).
    { apply FR3. assert (Hr : 0 <= as_errno B + i < 2 ^ 64) by (destruct HEW; lia).
      unfold w64. rewrite (RGtop.rg_unsigned_small _ Hr). intros X.
      assert (Hx : sptr_addr B ly2 q <= as_errno B + i < sptr_addr B ly2 q + req_size n) by lia.
      destruct (NBLK _ Hx) as [_ NS]. apply NS. right. lia. }
    rewrite EM, (ER3 i Hi), (ERA HQ i Hi). exact (ER1 i Hi). }
  intros x NA NA3 NS NE.
    assert (NEn : ~ (q <> PNull /\ sptr_addr B ly2 q <= bv_unsigned x < sptr_addr B ly2 q + req_size n))
      by (rewrite <- AQ3; intros X; apply NE; left; exact X).
    assert (NEo : ~ (p <> PNull /\ sptr_addr B ly2 p <= bv_unsigned x < sptr_addr B ly2 p + req_size n_old))
      by (rewrite AP2; intros [_ X]; apply NE; right; left; exact (conj HQ X)).
    assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S))
      by (intros X; apply NE; right; right; apply Exists_app; left; exact X).
    assert (NX3 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly3 S3))
      by (intros X; apply NE; right; right; apply Exists_app; right; exact X).
    pose proof (MID _ NA NA3) as NA2.
    rewrite (proj2 KP' x NS), (FR5w x NA2 NA3 (XSD _ NS) NEo), (proj2 KP4 x NS).
    rewrite (FR3 x ltac:(intros X; apply NEn; split; [exact HQ | lia])).
    rewrite (proj2 KP3 x NS).
    rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX3 (XS23 _ X))]) (XSA _ NS) NEn).
    exact (proj2 KP1 x NA NS).
Qed.

(* YGcfInstReallocK.arealloc_realizes_cf_k_of_parts with the keep: its premises, wrap_realloc_walk_cf_rh replaced by
   the keep record, by the original's steps over the keep composition above (at RP := fun S => ROOM_cf_k S
   RK_realloc, YGcfInstReallocK.realloc_room_rp_k), the post's room by YGcfRoomStep.realloc_room_keep_cf over a
   granted path (YG0dHc.amreal'_apath_gflag), and the end-state hull admission from the entry's. *)
Theorem arealloc_realizes_cf_k_of_parts_keep : forall (ARX : ARXh_t segs) (K1 : YGcfReallocCompose.K1r_t segs)
(K2 K3 : YGcfReallocCompose.K2r_t segs),
YGcfReallocCompose.acall_prefix_cf segs B -> YGcfReallocCompose.acall_xs_cf segs B -> YGcfReallocCompose.errno_word_cf B ->
relro_seg_t segs -> errno_relro_t B ->
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX -> YGcfReallocCompose.ARX_qmh segs ARX ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
wrap_realloc_walk_keep_cf_rh ARX K1 K2 K3 ->
forall Hp k, arealloc_realizes_cf_k_keep Hp cf_pc_wrap_realloc k.
Proof.
intros ARX K1 K2 K3 HPFX HXSP HEW HRS HER HNM HAR HXS HQM HAM HDM HW Hp k.
intros ly S W regs mem md p n_old n ch PRE RMk Hin H10 NIN H11 Hn Hlive Htr HADM.
assert (HADMp : forall trc r S', apath (ReallocP.realloc_tree_with malloc_cf free_cf p n
    (call_trace ly cf_pc_realloc_ra0 regs ch) S) trc (r, S') -> cf_hull_ok S')
  by (intros trc r S' Hpt; exact (cf_hull_adm_post S n r S' HADM (YGcfSecsStep.secs_realloc_step p n _ S trc (r, S') Hpt))).
pose proof (arealloc_realizes_cf_rp_rh_of_parts_keep (fun S => ROOM_cf_k S RK_realloc) ARX K1 K2 K3
  HPFX HXSP HEW HRS HER HNM HAR HXS HQM (YGcfInstReallocK.realloc_room_rp_k segs B ARX) HAM HDM HW Hp
  ly S W regs mem md p n_old n ch PRE (RK_mono S (RK_realloc + k) RK_realloc (Nat.le_add_r _ _) RMk)
  Hin H10 NIN H11 Hn Hlive Htr HADMp) as A.
pose proof (amreal'_apath_gflag segs RZ_cf _ _ _ _ A) as A2.
eapply amreal'_mono; [|exact A2].
intros r W' c' [[L R] (trc & Hpt & _)]. split; [exact (conj L R)|].
destruct r as [q s'].
exact (YGcfRoomStep.realloc_room_keep_cf k p n _ S trc q s'
  (YGcfRoomStep.room_shape_of_acall_pre_cf segs B ly S Hp W regs mem md ch PRE) RMk Hpt).
Qed.

End R.

(* ---------------------------------------------------------------------------- *)
(* 4. The keep forms imply the plain ones.                                      *)

Lemma realloc_leaf_cf_rh_of_keep : forall ly S Hp W regs mem md p n_old n r W' c',
realloc_leaf_cf_rh_keep ly S Hp W regs mem md p n_old n r W' c' ->
realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c'.
Proof. intros ly S Hp W regs mem md p n_old n r W' c' [L _]. exact L. Qed.

Lemma arealloc_realizes_cf_rp_h_rh_of_keep : forall RP Hp pc,
arealloc_realizes_cf_rp_h_rh_keep RP Hp pc -> YGcfReallocComposeRh.arealloc_realizes_cf_rp_h_rh segs B RP Hp pc.
Proof.
intros RP Hp pc H ly S W regs mem md p n_old n ch PRE RPS Hin H10 NIN H11 Hn Hlive Htr HADM.
eapply amreal'_mono; [|exact (H ly S W regs mem md p n_old n ch PRE RPS Hin H10 NIN H11 Hn Hlive Htr HADM)].
intros r W' c' [[L _] R]. exact (conj L R).
Qed.

Lemma arealloc_realizes_cf_k_of_keep : forall Hp pc k,
arealloc_realizes_cf_k_keep Hp pc k -> YGcfInstReallocK.arealloc_realizes_cf_k segs B Hp pc k.
Proof.
intros Hp pc k H ly S W regs mem md p n_old n ch PRE RMk Hin H10 NIN H11 Hn Hlive Htr HADM.
eapply amreal'_mono; [|exact (H ly S W regs mem md p n_old n ch PRE RMk Hin H10 NIN H11 Hn Hlive Htr HADM)].
intros r W' c' [[[L _] R] RM]. exact (conj (conj L R) RM).
Qed.

End J.
End G.

Set Printing Implicit.
Print realloc_leaf_cf_rh_keep.
Print arealloc_realizes_cf_k_keep.
Print arealloc_realizes_cf_rp_h_rh_keep.
Print wrap_realloc_walk_keep_cf_rh.
Check @arealloc_realizes_cf_rp_rh_of_parts_keep.
Check @arealloc_realizes_cf_k_of_parts_keep.
Check @wrap_realloc_walk_keep_cf_rh_of.
Check @wrap_realloc_walk_cf_rh_of_keep.
Check @realloc_leaf_cf_rh_of_keep.
Check @arealloc_realizes_cf_rp_h_rh_of_keep.
Check @arealloc_realizes_cf_k_of_keep.
(* each twin, then its original *)
Print Assumptions arealloc_realizes_cf_k_of_parts_keep.
Print Assumptions YGcfInstReallocK.arealloc_realizes_cf_k_of_parts.
Print Assumptions arealloc_realizes_cf_rp_rh_of_parts_keep.
Print Assumptions YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts.
Print Assumptions wrap_realloc_walk_keep_cf_rh_of.
Print Assumptions YGcfReallocComposeRh.wrap_realloc_walk_cf_rh_of.
Print Assumptions wrap_realloc_walk_cf_rh_of_keep.
Print Assumptions realloc_leaf_cf_rh_of_keep.
Print Assumptions arealloc_realizes_cf_rp_h_rh_of_keep.
Print Assumptions arealloc_realizes_cf_k_of_keep.
