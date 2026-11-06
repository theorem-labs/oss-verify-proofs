(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the memnorm-keeping walk records of the image-free realloc bridges and the
   memnorm-keeping form of the realloc(NULL, n) bridge (YGcfReallocCompose.v arealloc_null_realizes_cf_of_parts).
   rule 24: proves no function (kind: invariant lemma).
   WHAT: the null end rule (YGcfRealloc.v arealloc_null_realizes_cf) with the leaf strengthened by
   `YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'` at the leaf's end configuration (at_mem_cf): its leaf
   IS YGcfMallocComposeKeep.v's malloc_leaf_cf_keep.  The keep of the inner Allocate comes from its memnorm-kept
   contract (aalloc_realizes_cf_em_m, the original's premise); the interceptor's keep across its own segments is the
   one named premise, the null keep record.
   THE RECORDS: YGcfReallocCompose.v's two walk records with the keep in each segment's post (SRr is continuation-passing,
   YA0n.v SRr, so the keep must be a conjunct of the segment fact itself): the segments to Allocate's call (S1, S5) carry
   YGcfMallocComposeKeep.ikeep_mn_cf in place of ikeep_cf; S2a (to the copy routine's call) carries the keep right
   after RGtop.rkeep; S2b, S3, S4 and S6 right after RGtop.rwin; the copy routine's field rwk_memcpy carries it as the
   last conjunct inside its existential.  The invariants K1, K2, K3 and Kn carry no keep.  Each keep record implies
   the plain one.
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
AllocG DeallocG ReallocG ReallocP RGtop YGcfRmodel YAkMemnorm ErrnoGcf YGcfRealloc YG0s YGcfXs YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose YGcfMallocComposeKeep.
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
(* 1. The null end rule with the keep.                                          *)

(* YGcfRealloc.arealloc_null_realizes_cf with the malloc leaf with the keep (YGcfMallocComposeKeep.v). *)
Definition arealloc_null_realizes_cf_keep (Hp : list Z) (pc : Z) : Prop :=
ReallocP.arealloc_null_realizesP segs (admits (as_universe B)) malloc_cf free_cf
(fun ly S W regs mem md ch => acall_pre_cf segs B ly S Hp W regs mem md ch)
(fun _ _ => True) cf_malloc_max LIVE_MAX
(fun (R : Type) (t : itree astate R) W c Q => amreal segs t W c Q)
(fun ly S W regs mem md n r W' c' => YGcfMallocComposeKeep.malloc_leaf_cf_keep segs B ly S Hp W regs mem md n r W' c')
pc cf_pc_realloc_ra0.

(* ---------------------------------------------------------------------------- *)
(* 2. The walk records with the keep.                                           *)
Section R.
Variables (nmax al atp acf atpD : Z).
Local Abbreviation K1r_t := (YGcfReallocCompose.K1r_t segs).
Local Abbreviation K2r_t := (YGcfReallocCompose.K2r_t segs).
Local Abbreviation Knr_t := (YGcfReallocCompose.Knr_t segs).
Local Abbreviation rtr_cf := YGcfReallocCompose.rtr_cf.
Local Abbreviation rentry_cf := (YGcfReallocCompose.rentry_cf segs B).
Local Abbreviation rnentry_cf := (YGcfReallocCompose.rnentry_cf segs B).
Local Abbreviation realloc_dpre_cf := (YGcfReallocCompose.realloc_dpre_cf segs B atpD).
Local Abbreviation ikeep_mn_cf := (YGcfMallocComposeKeep.ikeep_mn_cf segs B).

(* YGcfReallocCompose.wrap_realloc_walk_cf with the keep in each segment's post. *)
Record wrap_realloc_walk_keep_cf (ARX : ARXh_t segs) (K1 : K1r_t) (K2 K3 : K2r_t) : Prop := {
rwk_pre : forall ly S Hp W regs mem md p n_old n ch,
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
rwk_mid_a : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
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
rwk_memcpy : forall (W : world segs) regs mem md d s n,
  ReallocG.rmemcpy_pre segs W regs mem d s n ->
  SRr segs W (cfg_at segs cf_pc_memcpy regs mem md)
  (fun W' c' => (W' = W /\ exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = aview segs (w_H W) mem (s + i)) /\
    (forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
    (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')));
rwk_mid_b : forall ly S Hp W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3,
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
rwk_ret : forall ly S Hp Hp' W regs mem md p n_old n ch q ly2 S2 W4 inst so bp regsD memD mdD ly3 S3 W5 regs5 mem5 md5,
  rentry_cf ly S Hp W regs mem md p n_old n ch ->
  K3 ly S Hp W regs mem md p n_old n ch q ly2 S2 W4 regsD memD mdD ->
  realloc_dpre_cf ARX Hp inst so bp ly2 S2 W4 regsD memD mdD p n_old (rtr_cf ly regs ch) ->
  free_dpost_cf segs B ARX Hp' inst ly2 S2 W4 regsD memD mdD
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
rwk_nret : forall ly S Hp W regs mem md p n_old n ch S1 W1 inst so bp regsA memA mdA ly2 S2 W2 regs2 mem2 md2,
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

(* YGcfReallocCompose.wrap_realloc_null_walk_cf with the keep in each segment's post. *)
Record wrap_realloc_null_walk_keep_cf (ARX : ARXh_t segs) (Kn : Knr_t) : Prop := {
rwnk_pre : forall ly S Hp W regs mem md n ch,
  rnentry_cf ly S Hp W regs mem md n ch -> ly_bot ly + 4096 < spZ regs -> xs_placed_cf ly S ->
  YGcfRmodel.rpre_cfr B S n -> 0 <= n < nmax ->
  amreal segs (free_cf PNull (rtr_cf ly regs ch) S) W (cfg_at segs cf_pc_wrap_realloc regs mem md)
  (fun r W1 c1 => exists inst so bp regsA memA mdA,
    c1 = cfg_at segs cf_pc_allocate regsA memA mdA /\
    (YGcfRmodel.rpre_cfr B (snd r) n -> blocks_bytes (snd r) + n <= LIVE_MAX -> admits (as_universe B) (rtr_cf ly regs ch) (snd r) ->
     malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly (snd r) W1 regsA memA mdA n (rtr_cf ly regs ch)) /\
    wle W W1 /\ same_io md mdA /\ RGtop.rin regs (spZ regsA) AllocG.AFSTACK_G /\
    ikeep_mn_cf ly S regs W mem W1 memA /\ errno_kept_cf B mem memA /\
    Kn ly S Hp W regs mem md n ch (snd r) W1 regsA memA mdA);
rwnk_post : forall ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2,
  rnentry_cf ly S Hp W regs mem md n ch ->
  Kn ly S Hp W regs mem md n ch S1 W1 regsA memA mdA ->
  malloc_apre_cf segs B nmax al atp acf ARX Hp inst so bp ly S1 W1 regsA memA mdA n (rtr_cf ly regs ch) ->
  malloc_apost_cf segs B ARX Hp inst ly S1 W1 regsA memA mdA
    (fun a => q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n) ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 (sptr_addr B ly2 q) -> qtight S2 ->
  (q = PNull -> val_mem segs (mrestrict (w_H W2) mem2) (as_oom_byte B) 1 1) ->
  (q <> PNull -> In (q, n) (blocks S2)) ->
  SRr segs W2 (cfg_at segs (raZ regsA) regs2 mem2 md2)
  (fun W' c' => exists regs' mem' md',
    c' = cfg_at segs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
    getr regs' 10 = w64 (sptr_addr B ly2 q) /\
    ARX Hp inst ly2 S2 W' mem' md' /\ same_io md2 md' /\
    RGtop.rkeep segs B regs W2 mem2 W' mem' /\ RGtop.rwin segs regs W' mem' /\
    (YAkMemnorm.memnorm segs mem2 -> YAkMemnorm.memnorm segs mem') /\
    (q = PNull -> val_mem segs (mrestrict (w_H W') mem') (as_errno B) 4 12 /\
                  val_mem segs (mrestrict (w_H W') mem') (as_oom_byte B) 1 1) /\
    (q <> PNull -> errno_kept_cf B mem2 mem'))
}.

(* ---------------------------------------------------------------------------- *)
(* 3. Each keep record implies the plain one.                                   *)

Lemma wrap_realloc_walk_cf_of_keep : forall ARX K1 K2 K3,
wrap_realloc_walk_keep_cf ARX K1 K2 K3 -> YGcfReallocCompose.wrap_realloc_walk_cf segs B nmax al atp acf atpD ARX K1 K2 K3.
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

Lemma wrap_realloc_null_walk_cf_of_keep : forall ARX Kn,
wrap_realloc_null_walk_keep_cf ARX Kn -> YGcfReallocCompose.wrap_realloc_null_walk_cf segs B nmax al atp acf ARX Kn.
Proof.
intros ARX Kn [WNPRE WNPOST]. constructor.
- intros ly S Hp W regs mem md n ch ENT HBOT HXS RP HN.
  eapply amreal_mono; [|exact (WNPRE ly S Hp W regs mem md n ch ENT HBOT HXS RP HN)].
  intros r W1 c1 (inst & so & bp & regsA & memA & mdA & E & PRE & WLE & IO & RIN & KP & ER & KK).
  exists inst, so, bp, regsA, memA, mdA.
  exact (conj E (conj PRE (conj WLE (conj IO (conj RIN
    (conj (YGcfMallocComposeKeep.ikeep_cf_of_mn segs B _ _ _ _ _ _ _ KP) (conj ER KK))))))).
- intros ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
    ENT KK APRE APO A0 QT OOM QB.
  eapply SRr_mono; [exact (WNPOST ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2
    regs2 mem2 md2 ENT KK APRE APO A0 QT OOM QB)|].
  intros W' c' _ (regs' & mem' & md' & E & CS & A0' & AX & IO & RK & RW & _ & NUL & ERK).
  exists regs', mem', md'.
  exact (conj E (conj CS (conj A0' (conj AX (conj IO (conj RK (conj RW (conj NUL ERK)))))))).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The null composition with the keep.                                       *)
(* YGcfReallocCompose.v's null bridge with its walk record replaced by the keep record and the leaf by the keep leaf,
   proved by that bridge's steps with the keep threaded: the entry segment's ikeep_mn_cf, Allocate's keep (the second
   conjunct of its at_mem_cf post, which the plain bridge drops), and the keep of the return segment, composed at the
   leaf's end memory.  WHY NOT FROM THE PLAIN BRIDGE: SRr and amreal are continuation-passing (YA0n.v SRr, YG0d.v
   amreal), and the plain bridge's post is the plain leaf, which keeps of ARX only ARcf and of the memory only a frame,
   so no instance of the plain bridge carries the memory keep to the leaf. *)
Local Abbreviation acall_pre_cf_ro := (YGcfReallocCompose.acall_pre_cf_ro segs B).
Local Abbreviation vm_rd32_cf := (YGcfReallocCompose.vm_rd32_cf segs).
Local Abbreviation vm_byte1_cf := (YGcfReallocCompose.vm_byte1_cf segs).

(* YGcfReallocCompose.arealloc_null_realizes_cf_of_parts with the keep. *)
Theorem arealloc_null_realizes_cf_of_parts_keep : forall (ARX : ARXh_t segs) (Kn : Knr_t),
YGcfReallocCompose.acall_prefix_cf segs B -> YGcfReallocCompose.acall_xs_cf segs B -> nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX ->
relro_seg_t segs -> errno_relro_t B ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
wrap_realloc_null_walk_keep_cf ARX Kn ->
forall Hp, arealloc_null_realizes_cf_keep Hp cf_pc_wrap_realloc.
Proof.
intros ARX Kn HPFX HXSP HNM HAR HXS RS ER HAM [WNPRE WNPOST] Hp.
intros ly S W regs mem md n ch PRE _ H10 H11 Hn Hlive Htr. cbv beta in PRE |- *.
pose proof (aalloc_realizes_cf_em_of_m segs B nmax al atp acf ARX HAM) as HA.
assert (ENT : rnentry_cf ly S Hp W regs mem md n ch) by exact (conj PRE (conj H10 (conj H11 (conj Hn (conj Hlive Htr))))).
pose proof (HPFX ly S Hp W regs mem md ch PRE) as HBOT.
pose proof (HXSP ly S Hp W regs mem md ch PRE) as HXS0.
pose proof (rpre_cfr_of_pre segs B ly S Hp W regs mem md ch n PRE) as RP.
assert (HN : 0 <= n < nmax) by (unfold nmax_cf_ok in HNM; lia).
set (tr := call_trace ly cf_pc_realloc_ra0 regs ch) in *.
unfold ReallocP.realloc_null_tree_with.
eapply amreal_mbind; [exact (RGtop.rg_apath_gflag segs _ _ _ _ (WNPRE ly S Hp W regs mem md n ch ENT HBOT HXS0 RP HN))|].
intros [] S1 W1 c1 H1. cbv beta in H1.
destruct H1 as [(inst & so & bp & regsA & memA & mdA & Ec1 & APREi & WLE1 & IO1 & RIN1 & (KV1 & KR1 & KM1) & ER1 & HKn) (trc1 & HP1 & HG1)].
subst c1. cbn [snd] in *.
pose proof (conj KV1 KR1) as KP1.
destruct (YGcfRmodel.rmodel_ok_cf_wf B) as [MO1 MO2].
destruct (MO1 S n tr trc1 S1 RP Hn Hlive Htr HP1 HG1) as (UA1 & RA1 & BB1 & BL1 & SEC1 & AOX1).
pose proof (APREi RA1 BB1 UA1) as APR.
assert (XO : forall a, ~ aowned B ly S a -> ~ Exists (in_zr a) (xs_cf ly S) -> ~ AOXm_cf B ly S1 a).
{ intros a N1 N2 X. destruct (AOX1 ly a X) as [Y|Y]; [exact (N1 Y) | exact (N2 Y)]. }
(* Allocate.  Field round 3 part 3b / 3c: arodata_ok_cf at Allocate's entry memory memA, from the call's
   (acall_pre_cf's last conjunct) through S1's raw frame (ikeep_cf). *)
pose proof (acall_pre_cf_ro ly S Hp W regs mem md ch PRE) as HROa0.
assert (ROa : arodata_ok_cf segs B memA).
{ pose proof (amc_layout _ _ _ _ _ (proj1 (proj1 PRE))) as LOa.
  assert (STKa : ly_stk_lo ly + ASTACK <= spZ regs) by (destruct PRE as (_ & _ & _ & STK & _); exact STK).
  apply (arodata_frame_cf segs B (fun a => aowned B ly S a \/ ascratch B ASTACK regs a) mem memA); [| |exact HROa0].
  - intros x NX. exact (proj2 KP1 x (fun H => NX (or_introl H)) (fun H => NX (or_intror H))).
  - intros a Ha NO. destruct (relro_apart_cf segs B ly S Hp W mem md a (proj1 PRE) RS Ha NO) as (R & _ & NA0 & _).
    split; [unfold kImgLo, kImgEnd in R; lia|].
    intros [X|X]; [exact (NA0 X) | exact (relro_not_scratch_cf B ly ASTACK regs a LOa STKa ER Ha R X)]. }
eapply RGtop.rg_then_SRr; [exact (HA Hp inst so bp ly S1 W1 regsA memA mdA n tr APR ROa)|].
intros [q S2] W2 c2 [LEAF KEEP].
unfold malloc_aleaf_cf, AllocG.alloc_leaf in LEAF.
destruct LEAF as (ly2 & regs2 & mem2 & md2 & Ec2 & APO & A02 & LP2 & (trc2 & HP2 & HG2) & OOM).
subst c2. cbn [fst snd] in *.
destruct (KEEP _ _ _ _ eq_refl) as [ERA MNA].
pose proof APO as (ARX2 & LLE2 & WLE2 & CS2 & IO2 & FR2 & FR2w & PR2).
destruct (MO2 S n tr trc1 S1 trc2 q S2 RP Hn Hlive Htr HP1 HG1 HP2 HG2) as (_ & QB2 & _).
eapply SRr_mono; [exact (WNPOST ly S Hp W regs mem md n ch S1 W1 inst so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2
  ENT HKn APR APO A02 LP2 OOM QB2)|].
intros W' c' WLE3 (regs' & mem' & md' & Ec' & CS' & A0' & ARX' & IO' & KP' & WN' & MN' & ENM' & ERK'). subst c'.
assert (XS : forall a, ~ ascratch B ASTACK regs a -> ~ ascratch B AllocG.AFSTACK_G regsA a)
  by (intros a NS X; exact (NS (RGtop.rg_scratch_in B regs regsA AllocG.AFSTACK_G a (proj1 RIN1) (proj2 RIN1) X))).
split.
- split.
  2:{ intros pc0 regs0 mem0 md0 E. unfold cfg_at in E. injection E. intros _ <- _ _ MN0.
      exact (MN' (MNA (KM1 MN0))). }
  exists ly2, regs', mem', md'. cbn [fst snd].
  split; [reflexivity|].
  split.
  { split; [exact (HAR _ _ _ _ _ _ _ ARX')|].
    split; [exact (layout_le_trans _ _ ly ly ly2 SEC1 (layout_le_refl _ ly) LLE2)|].
    split; [eapply wle_trans; [exact WLE1|]; eapply wle_trans; [exact WLE2 | exact WLE3]|].
    split; [exact CS'|].
    split; [exact (RGtop.rg_same_io_trans _ _ _ (RGtop.rg_same_io_trans _ _ _ IO1 IO2) IO')|].
    split; [|exact WN'].
    intros a Ha NA NA2 NS NE.
    assert (NX0 : ~ Exists (in_zr a) (xs_cf ly S)) by (intros X; apply NE; right; apply Exists_app; left; exact X).
    assert (NX2 : ~ Exists (in_zr a) (xs_cf ly2 S2)) by (intros X; apply NE; right; apply Exists_app; right; exact X).
    rewrite (proj1 KP' a Ha NS).
    rewrite (FR2 a Ha (XO a NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XS a NS)
      ltac:(intros X; apply NE; left; exact X)).
    exact (proj1 KP1 a Ha NA NS). }
  split; [exact A0'|]. split; [exact LP2|].
  split; [intros EQ; destruct (ENM' EQ) as [ER0 OM0]; exact (conj (vm_rd32_cf _ _ _ _ ER0) (vm_byte1_cf _ _ _ OM0))|].
  split; [exact (HXS _ _ _ _ _ _ _ ARX')|].
  split; [intros Hq i Hi; rewrite (ERK' Hq i Hi), (ERA Hq i Hi); exact (ER1 i Hi)|].
  intros x NA NA2 NS NE.
    assert (NX0 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly S)) by (intros X; apply NE; right; apply Exists_app; left; exact X).
    assert (NX2 : ~ Exists (in_zr (bv_unsigned x)) (xs_cf ly2 S2)) by (intros X; apply NE; right; apply Exists_app; right; exact X).
    rewrite (proj2 KP' x NS).
    rewrite (FR2w x (XO _ NA NX0) ltac:(intros [X|X]; [exact (NA2 X) | exact (NX2 X)]) (XS _ NS)
      ltac:(intros X; apply NE; left; exact X)).
    exact (proj2 KP1 x NA NS).
- intros EQ. subst q. exists S1, trc1, trc2. exact (conj HP1 (conj HG1 (conj HP2 HG2))).
Qed.

End R.

(* ---------------------------------------------------------------------------- *)
(* 5. The keep form implies the plain one.                                      *)

Lemma arealloc_null_realizes_cf_of_keep : forall Hp pc,
arealloc_null_realizes_cf_keep Hp pc -> YGcfRealloc.arealloc_null_realizes_cf segs B Hp pc.
Proof.
intros Hp pc H ly S W regs mem md n ch PRE RP H10 H11 Hn Hlive Htr. cbv beta in PRE |- *.
eapply amreal_mono; [|exact (H ly S W regs mem md n ch PRE RP H10 H11 Hn Hlive Htr)].
intros r W' c' [[L _] R]. exact (conj L R).
Qed.

End J.
End G.
