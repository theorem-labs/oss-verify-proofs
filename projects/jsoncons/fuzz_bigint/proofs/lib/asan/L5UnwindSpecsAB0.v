(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5USA.
Import L5A. Import L5CA. Import L5CSA. Import L5CB.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GP : Z := 67584.
Definition TOP_PAD : Z := 0x8e580.        (* [comment removed for export] *)
Definition E1_LANDING : Z := 0x8e5d8.     (* [comment removed for export] *)
Definition CATCH : Z := 0x8e644.          (* [comment removed for export] *)
Definition CATCH_E : Z := 0x8e648.        (* [comment removed for export] *)
Definition CATCH_RET : Z := 0x8e64c.      (* [comment removed for export] *)
Definition STRCTOR_THROW : Z := 0x8eaa0.  (* [comment removed for export] *)
Definition ZERO_THROW : Z := 0x93890.     (* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x907f0.   (* [comment removed for export] *)
Definition E1_RET : Z := 0x8e2e4.         (* [comment removed for export] *)
Definition OM1_RET : Z := 0x8eb34.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition EH_CAUGHT : Z := 0x610dc8.     (* [comment removed for export] *)
Definition EH_UNCAUGHT : Z := 0x610dd0.   (* [comment removed for export] *)
Definition SYSCAT_GUARD : Z := 0x610ff0.  (* [comment removed for export] *)
Definition SYSCAT_OBJ : Z := 0xdab80.     (* [comment removed for export] *)
Definition UW_FLAGS : Z := 0x611831.      (* [comment removed for export] *)
Definition ERRNO : Z := 0x611864.         (* [comment removed for export] *)
Definition TD_LOCALE : Z := 0x6118d8.     (* [comment removed for export] *)
Definition GLOBAL_LOCALE : Z := 0x631bd0. (* [comment removed for export] *)
Definition LOCALE_MSGCAT : Z := 0x631bf8. (* [comment removed for export] *)
Definition CANARY : Z := 0x631948.        (* [comment removed for export] *)
Definition AUXVP : Z := 0x631ba0.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition EXC_CLASS : Z := 0x434c4e47432b2b00.   (* [comment removed for export] *)
Definition DTOR_SYSTEM_ERROR : Z := 0xb3768.      (* [comment removed for export] *)
Definition DTOR_RUNTIME_ERROR : Z := 0xb0398.     (* [comment removed for export] *)

Definition EXC1_SZ : Z := 160.  (* [comment removed for export] *)
Definition EXC23_SZ : Z := 144. (* [comment removed for export] *)
Definition REF1_SZ : Z := 41.   (* [comment removed for export] *)
Definition REF2_SZ : Z := 37.   (* [comment removed for export] *)
Definition REF3_SZ : Z := 66.   (* [comment removed for export] *)
Definition MSG3_SZ : Z := 48.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CHAIN_SCR : Z := 69632.
(* [comment removed for export] *)
Definition CATCH_SCR : Z := 69632.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition UNW_STATICS : list (Z * Z) := [(EH_CAUGHT, 12); (SYSCAT_GUARD, 8); (UW_FLAGS, 6); (ERRNO, 4)].
(* [comment removed for export] *)
Definition UNW_CONSTS : list (Z * Z) := [(0xdab50, 32); (0xdab80, 8); (0x6118d8, 8); (0x631bf8, 8); (0x631948, 8); (0x631ba0, 8)].
(* [comment removed for export] *)
Definition TPV : Z := 0x611908.
Definition as0_unw_layout (L : asan_layout) : Prop :=
  (forall r a, In r UNW_STATICS -> fst r <= a < fst r + snd r -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a) /\
  (forall r a, In r UNW_CONSTS -> fst r <= a < fst r + snd r -> ~ hl_rt_static L a) /\
  hl_tp L = TPV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record XS : Type := mkXS { xs_gd : bool; xs_fl : bool; xs_av : Z; xs_uid : Z; xs_rnd : Z; xs_canary : Z; xs_hw : Z }.
Definition xs_of (gd fl : bool) (av uid rnd canary hw : Z) : XS := mkXS gd fl av uid rnd canary hw.

(* [comment removed for export] *)
Definition auxv20A (uid rnd hw : Z) : list Z := [3; 0x10040; 4; 56; 5; 11; 16; hw; 6; 4096; 11; uid; 12; uid; 23; 0; 25; rnd; 0; 0].

Definition uw_flags (M : word -> option byte) (fl : bool) : Prop :=
  if fl then L5.u8_at RSEGS M UW_FLAGS 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 1) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 2) 1
             /\ L5.u8_at RSEGS M (UW_FLAGS + 3) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 4) 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 5) 0
  else L5.u8_at RSEGS M UW_FLAGS 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 2) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 4) 0.
Definition syscat_guard (M : word -> option byte) (gd : bool) : Prop :=
  L5.u8_at RSEGS M SYSCAT_GUARD (if gd then 1 else 0) /\ L5.u8_at RSEGS M (SYSCAT_GUARD + 1) (if gd then 1 else 0).

(* [comment removed for export] *)
Definition statics_const (M : word -> option byte) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M TD_LOCALE GLOBAL_LOCALE /\ L5.u64_at RSEGS M LOCALE_MSGCAT 0
  /\ (exists e, L5.u32_at RSEGS M ERRNO e /\ 0 <= e < 2 ^ 64)      (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M CANARY canary /\ L5.u64_at RSEGS M AUXVP av /\ av mod 8 = 0 /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47
  /\ (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (auxv20A uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= canary < 2 ^ 64 /\ 0 <= hw < 2 ^ 64
  /\ L5.img_clear M 0x10000 0xd8000 /\ L5.img_clear M 0xdab50 0xdab70 /\ L5.img_clear M SYSCAT_OBJ (SYSCAT_OBJ + 8).

(* [comment removed for export] *)
Definition e1_staticsA (M : word -> option byte) (gd fl : bool) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M EH_CAUGHT 0 /\ L5.u32_at RSEGS M EH_UNCAUGHT 0
  /\ syscat_guard M gd /\ uw_flags M fl
  /\ statics_const M av uid rnd canary hw.
(* [comment removed for export] *)
Definition xs_pre (ar : asan_run) (st : XS) (M : word -> option byte) : Prop :=
  e1_staticsA M (xs_gd st) (xs_fl st) (xs_av st) (xs_uid st) (xs_rnd st) (xs_canary st) (xs_hw st) /\ ar_sptop ar <= xs_av st.

(* [comment removed for export] *)
Definition xs_foot : list L5.range := [(EH_UNCAUGHT, 4); (UW_FLAGS, 6)].
Definition xs_foot1 : list L5.range := [(EH_UNCAUGHT, 4); (UW_FLAGS, 6); (SYSCAT_GUARD, 8); (ERRNO, 4)].

(* [comment removed for export] *)
Definition statics_landed (M : word -> option byte) (gd : bool) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M EH_CAUGHT 0 /\ L5.u32_at RSEGS M EH_UNCAUGHT 1
  /\ syscat_guard M gd /\ uw_flags M true
  /\ statics_const M av uid rnd canary hw.

(* [comment removed for export] *)
Lemma statics_after_catch M M' gd av uid rnd canary hw :
  statics_landed M gd av uid rnd canary hw ->
  L5.u64_at RSEGS M' EH_CAUGHT 0 -> L5.u32_at RSEGS M' EH_UNCAUGHT 0 ->
  (syscat_guard M gd -> syscat_guard M' gd) -> (uw_flags M true -> uw_flags M' true) ->
  (statics_const M av uid rnd canary hw -> statics_const M' av uid rnd canary hw) ->
  e1_staticsA M' gd true av uid rnd canary hw.
Proof.
  intros (_ & _ & G & F & C) C0 U0 TG TF TC. unfold e1_staticsA.
  split. exact C0. split. exact U0. split. exact (TG G). split. exact (TF F). exact (TC C).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exc_at (M : word -> option byte) (obj ref dtor : Z) : Prop :=
     L5.u64_at RSEGS M (obj - 32) EXC_CLASS /\ L5.u32_at RSEGS M (obj - 72) 0 /\ L5.u64_at RSEGS M (obj - 40) obj
  /\ L5.u64_at RSEGS M (obj - 120) 1 /\ L5.u64_at RSEGS M (obj - 104) dtor
  /\ L5.u64_at RSEGS M (obj + 8) (ref + 24) /\ L5.u32_at RSEGS M (ref + 16) 0.

(* [comment removed for export] *)
Local Abbreviation stksh := L5OMA.stksh.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithLayout.
Variable L : asan_layout.

Definition landed_core (dtor objsz refsz : Z) (st : XS) (gd' : bool) (LB : list (Z * Z)) (sp : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) : Prop :=
  exists obj ref,
     getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ getr R' 2%bv = Z_to_bv 64 sp
  /\ LB' = (ref, refsz) :: (obj - 128, objsz) :: LB
  /\ exc_at M' obj ref dtor
  /\ statics_landed M' gd' (xs_av st) (xs_uid st) (xs_rnd st) (xs_canary st) (xs_hw st).

Definition e1_landed (st : XS) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (sp : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) : Prop :=
  landed_core DTOR_SYSTEM_ERROR EXC1_SZ REF1_SZ st true LB sp M' R' LB'
  /\ credit_le (L5OMA.adebits L cr 2 (EXC1_SZ + REF1_SZ)) cr' /\ incl LK' LK.

Definition e2_landed (st : XS) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (sp : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) : Prop :=
  landed_core DTOR_RUNTIME_ERROR EXC23_SZ REF2_SZ st (xs_gd st) LB sp M' R' LB'
  /\ credit_le (L5OMA.adebits L cr 2 (EXC23_SZ + REF2_SZ)) cr' /\ incl LK' LK.

(* [comment removed for export] *)
Definition e3_landed (st : XS) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (sp : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) : Prop :=
  landed_core DTOR_RUNTIME_ERROR EXC23_SZ REF3_SZ st (xs_gd st) LB sp M' R' LB'
  /\ credit_le (L5OMA.adebits L cr 3 (EXC23_SZ + MSG3_SZ + REF3_SZ)) cr'
  /\ exists f LKm, LK' = f :: LKm /\ ff_class f = 1 /\ incl LKm LK.

(* [comment removed for export] *)
Definition lk_bound (LK LK' : list fframe) : Prop :=
  exists LX, incl LK' (LX ++ LK) /\ (length LX <= 1)%nat /\ Forall (fun f => ff_class f = 1) LX.
Lemma lk_bound_incl LK LK' : incl LK' LK -> lk_bound LK LK'.
Proof. intros H. exists []. split. exact H. split. cbn; lia. constructor. Qed.
Lemma e2_lk st LB FF LK cr sp M' R' LB' cr' LK' : e2_landed st LB FF LK cr sp M' R' LB' cr' LK' -> lk_bound LK LK'.
Proof. intros (_ & _ & H). apply lk_bound_incl. exact H. Qed.
Lemma e3_lk st LB FF LK cr sp M' R' LB' cr' LK' : e3_landed st LB FF LK cr sp M' R' LB' cr' LK' -> lk_bound LK LK'.
Proof.
  intros (_ & _ & (f & LKm & E & CF & I)). exists [f]. split. { subst LK'. intros x [<-|Hx]. left; reflexivity. right. apply I. exact Hx. }
  split. cbn; lia. constructor. exact CF. constructor.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithIface.
Variables (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition e2_chainA_spec : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LB : list (Z * Z)) (FF LK LKt : list fframe) (cr : credit) (A : list (Z * Z))
         (S SCR xo bo F1 fl1 F3 fl3 rt8 : Z) (st : XS),
    L5DSA.zero_throw_atA L ar SCR LB FF R0 M0 R M S xo bo F1 fl1 F3 fl3 ->
    getr R0 1%bv = Z_to_bv 64 OM1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 (hl_tp L) ->
    getr R0 9%bv = Z_to_bv 64 (S + 16) -> S mod 32 = 16 ->                         (* [comment removed for export] *)
    L5.u64_at RSEGS M S rt8 -> L5.u64_at RSEGS M (S + 8) L5OMA.OMF1_RET ->          (* [comment removed for export] *)
    xs_pre ar st M ->
    ri_inv HI LB (L5DSA.ff_e2 FF S F1 F3) LKt cr A M (vml_of model) -> amodel_ok A model -> K [] -> incl LKt LK ->
    astk ar M S SCR -> CHAIN_SCR <= SCR -> SCR mod 8 = 0 -> stksh ar M (S - SCR) ->
    L5OMA.acredit_for L cr 2 (EXC23_SZ + REF2_SZ) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        L5OMA.landed_regs R0 R' S rt8 ->
        e2_landed st LB FF LK cr (S + 16) M' R' LB' cr' LK' ->
        ahpres L ar LB FF S SCR xs_foot M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R ZERO_THROW M model) K.

(* [comment removed for export] *)
Definition e3_req : Type :=
  list (Z * Z) -> list (Z * Z) -> list fframe -> bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Z -> Z -> list (Z * Z) -> Prop.
Definition ff_e3_of (FF : list fframe) (S : Z) (FR : list (Z * Z)) : list fframe :=
  match map fst FR with
  | [F1a; F3a; F1b; F3b; F1c; F1d] => L5DSA.ff_e3 FF S F1a F3a F1b F3b F1c F1d
  | _ => FF
  end.
Definition e3_chainA_spec_of (req : e3_req) : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LBT LB1 : list (Z * Z)) (FF LK LKt : list fframe) (cr : credit) (A : list (Z * Z))
         (S SCR xo rt8 : Z) (FR : list (Z * Z)) (st : XS),
    req LBT LB1 FF R0 M0 R M S xo FR -> length FR = 6%nat ->
    getr R0 1%bv = Z_to_bv 64 OM1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 (hl_tp L) ->
    getr R0 9%bv = Z_to_bv 64 (S + 16) -> S mod 32 = 16 ->                         (* [comment removed for export] *)
    L5.u64_at RSEGS M S rt8 -> L5.u64_at RSEGS M (S + 8) L5OMA.OMF1_RET ->          (* [comment removed for export] *)
    xs_pre ar st M ->
    ri_inv HI (LBT ++ LB1) (ff_e3_of FF S FR) LKt cr A M (vml_of model) -> amodel_ok A model -> K [] -> incl LKt LK ->
    astk ar M S SCR -> CHAIN_SCR <= SCR -> SCR mod 8 = 0 -> stksh ar M (S - SCR) ->
    L5OMA.acredit_for L cr 3 (EXC23_SZ + MSG3_SZ + REF3_SZ) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        L5OMA.landed_regs R0 R' S rt8 ->
        e3_landed st LB1 FF LK cr (S + 16) M' R' LB' cr' LK' ->
        ahpres L ar LB1 FF S SCR xs_foot M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R ASSERT_THROW M model) K.

(* [comment removed for export] *)
Definition e1_chainA_spec (IL : icpt_layout) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (S SCR s0v s2v : Z) (st : XS),
    getr R 2%bv = Z_to_bv 64 (S - 32) -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    getr R 9%bv = Z_to_bv 64 22 -> getr R 18%bv = Z_to_bv 64 SB -> S mod 32 = 0 ->
    L5.u64_at RSEGS M (S - 8) E1_RET -> L5.u64_at RSEGS M (S - 16) s0v -> L5.u64_at RSEGS M (S - 24) S -> L5.u64_at RSEGS M (S - 32) s2v ->
    0 <= s0v < 2 ^ 64 -> 0 <= s2v < 2 ^ 64 ->
    xs_pre ar st M ->
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    astk ar M S SCR -> CHAIN_SCR <= SCR -> SCR mod 8 = 0 -> stksh ar M (S - SCR) ->
    L5OMA.acredit_for L cr 2 (EXC1_SZ + REF1_SZ) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit)
            (LK' : list fframe) (A' : list (Z * Z)),
        getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 S -> getr R' 18%bv = Z_to_bv 64 s2v ->
        (forall i, In i [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr R (reg i)) ->
        e1_landed st LB FF LK cr S M' R' LB' cr' LK' ->
        ahpres L ar LB FF S SCR xs_foot1 M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' E1_LANDING M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R STRCTOR_THROW M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition catchA_spec (dtor objsz refsz : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (obj ref S SCR : Z),
    ri_inv HI ((ref, refsz) :: (obj - 128, objsz) :: LB) FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 (obj - 32) ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> getr R 9%bv = Z_to_bv 64 S ->
    S mod 32 = 0 -> S + 64 <= 2 ^ 47 -> astk ar M S SCR -> CATCH_SCR <= SCR -> SCR mod 8 = 0 -> stksh ar M (S - SCR) ->
    exc_at M obj ref dtor ->
    L5.u64_at RSEGS M EH_CAUGHT 0 -> L5.u32_at RSEGS M EH_UNCAUGHT 1 ->
    L5.img_clear M 0x10000 0xd8000 -> L5.img_clear M 0xdab50 0xdab70 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
        regs_preserved R R' ->
        L5.u64_at RSEGS M' EH_CAUGHT 0 -> L5.u32_at RSEGS M' EH_UNCAUGHT 0 ->
        ahpres L ar LB FF S SCR [(EH_CAUGHT, 8); (EH_UNCAUGHT, 4)] M M' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' ->
        ri_inv HI LB FF LK cr A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg (fx:=fx') R' CATCH_RET M' model') K) ->
    srealizes RSEGS SCFG (cfg (fx:=fx) R CATCH M model) K.

Definition catch1A_spec : Prop := catchA_spec DTOR_SYSTEM_ERROR EXC1_SZ REF1_SZ.
Definition catch2A_spec : Prop := catchA_spec DTOR_RUNTIME_ERROR EXC23_SZ REF2_SZ.
Definition catch3A_spec : Prop := catchA_spec DTOR_RUNTIME_ERROR EXC23_SZ REF3_SZ.

End WithIface.
End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma xs_pre_e1 ar gd fl av uid rnd canary hw M :
  xs_pre ar (xs_of gd fl av uid rnd canary hw) M <-> e1_staticsA M gd fl av uid rnd canary hw /\ ar_sptop ar <= av.
Proof. unfold xs_pre, xs_of. cbn. tauto. Qed.

(* [comment removed for export] *)
Lemma landed_core_elim dtor objsz refsz st gd' LB sp M' R' LB' :
  landed_core dtor objsz refsz st gd' LB sp M' R' LB' ->
  exists obj ref, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1
    /\ LB' = (ref, refsz) :: (obj - 128, objsz) :: LB /\ exc_at M' obj ref dtor
    /\ L5.u64_at RSEGS M' EH_CAUGHT 0 /\ L5.u32_at RSEGS M' EH_UNCAUGHT 1
    /\ L5.img_clear M' 0x10000 0xd8000 /\ L5.img_clear M' 0xdab50 0xdab70.
Proof.
  intros (obj & ref & A0 & A1 & _ & ELB & EXC & (C0 & U1 & _ & _ & SC)). exists obj, ref.
  destruct SC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & I2 & _).
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma unw_statics_img : Forall (fun r => 0xd8000 <= fst r /\ fst r + snd r <= 0x634000) UNW_STATICS.
Proof. unfold UNW_STATICS. repeat (apply Forall_cons; [split; vm_compute; discriminate|]). apply Forall_nil. Qed.

End SCFG_1.
End L5USA.
