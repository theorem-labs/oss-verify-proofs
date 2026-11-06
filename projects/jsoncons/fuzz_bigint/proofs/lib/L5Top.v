(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreSpecs L5ParseSpecs L5DivSpecs BigModel BigFactsRun BigFactsDigits BigFactsOps.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState Mem Cells Step Frame Exec Tac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Ref Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5TopKit L5TopStretch.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5TOP.
Import L5CS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TOPK : Z := 8 * 64.                       (* [comment removed for export] *)
Definition TOPB (len : Z) : Z := 2 ^ 29 + 8 * len.   (* [comment removed for export] *)

Definition TopLay (L : heap_layout) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x20598;
  ll_gp := 67584;
  ll_empty := 0x6f8d0;
  ll_initc := [(0x70370, 0x70438); (0x906a8, 0x906b0); (0x906d0, 0x906d8); (0x90700, 0x90730)];
  ll_init_img := [(0x10000, 0x5f870); (0x6f8c5, 0x70368); (0x90440, 0x90460)];
  ll_td_self := 0x70370; ll_td_tid := 0x70390; ll_td_locale := 0x70408; ll_locale := 0x90700; ll_td_canary := 0x70428;
  ll_guard := 0x906a8; ll_auxvp := 0x906d0;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0x5f770;
  ll_stack := 65536;
  ll_credit := fun len => (TOPK, TOPB len);
  ll_foot := [(0x6f8f8, 0x6f908); (0x6fb20, 0x6fb22); (0x70361, 0x70367)] |}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition top_ls_ok (L : heap_layout) (g : bool * bool) (M : word -> option byte) : Prop :=
  exists av uid rnd canary hw, hl_sptop L <= av /\ L5PS.e1_statics M (fst g) (snd g) av uid rnd canary hw.

Definition TopLS (L : heap_layout) : lib_statics :=
  {| ls_state := (bool * bool)%type; ls_ok := top_ls_ok L; ls_g0 := (false, false) |}.

(* [comment removed for export] *)
Definition e1_dom (av a : Z) : Prop :=
  ((0x10000 <= a < 0x5f608) \/ (0x5f630 <= a < 0x5f650) \/ (0x5f660 <= a < 0x5f668)) \/ (0x6f8f8 <= a < 0x6f904) \/ (0x6fb20 <= a < 0x6fb22) \/ (0x70361 <= a < 0x70367)
  \/ (0x70408 <= a < 0x70410) \/ (0x906a8 <= a < 0x906b0) \/ (0x906d0 <= a < 0x906d8) \/ (0x90728 <= a < 0x90730)
  \/ (av <= a < av + 160).

Lemma u32_at_agree : forall M M' a v, L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros M M' a v AG Ha H4 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4 a Ha H4 AG). exact H. Qed.

Lemma e1_statics_agree : forall M M' gd fl av uid rnd canary hw,
  L5PS.e1_statics M gd fl av uid rnd canary hw ->
  (forall a, e1_dom av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5PS.e1_statics M' gd fl av uid rnd canary hw.
Proof.
  intros M M' gd fl av uid rnd canary hw ST AG.
  unfold L5PS.e1_statics, L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS, L5PS.TD_LOCALE, L5PS.GLOBAL_LOCALE,
    L5PS.LOCALE_MSGCAT, L5PS.CANARY, L5PS.AUXVP in *.
  destruct ST as (C1 & C2 & G1 & G2 & FL & TL & MC & CA & AX & AV8 & AVlo & AVhi & AW & Huid & Hrnd & Hcan & Hhw & I1 & I2 & I3).
  assert (A8 : forall a v, L5.u64_at RSEGS M a v -> (forall i, a <= i < a + 8 -> e1_dom av i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M' a v).
  { intros a v H D Ha H8. eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; apply D; exact Hi| exact Ha| exact H8| exact H]. }
  assert (A1 : forall a v, L5.u8_at RSEGS M a v -> e1_dom av a -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS M' a v).
  { intros a v H D Ha H1. eapply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; replace i with a by lia; exact D| exact Ha| exact H1| exact H]. }
  unfold e1_dom in *.
  repeat split.
  - apply A8; [exact C1| intros; lia| lia| lia].
  - eapply (u32_at_agree M M'); [intros i Hi; apply AG; lia| lia| lia| exact C2].
  - apply A1; [exact G1| lia| lia| lia].
  - apply A1; [exact G2| lia| lia| lia].
  - destruct fl.
    + destruct FL as (F1 & F2 & F3 & F4 & F5 & F6). repeat split; (apply A1; [assumption| lia| lia| lia]).
    + destruct FL as (F1 & F2 & F3). repeat split; (apply A1; [assumption| lia| lia| lia]).
  - apply A8; [exact TL| intros; lia| lia| lia].
  - apply A8; [exact MC| intros; lia| lia| lia].
  - apply A8; [exact CA| intros; lia| lia| lia].
  - apply A8; [exact AX| intros; lia| lia| lia].
  - exact AV8. - exact AVlo. - exact AVhi.
  - intros j Hj. apply A8; [apply AW; exact Hj| intros; lia| lia| lia].
  - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia.
  - intros i Hi. rewrite AG by lia. apply I1. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I2. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I3. exact Hi.
Qed.

(* [comment removed for export] *)
Definition statics_landed (M : word -> option byte) (gd : bool) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M L5PS.EH_CAUGHT 0 /\ L5.u32_at RSEGS M L5PS.EH_UNCAUGHT 1
  /\ L5.u8_at RSEGS M L5PS.SYSCAT_GUARD (if gd then 1 else 0) /\ L5.u8_at RSEGS M (L5PS.SYSCAT_GUARD + 1) (if gd then 1 else 0)
  /\ (L5.u8_at RSEGS M L5PS.UW_FLAGS 1 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 1) 0 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 2) 1
      /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 3) 0 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 4) 1 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 5) 0)
  /\ L5.u64_at RSEGS M L5PS.TD_LOCALE L5PS.GLOBAL_LOCALE /\ L5.u64_at RSEGS M L5PS.LOCALE_MSGCAT 0
  /\ L5.u64_at RSEGS M L5PS.CANARY canary /\ L5.u64_at RSEGS M L5PS.AUXVP av /\ av mod 8 = 0 /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47
  /\ (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (L5PS.auxv20 uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= canary < 2 ^ 64 /\ 0 <= hw < 2 ^ 64
  /\ L5.img_clear M 0x10000 0x5f608 /\ L5.img_clear M 0x5f630 0x5f650 /\ L5.img_clear M 0x5f660 0x5f668.

Lemma statics_landed_e1 : forall M M0 gd fl av uid rnd canary hw,
  L5PS.e1_statics M0 gd fl av uid rnd canary hw -> L5PS.e1_statics_landed M av uid rnd canary hw -> statics_landed M true av uid rnd canary hw.
Proof.
  intros M M0 gd fl av uid rnd canary hw ST SL.
  destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _ & Huid & Hrnd & Hcan & Hhw & _).
  destruct SL as (C1 & C2 & G1 & G2 & F1 & F2 & F3 & F4 & F5 & F6 & TL & MC & CA & AX & AW & I1 & I2 & I3).
  unfold statics_landed. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Definition e1_dom' (av a : Z) : Prop := e1_dom av a /\ ~ (0x6f8f8 <= a < 0x6f904).

Lemma statics_landed_agree : forall M M' gd av uid rnd canary hw,
  statics_landed M gd av uid rnd canary hw ->
  (forall a, e1_dom av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  statics_landed M' gd av uid rnd canary hw.
Proof.
  intros M M' gd av uid rnd canary hw ST AG.
  unfold statics_landed, L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS, L5PS.TD_LOCALE, L5PS.GLOBAL_LOCALE,
    L5PS.LOCALE_MSGCAT, L5PS.CANARY, L5PS.AUXVP in *.
  destruct ST as (C1 & C2 & G1 & G2 & (F1 & F2 & F3 & F4 & F5 & F6) & TL & MC & CA & AX & AV8 & AVlo & AVhi & AW & Huid & Hrnd & Hcan & Hhw & I1 & I2 & I3).
  assert (A8 : forall a v, L5.u64_at RSEGS M a v -> (forall i, a <= i < a + 8 -> e1_dom av i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M' a v).
  { intros a v H D Ha H8. eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; apply D; exact Hi| exact Ha| exact H8| exact H]. }
  assert (A1 : forall a v, L5.u8_at RSEGS M a v -> e1_dom av a -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS M' a v).
  { intros a v H D Ha H1. eapply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; replace i with a by lia; exact D| exact Ha| exact H1| exact H]. }
  unfold e1_dom in *.
  repeat split; try lia.
  - apply A8; [exact C1| intros; lia| lia| lia].
  - eapply (u32_at_agree M M'); [intros i Hi; apply AG; lia| lia| lia| exact C2].
  - apply A1; [exact G1| lia| lia| lia].
  - apply A1; [exact G2| lia| lia| lia].
  - apply A1; [exact F1| lia| lia| lia].
  - apply A1; [exact F2| lia| lia| lia].
  - apply A1; [exact F3| lia| lia| lia].
  - apply A1; [exact F4| lia| lia| lia].
  - apply A1; [exact F5| lia| lia| lia].
  - apply A1; [exact F6| lia| lia| lia].
  - apply A8; [exact TL| intros; lia| lia| lia].
  - apply A8; [exact MC| intros; lia| lia| lia].
  - apply A8; [exact CA| intros; lia| lia| lia].
  - apply A8; [exact AX| intros; lia| lia| lia].
  - intros j Hj. apply A8; [apply AW; exact Hj| intros; lia| lia| lia].
  - intros i Hi. rewrite AG by lia. apply I1. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I2. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I3. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma e1_statics_of_landed : forall M M' gd av uid rnd canary hw,
  statics_landed M gd av uid rnd canary hw ->
  (forall a, e1_dom' av a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  L5.u64_at RSEGS M' L5PS.EH_CAUGHT 0 -> L5.u32_at RSEGS M' L5PS.EH_UNCAUGHT 0 ->
  L5PS.e1_statics M' gd true av uid rnd canary hw.
Proof.
  intros M M' gd av uid rnd canary hw ST AG C1' C2'.
  unfold statics_landed, L5PS.e1_statics, L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS, L5PS.TD_LOCALE, L5PS.GLOBAL_LOCALE,
    L5PS.LOCALE_MSGCAT, L5PS.CANARY, L5PS.AUXVP in *.
  destruct ST as (C1 & C2 & G1 & G2 & (F1 & F2 & F3 & F4 & F5 & F6) & TL & MC & CA & AX & AV8 & AVlo & AVhi & AW & Huid & Hrnd & Hcan & Hhw & I1 & I2 & I3).
  assert (A8 : forall a v, L5.u64_at RSEGS M a v -> (forall i, a <= i < a + 8 -> e1_dom' av i) -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M' a v).
  { intros a v H D Ha H8. eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; apply D; exact Hi| exact Ha| exact H8| exact H]. }
  assert (A1 : forall a v, L5.u8_at RSEGS M a v -> e1_dom' av a -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS M' a v).
  { intros a v H D Ha H1. eapply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; replace i with a by lia; exact D| exact Ha| exact H1| exact H]. }
  unfold e1_dom', e1_dom in *.
  repeat split; try lia.
  - exact C1'.
  - exact C2'.
  - apply A1; [exact G1| lia| lia| lia].
  - apply A1; [exact G2| lia| lia| lia].
  - apply A1; [exact F1| lia| lia| lia].
  - apply A1; [exact F2| lia| lia| lia].
  - apply A1; [exact F3| lia| lia| lia].
  - apply A1; [exact F4| lia| lia| lia].
  - apply A1; [exact F5| lia| lia| lia].
  - apply A1; [exact F6| lia| lia| lia].
  - apply A8; [exact TL| intros; lia| lia| lia].
  - apply A8; [exact MC| intros; lia| lia| lia].
  - apply A8; [exact CA| intros; lia| lia| lia].
  - apply A8; [exact AX| intros; lia| lia| lia].
  - intros j Hj. apply A8; [apply AW; exact Hj| intros; lia| lia| lia].
  - intros i Hi. rewrite AG by lia. apply I1. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I2. exact Hi.
  - intros i Hi. rewrite AG by lia. apply I3. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma e1_img : forall M gd fl av uid rnd canary hw, L5PS.e1_statics M gd fl av uid rnd canary hw -> L5.img_clear M 0x10000 0x20000.
Proof.
  intros M gd fl av uid rnd canary hw ST.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG & _ & _).
  intros i Hi. apply IMG. lia.
Qed.

(* [comment removed for export] *)
Lemma vblk_bound : forall m, (m <= 4999)%nat -> 0 <= L5PS.vblk m <= 2144.
Proof.
  intros m Hm. unfold L5PS.vblk. destruct (Nat.ltb_spec m 39); [lia|].
  pose proof (num_words_est_4999 m Hm). pose proof (round_up_le (num_words_est m)). pose proof (round_up_gt (num_words_est m)). lia.
Qed.

Lemma digits_all : forall ds, L5PS.digits_ok ds -> all_digits ds = true.
Proof.
  intros ds H. unfold all_digits. apply forallb_forall. intros x Hx. unfold is_digit.
  pose proof (proj1 (List.Forall_forall _ _) H x Hx) as X. cbn in X. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma nwords_cap : forall ds, L5PS.digits_ok ds -> (length ds <= 4999)%nat -> (nwords (dec ds) <= 260)%nat.
Proof.
  intros ds D Hl. eapply Nat.le_trans; [| apply num_words_est_4999; exact Hl].
  apply nwords_bound. apply dec_bound. apply digits_all. exact D.
Qed.

Lemma reduced_wlist : forall V, 0 <= V -> L5DS.reduced (wlist V (nwords V)).
Proof.
  intros V HV. unfold L5DS.reduced. destruct (Z.eq_dec V 0) as [->|NZ]; [left; rewrite nwords_0; reflexivity| right].
  rewrite wlist_length. pose proof (nwords_pos V ltac:(lia)) as NP.
  change (nth (nwords V - 1) (wlist V (nwords V)) 0) with (nth_w (wlist V (nwords V)) (nwords V - 1)).
  rewrite wlist_nth by lia. apply wordi_top_nonzero. lia.
Qed.

Lemma split_sign_length : forall s, (length (snd (L5PS.split_sign s)) <= length s)%nat.
Proof. intros [|c t]; cbn; [lia|]. destruct (Z.eqb c 45); cbn; lia. Qed.

Lemma blocks_apart_sub : forall A n L1 L2, blocks_apart A n L1 -> (forall b, In b L2 -> In b L1) -> blocks_apart A n L2.
Proof. intros A n L1 L2 BA SUB b Hb. apply BA. apply SUB. exact Hb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TOP.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
(* [comment removed for export] *)
Let IMGLO : hl_img_lo L = 0x10000 := ly_img_lo L LY.
Let IMGHI : hl_img_hi L = 0x91000 := ly_img_hi L LY.
Hypothesis HIok : heap_iface_ok L SCFG HI.
(* [comment removed for export] *)
Hypothesis STRINIT : strinit_spec L HI.
Hypothesis COPYC : copy_spec L HI.
Hypothesis OPDELS : opdel_sized_spec L HI.
Hypothesis CSTR : L5PS.cstr_spec L HI.
Hypothesis STRCTOR : L5PS.strctor_spec L HI.
(* [comment removed for export] *)
Variable XS : Type.
Variable xs_pre : XS -> (word -> option byte) -> Prop.
Variable xs_foot : list L5.range.
Variable e2_landed e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.
Hypothesis OPMOD1 : L5DS.opmod1_spec L HI XS xs_pre xs_foot e2_landed e3_landed.
Hypothesis OPMOD2 : L5DS.opmod2_spec L HI.
(* [comment removed for export] *)
Variable xs_of : bool -> bool -> Z -> Z -> Z -> Z -> Z -> XS.
Hypothesis XSP : forall M gd fl av uid rnd canary hw, L5PS.e1_statics M gd fl av uid rnd canary hw -> hl_sptop L <= av -> xs_pre (xs_of gd fl av uid rnd canary hw) M.

(* [comment removed for export] *)
Definition CATCH : Z := 0x20810.
Definition CATCH_RET : Z := 0x20818.
Definition CATCH_SCR : Z := 112 + HEAP_STACK.     (* [comment removed for export] *)
Definition catch_spec (exc_at : (word -> option byte) -> Z -> list (Z * Z) -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB LBX : list (Z * Z)) (cr : credit) (obj S : Z),
    hi_heap HI (LBX ++ LB) cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 (obj - 32) ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 L5PS.GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M S CATCH_SCR ->
    exc_at M obj LBX ->
    L5.u64_at rsegs M L5PS.EH_CAUGHT 0 -> L5.u32_at rsegs M L5PS.EH_UNCAUGHT 1 ->
    L5.img_clear M 0x10000 0x5f608 -> L5.img_clear M 0x5f630 0x5f650 -> L5.img_clear M 0x5f660 0x5f668 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5.u64_at rsegs M' L5PS.EH_CAUGHT 0 -> L5.u32_at rsegs M' L5PS.EH_UNCAUGHT 0 ->
        L5C.hpres L LB S CATCH_SCR [(L5PS.EH_CAUGHT, 8); (L5PS.EH_UNCAUGHT, 4)] M M' ->
        model_but_vm model model' -> hi_heap HI LB cr M' (m_vmmaps model') ->
        srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 CATCH_RET) M' (seg_rom rsegs)) model') K) ->
    srealizes rsegs SCFG (mkCfg (mkst R (Z_to_bv 64 CATCH) M (seg_rom rsegs)) model) K.
(* [comment removed for export] *)
Variable exc1 exc2 exc3 : (word -> option byte) -> Z -> list (Z * Z) -> Prop.
Hypothesis CATCH1 : catch_spec exc1.
Hypothesis CATCH2 : catch_spec exc2.
Hypothesis CATCH3 : catch_spec exc3.
(* [comment removed for export] *)
Hypothesis EXC1_of_landing : forall LB0 M obj ref spL, L5PS.e1_exception_at M obj ref spL ->
  L5C.fresh_block L LB0 M (obj - 128) 160 -> L5C.fresh_block L ((obj - 128, 160) :: LB0) M ref 41 ->
  exc1 M obj [(ref, 41); (obj - 128, 160)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis E2L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  e2_landed (xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ exc2 M' obj LBX /\ statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 2 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (181 + 2 * hl_b_overhead L) <= snd cr'.   (* [comment removed for export] *)
Hypothesis E3L : forall gd fl av uid rnd canary hw LB1 cr1 Sx M' R' LB' cr',
  e3_landed (xs_of gd fl av uid rnd canary hw) LB1 cr1 Sx M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ exc3 M' obj LBX /\ statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 3 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (258 + 3 * hl_b_overhead L) <= snd cr'.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis EXC2_agree : forall M M' obj LBX, (forall b, In b LBX -> L5C.agree_on M M' (fst b) (snd b)) -> exc2 M obj LBX -> exc2 M' obj LBX.
Hypothesis EXC3_agree : forall M M' obj LBX, (forall b, In b LBX -> L5C.agree_on M M' (fst b) (snd b)) -> exc3 M obj LBX -> exc3 M' obj LBX.
(* [comment removed for export] *)
Hypothesis XSF : Forall (fun r => (0x6f8f8 <= fst r /\ fst r + snd r <= 0x6f908) \/ (0x6fb20 <= fst r /\ fst r + snd r <= 0x6fb22)
                                \/ (0x70361 <= fst r /\ fst r + snd r <= 0x70367)) xs_foot.

(* [comment removed for export] *)
Record toplay : Prop := TLY {
  tly_k : hl_k_per_malloc L = 8;
  tly_b : 0 <= hl_b_overhead L <= 2 ^ 23;
  tly_sptop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 }.   (* [comment removed for export] *)
Hypothesis TLY_ : toplay.
(* [comment removed for export] *)
Let SPW : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 := tly_sptop TLY_.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_footZ (a : Z) : Prop := (0x6f8f8 <= a < 0x6f908) \/ (0x6fb20 <= a < 0x6fb22) \/ (0x70361 <= a < 0x70367).

Lemma in_footZ_iff : forall a, in_foot (TopLay L) a <-> in_footZ a.
Proof.
  intros a. unfold in_foot, in_footZ. cbn [ll_foot TopLay]. split.
  - intros (iv & Hin & Hr). cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn in Hr; lia.
  - intros [H|[H|H]]; [exists (0x6f8f8, 0x6f908)| exists (0x6fb20, 0x6fb22)| exists (0x70361, 0x70367)]; cbn; auto.
Qed.

(* [comment removed for export] *)
Ltac hp_split H K D := pose proof (proj1 H) as K; first [pose proof (proj1 (proj2 H)) as D | pose proof (proj2 H) as D].

Definition topcl (LB : list (Z * Z)) (sp a : Z) : Prop :=
  0 <= a < 2 ^ 64 /\ client_addr L LB sp 65536 a /\ ~ in_errno L a /\ ~ in_footZ a.

Definition wok (LB : list (Z * Z)) (S : Z) (r : L5.range) : Prop :=
     (S <= fst r /\ fst r + snd r <= S + 216)
  \/ ((4096 <= fst r /\ (fst r + snd r <= hl_img_lo L \/ hl_img_hi L <= fst r)) /\ fst r + snd r <= hl_ceil L /\ blocks_apart (fst r) (snd r) LB)
  \/ (forall a, L5.in_rng r a -> in_footZ a).

Lemma topcl_outside : forall LB S W a, topcl LB (S + 240) a -> hl_sptop L - 2 ^ 23 <= S ->
  (forall b, In b LB -> (4096 <= fst b /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b)) /\ fst b + snd b <= hl_ceil L) ->
  Forall (wok LB S) W -> L5.outside W a.
Proof. clear IMGLO IMGHI.   (* [comment removed for export] *)
  intros LB S W a (Ha & CA & NE & NF) HS LBR FW r Hr In_r.
  pose proof (proj1 (List.Forall_forall _ _) FW r Hr) as WR. unfold L5.in_rng in In_r.
  pose proof (ly_img_hi L LY) as IH.
  destruct WR as [[W1 W2]|[(W1 & W2 & W3)|W3]].
  - destruct CA as [(b & Hb & Hrb)|[[A1 A2]|[A1 A2]]]; [destruct (LBR b Hb); lia| lia| lia].
  - destruct CA as [(b & Hb & Hrb)|[[A1 A2]|[A1 A2]]]; [pose proof (W3 b Hb); lia| lia| lia].
  - exact (NF (W3 a In_r)).
Qed.

Lemma topcl_kept : forall LB LBk S scr W a, topcl LB (S + 240) a -> hl_sptop L - 2 ^ 23 <= S ->
  (forall b, In b LB -> In b LBk) -> (forall b, In b LB -> (4096 <= fst b /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b)) /\ fst b + snd b <= hl_ceil L) ->
  0 <= scr <= 65536 - 240 -> Forall (wok LB S) W -> L5C.kept L LBk S scr W a.
Proof.
  clear IMGLO IMGHI.   (* [comment removed for export] *)
  intros LB LBk S scr W a TC HS SUB LBR Hscr FW. pose proof TC as (Ha & CA & NE & NF).
  split; [exact Ha|]. split; [| split; [exact NE| exact (topcl_outside LB S W a TC HS LBR FW)]].
  destruct CA as [(b & Hb & Hr)|[[A1 A2]|IM]]; [left; exists b; split; [apply SUB; exact Hb| exact Hr]| right; left; split; [exact A1| lia]| right; right; exact IM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cgrows (LBk : list (Z * Z)) (S scr : Z) (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> client_addr L LBk S scr a -> ~ in_errno L a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.

(* [comment removed for export] *)
Lemma HPG : forall LBk S scr W M M', L5C.hpres L LBk S scr W M M' -> cgrows LBk S scr M M'.
Proof. intros LBk S scr W M M' HP. exact (proj2 (proj2 HP)). Qed.

Definition TI (LB : list (Z * Z)) (S : Z) (M0 m1 Mk : word -> option byte) : Prop :=
     (forall a, topcl LB (S + 240) a -> Mk (Z_to_bv 64 a) = M0 (Z_to_bv 64 a))
  /\ (forall a, S + 240 - 65536 <= a < S -> Mk (Z_to_bv 64 a) <> None)
  /\ (forall a, S + 216 <= a < S + 240 -> Mk (Z_to_bv 64 a) = m1 (Z_to_bv 64 a))
  /\ (forall a, S <= a < S + 216 -> Mk (Z_to_bv 64 a) <> None).

Lemma TI_step : forall LB LBk S scr W M0 m1 Mk Mk1,
  TI LB S M0 m1 Mk -> L5C.hpres L LBk S scr W Mk Mk1 -> cgrows LBk S scr Mk Mk1 ->
  (forall b, In b LB -> In b LBk) -> (forall b, In b LB -> (4096 <= fst b /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b)) /\ fst b + snd b <= hl_ceil L) ->
  0 <= scr <= 65536 - 240 -> hl_sptop L - 2 ^ 23 + 65536 <= S + 240 -> S + 240 <= 2 ^ 47 -> Forall (wok LB S) W ->
  TI LB S M0 m1 Mk1.
Proof.
  intros LB LBk S scr W M0 m1 Mk Mk1 (T1 & T2 & T3 & T4) HP GROW SUB LBR Hscr Hlo Hhi FW. hp_split HP KEPT DEF.
  pose proof (ly_errno L LY) as HE. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in *.
  split; [| split; [| split]].
  4:{ intros a Ha. apply GROW; [lia| right; left; lia| unfold in_errno; rewrite HE; lia| apply T4; exact Ha]. }
  - intros a TC. rewrite <- (T1 a TC). apply KEPT. eapply topcl_kept; eauto; [lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); exact LBR].
  - intros a Ha. destruct (Z_lt_le_dec a (S - scr)) as [B|B].
    + rewrite KEPT; [apply T2; exact Ha|]. apply (L5C.kept_below L); [lia| lia| lia| rewrite HE; lia| lia|].
      intros r Hr In_r. pose proof (proj1 (List.Forall_forall _ _) FW r Hr) as [[W1 W2]|[(W1 & W2 & W3)|W3]]; unfold L5.in_rng in In_r; [lia| lia|].
      pose proof (W3 a In_r) as F. unfold in_footZ in F. lia.
    + eapply TK.defined_at; [exact DEF| lia].
  - intros a Ha. rewrite <- (T3 a Ha). apply KEPT. apply (L5C.kept_stack L); [lia| lia| lia| rewrite HE; lia| lia|].
    intros r Hr In_r. pose proof (proj1 (List.Forall_forall _ _) FW r Hr) as [[W1 W2]|[(W1 & W2 & W3)|W3]]; unfold L5.in_rng in In_r; [lia| lia|].
    pose proof (W3 a In_r) as F. unfold in_footZ in F. lia.
Qed.

(* [comment removed for export] *)
Lemma stat_step : forall LBk S scr W Mk Mk1 gd fl av uid rnd canary hw,
  L5PS.e1_statics Mk gd fl av uid rnd canary hw -> hl_sptop L <= av ->
  L5C.hpres L LBk S scr W Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S -> S + 240 <= hl_sptop L ->
  Forall (fun r => (S <= fst r /\ fst r + snd r <= S + 240) \/ ((4096 <= fst r /\ (fst r + snd r <= hl_img_lo L \/ hl_img_hi L <= fst r)) /\ fst r + snd r <= hl_ceil L)) W ->
  L5PS.e1_statics Mk1 gd fl av uid rnd canary hw.
Proof.
  intros LBk S scr W Mk Mk1 gd fl av uid rnd canary hw ST AVS HP Hscr Hlo Hhi FW. pose proof (proj1 HP) as KEPT.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVlo & AVhi & _).
  eapply e1_statics_agree; [exact ST|]. intros a Da. change Plain.M.loaded_segments with rsegs. apply KEPT.
  assert (OW : L5.outside W a).
  { intros r Hr In_r. pose proof (proj1 (List.Forall_forall _ _) FW r Hr) as [[W1 W2]|[W1 W2]]; unfold L5.in_rng in In_r;
      rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in *; unfold e1_dom in Da; lia. }
  unfold e1_dom in Da. destruct (Z_lt_le_dec a 0x90730) as [Lo|Hi].
  - apply (L5C.kept_static L); rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY), ?(ly_errno L LY); [lia| intros X; apply (ly_static L LY) in X; lia| lia| lia| lia| exact OW].
  - apply (L5C.kept_stack L); rewrite ?(ly_errno L LY); [lia| lia| lia| lia| lia| exact OW].
Qed.

(* [comment removed for export] *)
Lemma dom_kept : forall LBk S scr W Mk Mk1 av a,
  L5C.hpres L LBk S scr W Mk Mk1 -> hl_sptop L <= av -> 2 ^ 40 <= av -> av + 160 <= 2 ^ 47 ->
  0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S -> S + 240 <= hl_sptop L ->
  e1_dom av a -> L5.outside W a -> Mk1 (Z_to_bv 64 a) = Mk (Z_to_bv 64 a).
Proof.
  intros LBk S scr W Mk Mk1 av a HP AVS AVlo AVhi Hscr Hlo Hhi Da OW. apply (proj1 HP).
  unfold e1_dom in Da. destruct (Z_lt_le_dec a 0x90730) as [Lo|Hi].
  - apply (L5C.kept_static L); rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY), ?(ly_errno L LY); [lia| intros X; apply (ly_static L LY) in X; lia| lia| lia| lia| exact OW].
  - apply (L5C.kept_stack L); rewrite ?(ly_errno L LY); [lia| lia| lia| lia| lia| exact OW].
Qed.

Lemma landed_step : forall LBk S scr W Mk Mk1 gd av uid rnd canary hw,
  statics_landed Mk gd av uid rnd canary hw -> hl_sptop L <= av ->
  L5C.hpres L LBk S scr W Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S -> S + 240 <= hl_sptop L ->
  Forall (fun r => (S <= fst r /\ fst r + snd r <= S + 240) \/ ((4096 <= fst r /\ (fst r + snd r <= hl_img_lo L \/ hl_img_hi L <= fst r)) /\ fst r + snd r <= hl_ceil L)) W ->
  statics_landed Mk1 gd av uid rnd canary hw.
Proof.
  intros LBk S scr W Mk Mk1 gd av uid rnd canary hw ST AVS HP Hscr Hlo Hhi FW.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVlo & AVhi & _).
  eapply statics_landed_agree; [exact ST|]. intros a Da. change Plain.M.loaded_segments with rsegs.
  eapply dom_kept; [exact HP| exact AVS| exact AVlo| exact AVhi| exact Hscr| exact Hlo| exact Hhi| exact Da|].
  intros r Hr In_r. pose proof (proj1 (List.Forall_forall _ _) FW r Hr) as [[W1 W2]|[W1 W2]]; unfold L5.in_rng in In_r;
    rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in *; unfold e1_dom in Da; lia.
Qed.

Abbreviation reg i := (Z_to_bv 5 i).
Local Ltac greg REQ k := rewrite (TK.getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ REQ ltac:(lia)); cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add].

(* [comment removed for export] *)
Lemma hpres_refl : forall LBk S scr M, L5.defined M (S - scr) scr -> L5C.hpres L LBk S scr [] M M.
Proof. intros LBk S scr M D. split; [intros; reflexivity|]. first [exact D | split; [exact D| intros; assumption]]. Qed.

(* [comment removed for export] *)
Lemma dtor_call : forall (fx : FPState) (pc off k : Z) (S : Z) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
    (LBk : list (Z * Z)) (cr : credit) (b : L5.bigobj)
    (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  TS.dtor_stmt (wz S) pc off k -> L5.ra_ok k ->
  hl_sptop L - 2 ^ 23 + 65536 <= S + 240 -> S + 240 <= hl_sptop L -> hl_sptop L <= 2 ^ 47 -> S mod 16 = 0 -> 0 <= off <= 184 ->
  m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> K [] ->
  hi_heap HI LBk cr M (m_vmmaps model) ->
  regs_eqv (mkR ra (wz S) gp (Z_to_bv 64 TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R ->
  L5.big_at rsegs M (S + off) b ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBk) ->
  L5.defined M (S - OPDEL_SCR) OPDEL_SCR ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)),
      regs_preserved (mkR ra (wz S) gp (Z_to_bv 64 TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R' ->
      match L5.bo_st b with L5.BInl _ _ => LB' = LBk | L5.BDyn cap q => LB' = lb_remove q LBk end ->
      L5C.hpres L LB' S OPDEL_SCR [] M M' ->
      model_but_vm model model' -> hi_heap HI LB' cr M' (m_vmmaps model') ->
      srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 k) M' (seg_rom rsegs)) model') K) ->
  srealizes rsegs SCFG (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom rsegs)) model) K.
Proof.
  intros until t6. intros DT RAK SLO SHI STOP S16 OFF Mh Ml Mm HK0 HH REQ BIG INLB SDEF CONT.
  destruct b as [fb len st]. cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap L5.bo_data] in *.
  destruct BIG as (FB & FBR & LEN & REST).
  eapply (TK.srz_evt_canonMS _ R _ M model K Mh Ml).
  { rewrite (TK.canon_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R REQ).
    eapply DT with (fb := fb) (cap := match st with L5.BInl _ _ => 2 | L5.BDyn c _ => c end)
                             (q := match st with L5.BInl _ _ => S + off + 16 | L5.BDyn _ q => q end); rewrite ?wz_unsigned by lia.
    - apply TK.ro_cells_u8; [exact FB| lia| lia].
    - exact FBR.
    - intros DYN. destruct st as [v0 v1|cap q].
      + destruct REST as (TB0 & _). rewrite TB0 in DYN. discriminate.
      + destruct REST as (TB1 & U16 & U24 & LC & CAP & Q8 & QLO & QHI).
        split; [| lia]. split; [exact (conj I (conj I I))|].
        cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_app. split.
        * apply (TK.bytes_at_of_rdn M 8); [exact U16| apply (TK.rdn_length _ _ _ _ U16)| lia| lia].
        * cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite length_le8.
          replace (S + off + 16 + 8) with (S + off + 24) by lia.
          apply (TK.bytes_at_of_rdn M 8); [exact U24| apply (TK.rdn_length _ _ _ _ U24)| lia| lia]. }
  2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
  intros R1c pc1 m1 R1 (a0' & a1' & CASES) REQ1.
  destruct CASES as [[TB0 E]|(TB1 & -> & -> & E)]; inversion E; subst R1c pc1 m1; clear E.
  - (* [comment removed for export] *)
    apply (CONT fx R1 M model LBk).
    + eapply (TK.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 REQ1); reflexivity.
    + destruct st as [v0 v1|cap q]; [reflexivity|]. exfalso. destruct REST as (TB1 & _). rewrite TB1 in TB0. discriminate.
    + apply hpres_refl. exact SDEF.
    + apply L5C.model_but_vm_refl.
    + exact HH.
  - (* [comment removed for export] *)
    destruct st as [v0 v1|cap q].
    { exfalso. destruct REST as (TB0 & _). rewrite TB0 in TB1. discriminate. }
    eapply (OPDELS fx R1 M model K LBk cr q (8 * cap) S k).
    + exact HH.
    + split; [exact Mh| split; [exact Ml| exact Mm]].
    + exact HK0.
    + apply (INLB cap q). reflexivity.
    + greg REQ1 10. reflexivity.
    + greg REQ1 1. reflexivity.
    + exact RAK.
    + greg REQ1 2. reflexivity.
    + greg REQ1 4. reflexivity.
    + split; [exact S16|]. split; [unfold OPDEL_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia| exact SDEF].
    + intros fx' R' M' model' RP HP MBV HH'. unfold L5CS.cfg.
      apply (CONT fx' R' M' model' (lb_remove q LBk)); [| reflexivity| exact HP| exact MBV| exact HH'].
      intros r Hr. rewrite (RP r Hr).
      apply (TK.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (mkR ra (wz S) gp (Z_to_bv 64 TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R1 REQ1); try reflexivity. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_ok (R : bvmap 5 word) (S : Z) (Rk : bvmap 5 word) : Prop :=
  getr Rk 2%bv = wz S /\ getr Rk 3%bv = getr R 3%bv /\ getr Rk 4%bv = Z_to_bv 64 TP
  /\ getr Rk 18%bv = getr R 18%bv /\ getr Rk 19%bv = getr R 19%bv /\ getr Rk 20%bv = getr R 20%bv /\ getr Rk 21%bv = getr R 21%bv
  /\ getr Rk 22%bv = getr R 22%bv /\ getr Rk 23%bv = getr R 23%bv /\ getr Rk 24%bv = getr R 24%bv /\ getr Rk 25%bv = getr R 25%bv
  /\ getr Rk 26%bv = getr R 26%bv /\ getr Rk 27%bv = getr R 27%bv.

Lemma canon_cs : forall R S Rk, cs_ok R S Rk ->
  canon_regs Rk = mkR (getr Rk 1%bv) (wz S) (getr R 3%bv) (Z_to_bv 64 TP) (getr Rk 5%bv) (getr Rk 6%bv) (getr Rk 7%bv) (getr Rk 8%bv) (getr Rk 9%bv)
                      (getr Rk 10%bv) (getr Rk 11%bv) (getr Rk 12%bv) (getr Rk 13%bv) (getr Rk 14%bv) (getr Rk 15%bv) (getr Rk 16%bv) (getr Rk 17%bv)
                      (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv) (getr R 24%bv)
                      (getr R 25%bv) (getr R 26%bv) (getr R 27%bv) (getr Rk 28%bv) (getr Rk 29%bv) (getr Rk 30%bv) (getr Rk 31%bv).
Proof.
  intros R S Rk (E2 & E3 & E4 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27). unfold canon_regs.
  rewrite E2, E3, E4, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_of_eqv : forall R S Rk v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31,
  regs_eqv (mkR v1 (wz S) (getr R 3%bv) (Z_to_bv 64 TP) v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
                (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv) (getr R 24%bv)
                (getr R 25%bv) (getr R 26%bv) (getr R 27%bv) v28 v29 v30 v31) Rk ->
  cs_ok R S Rk.
Proof.
  intros until v31. intros H. unfold cs_ok.
  greg H 2. greg H 3. greg H 4. greg H 18. greg H 19. greg H 20. greg H 21. greg H 22. greg H 23. greg H 24. greg H 25. greg H 26. greg H 27.
  repeat split; reflexivity.
Qed.

Lemma cs_eqv : forall R S Rk, cs_ok R S Rk ->
  regs_eqv (mkR (getr Rk 1%bv) (wz S) (getr R 3%bv) (Z_to_bv 64 TP) (getr Rk 5%bv) (getr Rk 6%bv) (getr Rk 7%bv) (getr Rk 8%bv) (getr Rk 9%bv)
                (getr Rk 10%bv) (getr Rk 11%bv) (getr Rk 12%bv) (getr Rk 13%bv) (getr Rk 14%bv) (getr Rk 15%bv) (getr Rk 16%bv) (getr Rk 17%bv)
                (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv) (getr R 24%bv)
                (getr R 25%bv) (getr R 26%bv) (getr R 27%bv) (getr Rk 28%bv) (getr Rk 29%bv) (getr Rk 30%bv) (getr Rk 31%bv)) Rk.
Proof. intros R S Rk CS. rewrite <- (canon_cs R S Rk CS). apply regs_eqv_sym. apply canon_regs_eqv. Qed.

(* [comment removed for export] *)
Lemma cs_ok_canon_call : forall (R : bvmap 5 word) (S : Z) (Rk R1 : bvmap 5 word) (v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
  regs_preserved (mkR v1 (wz S) (getr R 3%bv) (Z_to_bv 64 TP) v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
                (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv) (getr R 24%bv)
                (getr R 25%bv) (getr R 26%bv) (getr R 27%bv) v28 v29 v30 v31) R1 ->
  cs_ok R S R1.
Proof using SPW.
  intros until v31. intros RP. unfold cs_ok. rewrite !RP by (cbn; tauto). unfold getr; cbn. repeat split; reflexivity.
Qed.

Lemma cs_ok_call : forall R S R1 R2, cs_ok R S R1 -> regs_preserved R1 R2 -> cs_ok R S R2.
Proof using SPW.
  intros R S R1 R2 (E2 & E3 & E4 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27) RP. unfold cs_ok.
  rewrite !RP by (cbn; tauto). repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASES.
Variables (R : bvmap 5 word) (M0 m1 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit).
Variables (S ra : Z) (payload : list byte) (junk : list byte) (av uid rnd canary hw : Z).
Let len : Z := Z.of_nat (length payload).
Hypothesis CONT : forall (fx' : FPState) (g' : bool * bool) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (cr' : credit),
    lib_post (TopLay L) (TopLS L) g' LB cr (S + 240) payload R M0 R' M' cr' ->
    hi_heap HI LB cr' M' (m_vmmaps model') -> model_but_vm model0 model' ->
    srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom rsegs)) model') K.
Hypothesis Rsp : getr R 2%bv = Z_to_bv 64 (S + 240).
Hypothesis Rgp : getr R 3%bv = Z_to_bv 64 67584.
Hypothesis Rtp : getr R 4%bv = Z_to_bv 64 TP.
Hypothesis RAok : L5.ra_ok ra.
Hypothesis SLO : hl_sptop L - 2 ^ 23 + 65536 <= S + 240.
Hypothesis SHI : S + 240 <= hl_sptop L.
Hypothesis STOP : hl_sptop L <= 2 ^ 47.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK0 : K [].
Hypothesis LBR : forall b, In b LB -> (4096 <= fst b /\ (fst b + snd b <= hl_img_lo L \/ hl_img_hi L <= fst b)) /\ fst b + snd b <= hl_ceil L.
Hypothesis CRK : TOPK <= fst cr.
Hypothesis CRB : TOPB len <= snd cr.
Hypothesis AVS : hl_sptop L <= av.
Hypothesis FR1 : rw_cells rsegs m1 S [CB 216 junk; C8 (getr R 9%bv); C8 (getr R 8%bv); C8 (Z_to_bv 64 ra)].
Hypothesis LEN : len < 2 ^ 26.
Hypothesis Mh0 : m_halted model0 = None.
Hypothesis Ml0 : m_vm_lazy model0 = [].
Hypothesis Mm0 : m_vm_materialized model0 = [].

(* [comment removed for export] *)
Lemma ph_end : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool),
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LB crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk -> m_halted modelk = None -> m_vm_lazy modelk = [] ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x2070c) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fl. intros TIk ST HH MBV Mh Ml CK CB CS. pose proof TIk as (T1 & T2 & T3 & FDEF).
  assert (SAVED : ro_cells rsegs Mk (S + 216) [C8 (getr R 9%bv); C8 (getr R 8%bv); C8 (Z_to_bv 64 ra)]).
  { pose proof (TK.ro_cells_skip1 _ _ _ _ (TK.ro_of_rw _ _ _ FR1)) as X. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
    eapply TK.ro_cells_agree; [exact X|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. unfold wa. apply T3. lia. }
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS).
    eapply (TS.s17 (wz S)). rewrite wz_unsigned by lia. exact SAVED. }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R6c pc6 m6 R6 E REQ6. inversion E; subst R6c pc6 m6; clear E.
  rewrite (TK.ret_pc_lit ra RAok).
  eapply (CONT fx (gd, fl) R6 Mk modelk crk); [| exact HH| exact MBV].
  constructor.
  - greg REQ6 10. reflexivity.
  - eapply (TK.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R6 REQ6); try reflexivity.
    + rewrite Rsp. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
    + rewrite Rtp. reflexivity.
  - cbn [ll_credit TopLay fst snd credit_sub credit_le]. unfold credit_le, credit_sub. cbn [fst snd]. subst len. lia.
  - cbn [ll_stack ll_heap TopLay]. intros a Ha CA NF NE. apply T1. split; [exact Ha|]. split; [exact CA|]. split; [exact NE|].
    intros F. apply NF. apply in_footZ_iff. exact F.
  - cbn [ll_stack TopLay]. intros a Ha.
    destruct (Z_lt_le_dec a S) as [B1|B1]; [apply T2; lia|].
    destruct (Z_lt_le_dec a (S + 216)) as [B2|B2]; [apply FDEF; lia|].
    rewrite T3 by lia. pose proof (proj2 FR1) as (W0 & W1 & WR). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in WR.
    specialize (WR (a - S) ltac:(lia)). replace (S + (a - S)) with a in WR by lia.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia). unfold wa in WR. exact WR.
  - cbn [ls_ok TopLS]. exists av, uid, rnd, canary, hw. split; [exact AVS| exact ST].
Qed.
(* [comment removed for export] *)
Lemma cgrows_nil : forall LBk Sx scr M M', L5C.hpres L LBk Sx scr [] M M' -> cgrows LBk Sx scr M M'.
Proof.
  intros LBk Sx scr M M' HP a Ha CA NE D. rewrite (proj1 HP a); [exact D|]. split; [exact Ha|]. split; [exact CA|]. split; [exact NE|]. intros r [].
Qed.

Definition ostr (sk : option (Z * Z)) : list (Z * Z) := match sk with None => [] | Some b => [b] end.

(* [comment removed for export] *)
Definition str_at (Mk : word -> option byte) (sk : option (Z * Z)) : Prop :=
  match sk with
  | None => exists b0, L5.u8_at rsegs Mk (S + 192) b0 /\ 0 <= b0 < 256 /\ Z.testbit b0 0 = false
  | Some (p, cap) => exists w0, L5.u64_at rsegs Mk (S + 192) w0 /\ L5.u64_at rsegs Mk (S + 208) p /\ Z.testbit w0 0 = true
                     /\ 0 <= w0 < 2 ^ 64 /\ 0 < cap /\ (4096 <= p /\ (p + cap <= hl_img_lo L \/ hl_img_hi L <= p)) /\ p + cap <= hl_ceil L
  end.

Lemma str_at_kept_nil : forall LBk scr Mk Mk1 sk, L5C.hpres L LBk S scr [] Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  str_at Mk sk -> str_at Mk1 sk.
Proof.
  intros LBk scr Mk Mk1 sk HP Hscr Hlo ST.
  assert (AG : forall o n, S <= o -> o + n <= S + 240 -> L5C.agree_on Mk Mk1 o n).
  { intros o n Ho Hn i Hi. apply (proj1 HP). apply (L5C.kept_stack L); [lia| lia| lia| rewrite (ly_errno L LY); lia| lia| intros r []]. }
  destruct sk as [[p cap]|].
  - destruct ST as (w0 & U0 & U16 & TB & W0 & C0 & P0 & PC). exists w0. repeat split; try assumption; try lia.
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [apply AG; lia| lia| lia| exact U0].
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [apply AG; lia| lia| lia| exact U16].
  - destruct ST as (b0 & U0 & B0 & TB). exists b0. repeat split; try assumption; try lia.
    eapply (L5C.u8_at_agree rsegs Mk Mk1); [apply AG; lia| lia| lia| exact U0].
Qed.

(* [comment removed for export] *)
Lemma ph_strdtor : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk : option (Z * Z)),
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI (ostr sk ++ LB) crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  str_at Mk sk ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x206f0) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until sk. intros TIk ST HH MBV Mh Ml Mm CK CB SK CS. pose proof TIk as (T1 & T2 & T3 & T4).
  assert (SR' : 0x7fff7f800000 <= bv_unsigned (wz S) /\ bv_unsigned (wz S) + 240 <= 2 ^ 47) by (rewrite wz_unsigned by lia; lia).
  destruct sk as [[p cap]|].
  - (* [comment removed for export] *)
    destruct SK as (w0 & U0 & U16 & TB & W0R & CAP0 & P0 & PHI).
    eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
    { rewrite (canon_cs R S Rk CS).
      eapply (TS.s16 (wz S)) with (b0 := w0 mod 256) (w0 := w0) (p := p); rewrite ?wz_unsigned by lia.
      + apply TK.ro_cells_u8; [| lia| lia]. apply TK.u8_of_u64; [exact U0| lia].
      + pose proof (Z.mod_pos_bound w0 256). lia.
      + intros _. split; [| split; [| lia]].
        * apply TK.ro_cells_u64; [exact U0| lia| lia].
        * apply TK.ro_cells_u64; [exact U16| lia| lia]. }
    2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
    intros R4c pc4 m4 R4 (a0' & a1' & CASES) REQ4.
    destruct CASES as [[TB0 E]|(TB1 & -> & -> & E)].
    { exfalso. change 256 with (2 ^ 8) in TB0. rewrite Z.mod_pow2_bits_low in TB0 by lia. rewrite TB in TB0. discriminate. }
    inversion E; subst R4c pc4 m4; clear E.
    eapply (OPDELS fx R4 Mk modelk K ((p, cap) :: LB) crk p cap S 0x2070c).
    + exact HH.
    + split; [exact Mh| split; [exact Ml| exact Mm]].
    + exact HK0.
    + left. reflexivity.
    + greg REQ4 10. reflexivity.
    + greg REQ4 1. reflexivity.
    + split; [lia| reflexivity].
    + greg REQ4 2. reflexivity.
    + greg REQ4 4. reflexivity.
    + split; [exact S16|]. split; [unfold OPDEL_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
      intros i Hi. apply T2. unfold OPDEL_SCR, HEAP_STACK in Hi |- *. lia.
    + intros fx2 R5 M5 model5 RP45 HPRES5 MBV5 HH5. unfold L5CS.cfg.
      pose proof (L5C.halted_but_vm _ _ MBV5) as Mh5. rewrite Mh in Mh5.
      pose proof (L5C.lazy_but_vm _ _ MBV5) as Ml5. rewrite Ml in Ml5.
      replace (lb_remove p ((p, cap) :: LB)) with LB in HPRES5, HH5 by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
      assert (TI5 : TI LB S M0 m1 M5).
      { eapply (TI_step LB LB S OPDEL_SCR []); [exact TIk| exact HPRES5| apply cgrows_nil; exact HPRES5| auto| exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor]. }
      eapply (ph_end fx2 R5 M5 model5 crk gd fl); [exact TI5| | exact HH5| eapply L5C.model_but_vm_trans; [exact MBV| exact MBV5]| exact Mh5| exact Ml5| lia| lia|].
      * eapply (stat_step LB S OPDEL_SCR []); [exact ST| exact AVS| exact HPRES5| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor].
      * eapply cs_ok_call; [| exact RP45]. eapply cs_ok_of_eqv. exact REQ4.
  - (* [comment removed for export] *)
    destruct SK as (b0 & UB0 & B0R & TBF).
    eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
    { rewrite (canon_cs R S Rk CS).
      eapply (TS.s16 (wz S)) with (b0 := b0) (w0 := 0) (p := 0); rewrite ?wz_unsigned by lia.
      + apply TK.ro_cells_u8; [exact UB0| lia| lia].
      + lia.
      + intros TB1. exfalso. rewrite TBF in TB1. discriminate. }
    2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
    intros R4c pc4 m4 R4 (a0' & a1' & CASES) REQ4.
    destruct CASES as [[TB0 E]|(TB1 & -> & -> & E)].
    2:{ exfalso. rewrite TBF in TB1. discriminate. }
    inversion E; subst R4c pc4 m4; clear E.
    eapply (ph_end fx R4 Mk modelk crk gd fl); [exact TIk| exact ST| exact HH| exact MBV| exact Mh| exact Ml| lia| lia| eapply cs_ok_of_eqv; exact REQ4].
Qed.
(* [comment removed for export] *)
Lemma big_kept_nil : forall LBk scr Mk Mk1 o b, L5C.hpres L LBk S scr [] Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  S <= o -> o + 32 <= S + 240 -> L5.big_at rsegs Mk o b -> L5.big_at rsegs Mk1 o b.
Proof.
  intros LBk scr Mk Mk1 o b HP Hscr Hlo Ho Hhi B. eapply (L5C.big_at_agree rsegs Mk Mk1); [| lia| lia| exact B].
  intros i Hi. apply (proj1 HP). apply (L5C.kept_stack L); [lia| lia| lia| rewrite (ly_errno L LY); lia| lia| intros r []].
Qed.
Lemma lstr_short_kept_nil : forall LBk scr Mk Mk1 o str, L5C.hpres L LBk S scr [] Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  S <= o -> o + 24 <= S + 240 -> L5.lstr_short rsegs Mk o str -> L5.lstr_short rsegs Mk1 o str.
Proof.
  intros LBk scr Mk Mk1 o str HP Hscr Hlo Ho Hhi B. eapply (L5C.lstr_short_agree rsegs Mk Mk1); [| lia| lia| exact B].
  intros i Hi. apply (proj1 HP). apply (L5C.kept_stack L); [lia| lia| lia| rewrite (ly_errno L LY); lia| lia| intros r []].
Qed.

(* [comment removed for export] *)
Definition obj_at (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (blk : option (Z * Z)) : Prop :=
  L5.big_at rsegs Mk o b /\
  match L5.bo_st b with
  | L5.BInl _ _ => blk = None
  | L5.BDyn cap q => blk = Some (q, 8 * cap)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGS (W : list L5.range) (Mk Mk1 : word -> option byte) : Prop :=
  forall a, S <= a < S + 240 -> L5.outside W a -> Mk1 (Z_to_bv 64 a) = Mk (Z_to_bv 64 a).
Definition apart (o n : Z) (W : list L5.range) : Prop := Forall (fun r => o + n <= fst r \/ fst r + snd r <= o) W.

Lemma ags_hpres : forall LBk scr W Mk Mk1, L5C.hpres L LBk S scr W Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S -> AGS W Mk Mk1.
Proof. intros LBk scr W Mk Mk1 HP Hscr Hlo a Ha OW. apply (proj1 HP). apply (L5C.kept_stack L); [lia| lia| lia| rewrite (ly_errno L LY); lia| lia| exact OW]. Qed.

Lemma ags_agree : forall W Mk Mk1 o n, AGS W Mk Mk1 -> S <= o -> o + n <= S + 240 -> apart o n W -> L5C.agree_on Mk Mk1 o n.
Proof using S16 SLO SPW len.
  intros W Mk Mk1 o n AG Ho Hn AP i Hi. apply AG; [lia|]. intros r Hr In_r.
  pose proof (proj1 (List.Forall_forall _ _) AP r Hr) as X. cbn in X. unfold L5.in_rng in In_r. lia.
Qed.

Lemma big_kept : forall W Mk Mk1 o b, AGS W Mk Mk1 -> S <= o -> o + 32 <= S + 240 -> apart o 32 W ->
  L5.big_at rsegs Mk o b -> L5.big_at rsegs Mk1 o b.
Proof using S16 SHI SLO SPW STOP len. intros W Mk Mk1 o b AG Ho Hn AP B. eapply (L5C.big_at_agree rsegs Mk Mk1); [eapply ags_agree; eauto| lia| lia| exact B]. Qed.

Lemma obj_at_kept : forall W Mk Mk1 o b blk, AGS W Mk Mk1 -> S <= o -> o + 32 <= S + 240 -> apart o 32 W ->
  obj_at Mk o b blk -> obj_at Mk1 o b blk.
Proof using S16 SHI SLO SPW STOP len. intros W Mk Mk1 o b blk AG Ho Hn AP [B E]. split; [eapply big_kept; eauto| exact E]. Qed.

Lemma str_at_kept : forall W Mk Mk1 sk, AGS W Mk Mk1 -> apart (S + 192) 24 W -> str_at Mk sk -> str_at Mk1 sk.
Proof using S16 SHI SLO SPW STOP len.
  intros W Mk Mk1 sk AG AP ST.
  assert (A8 : forall o, S + 192 <= o -> o + 8 <= S + 216 -> L5C.agree_on Mk Mk1 o 8).
  { intros o Ho Hn. eapply ags_agree; [exact AG| lia| lia|]. eapply List.Forall_impl; [| exact AP]. intros r Hr. cbn in Hr |- *. lia. }
  destruct sk as [[p cap]|].
  - destruct ST as (w0 & U0 & U16 & TB & W0 & C0 & P0 & PC). exists w0. repeat split; try assumption; try lia.
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [apply A8; lia| lia| lia| exact U0].
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [apply A8; lia| lia| lia| exact U16].
  - destruct ST as (b0 & U0 & B0 & TB). exists b0. repeat split; try assumption; try lia.
    eapply (L5C.u8_at_agree rsegs Mk Mk1); [| lia| lia| exact U0]. intros i Hi. apply (A8 (S + 192)); lia.
Qed.

(* [comment removed for export] *)
Lemma blk_agree : forall LBk scr W Mk Mk1 q n, L5C.hpres L LBk S scr W Mk Mk1 -> In (q, n) LBk ->
  (4096 <= q /\ (q + n <= hl_img_lo L \/ hl_img_hi L <= q)) -> q + n <= hl_ceil L -> apart q n W -> L5C.agree_on Mk Mk1 q n.
Proof using LY S16 SLO SPW STOP len.
  intros LBk scr W Mk Mk1 q n HP IN Hlo Hhi AP i Hi. apply (proj1 HP). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in Hlo.
  eapply (L5C.kept_block L LBk S scr W q n); [exact IN| lia| lia| lia| rewrite (ly_errno L LY); lia|].
  intros r Hr In_r. pose proof (proj1 (List.Forall_forall _ _) AP r Hr) as X. cbn in X. unfold L5.in_rng in In_r. lia.
Qed.

(* [comment removed for export] *)
Lemma limbs_kept : forall LBk scr W Mk Mk1 b ws, L5C.hpres L LBk S scr W Mk Mk1 ->
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LBk /\ (4096 <= q /\ (q + 8 * cap <= hl_img_lo L \/ hl_img_hi L <= q)) /\ q + 8 * cap <= hl_ceil L /\
                                                Z.of_nat (L5.bo_len b) <= cap /\ apart q (8 * cap) W) ->
  L5C.obj_limbs rsegs Mk b ws -> L5C.obj_limbs rsegs Mk1 b ws.
Proof using LY S16 SLO SPW STOP len.
  intros LBk scr W Mk Mk1 b ws HP DY (LEN' & RNG & LM). split; [exact LEN'|]. split; [exact RNG|].
  destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E; [exact LM|].
  destruct (DY cap q eq_refl) as (IN & Hlo & Hhi & LC & AP). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in Hlo.
  eapply (L5C.limbs_at_agree rsegs Mk Mk1); [| lia| lia| exact LM].
  intros i Hi. eapply (blk_agree LBk scr W Mk Mk1 q (8 * cap) HP IN); [rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| exact AP| lia].
Qed.

(* [comment removed for export] *)
Lemma hpres_frame : forall LBk scr W Mk Mk1, L5.frame_but W Mk Mk1 -> mem_grows Mk Mk1 -> L5.defined Mk (S - scr) scr ->
  L5C.hpres L LBk S scr W Mk Mk1 /\ cgrows LBk S scr Mk Mk1.
Proof.
  intros LBk scr W Mk Mk1 FB MG D. split; [split|].
  - intros a (Ha & _ & _ & OW). apply FB. rewrite L5.unsigned_lit by exact Ha. exact OW.
  - first [eapply L5.defined_grows; [exact MG| exact D] | split; [eapply L5.defined_grows; [exact MG| exact D]| intros a _ _ _ X; apply MG; exact X]].
  - intros a _ _ _ X. apply MG. exact X.
Qed.

Lemma obj_at_kept_nil : forall LBk scr Mk Mk1 o b blk, L5C.hpres L LBk S scr [] Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  S <= o -> o + 32 <= S + 240 -> obj_at Mk o b blk -> obj_at Mk1 o b blk.
Proof. intros LBk scr Mk Mk1 o b blk HP A B C D [H1 H2]. split; [eapply big_kept_nil; eauto| exact H2]. Qed.

Lemma lb_remove_app_skip : forall q l1 l2, ~ In q (map fst l1) -> lb_remove q (l1 ++ l2) = l1 ++ lb_remove q l2.
Proof.
  intros q l1 l2 H. induction l1 as [|[c m] l1 IH]; [reflexivity|]. cbn [lb_remove fst app map In] in *.
  destruct (Z.eqb_spec c q); [exfalso; apply H; left; exact e|]. cbn. rewrite IH; [reflexivity|]. intros X; apply H; right; exact X.
Qed.
Lemma lb_remove_mid : forall l1 q n l2, NoDup (map fst (l1 ++ (q, n) :: l2)) -> lb_remove q (l1 ++ (q, n) :: l2) = l1 ++ l2.
Proof.
  intros l1 q n l2 ND. rewrite map_app in ND. apply (proj1 (list_relations.list.NoDup_app _ _)) in ND as (_ & NI & _).
  rewrite lb_remove_app_skip.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity.
  - intros IN. apply (NI q); [apply list_elem_of_In; exact IN|]. cbn [map fst]. apply list_elem_of_here.
Qed.

(* [comment removed for export] *)
Lemma ph_dtors : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk oy od oc ob : option (Z * Z)) (byo bd bc bb ba : L5.bigobj),
  let LBk := ostr od ++ ostr oy ++ ostr oc ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  str_at Mk sk -> match sk with None => True | Some (p, cap) => 0 < cap end ->
  obj_at Mk S byo oy -> obj_at Mk (S + 32) bd od -> obj_at Mk (S + 96) bc oc -> obj_at Mk (S + 128) bb ob ->
  L5.big_at rsegs Mk (S + 160) ba -> L5.bo_dyn ba = false ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x20650) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until ba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR SKP OY OD OC OB BA BAI CS.
  assert (DEFS : forall M', TI LB S M0 m1 M' -> L5.defined M' (S - OPDEL_SCR) OPDEL_SCR).
  { intros M' (_ & T2 & _). intros i Hi. apply T2. unfold OPDEL_SCR, HEAP_STACK in Hi |- *. lia. }
  assert (RA1 : L5.ra_ok 0x20670) by (split; [lia| reflexivity]).
  assert (RA2 : L5.ra_ok 0x20690) by (split; [lia| reflexivity]).
  assert (RA3 : L5.ra_ok 0x206b0) by (split; [lia| reflexivity]).
  assert (RA4 : L5.ra_ok 0x206d0) by (split; [lia| reflexivity]).
  assert (RA5 : L5.ra_ok 0x206f0) by (split; [lia| reflexivity]).
  (* [comment removed for export] *)
  eapply (dtor_call fx 0x20650 0 0x20670 S Rk Mk modelk K LBk crk byo); try eassumption; try lia.
  { apply TS.d_y; rewrite ?wz_unsigned by lia; lia. }
  { replace (S + 0) with S by lia. apply (cs_eqv R S Rk CS). }
  { replace (S + 0) with S by lia. exact (proj1 OY). }
  { intros cap q E. destruct OY as [_ OYB]. rewrite E in OYB. subst oy LBk. apply in_app_iff. right. left. reflexivity. }
  { apply DEFS. exact TIk. }
  intros fx1 R1 M1 model1 LB1 RP1 ELB1 HP1 MBV1 HH1.
  pose proof (L5C.halted_but_vm _ _ MBV1) as Mh1. rewrite Mh in Mh1.
  pose proof (L5C.lazy_but_vm _ _ MBV1) as Ml1. rewrite Ml in Ml1.
  pose proof (L5C.materialized_but_vm _ _ MBV1) as Mm1. rewrite Mm in Mm1.
  assert (ELB1' : LB1 = ostr od ++ ostr oc ++ ostr ob ++ ostr sk ++ LB).
  { destruct OY as [_ OYB]. destruct (L5.bo_st byo) as [v0 v1|cap q]; subst oy; rewrite ELB1; [reflexivity|]. subst LBk.
    apply (lb_remove_mid (ostr od) q (8 * cap)). exact (proj1 (proj2 (hio_wf L SCFG HI HIok _ _ _ _ HH))). }
  clear ELB1. subst LB1.
  assert (TI1 : TI LB S M0 m1 M1).
  { eapply (TI_step LB _ S OPDEL_SCR []); [exact TIk| exact HP1| apply cgrows_nil; exact HP1| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (ST1 : L5PS.e1_statics M1 gd fl av uid rnd canary hw).
  { eapply (stat_step _ S OPDEL_SCR []); [exact ST| exact AVS| exact HP1| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor]. }
  pose proof (cs_ok_canon_call R S Rk R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP1) as CS1.
  pose proof (str_at_kept_nil _ _ _ _ sk HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) STR) as STR1.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 32) _ _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OD) as OD1.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 96) _ _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OC) as OC1.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 128) _ _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OB) as OB1.
  pose proof (big_kept_nil _ _ _ _ (S + 160) _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) BA) as BA1.
  pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV1) as MBV1'.
  clear TIk ST CS STR OY OD OC OB BA HP1 MBV MBV1 RP1 HH Mh Ml Mm Rk Mk modelk.
  (* [comment removed for export] *)
  eapply (dtor_call fx1 0x20670 32 0x20690 S R1 M1 model1 K _ crk bd); try eassumption; try lia.
  { apply TS.d_d; rewrite ?wz_unsigned by lia; lia. }
  { apply (cs_eqv R S R1 CS1). }
  { exact (proj1 OD1). }
  { intros cap q E. destruct OD1 as [_ ODB]. rewrite E in ODB. subst od. apply in_app_iff. left. left. reflexivity. }
  { apply DEFS. exact TI1. }
  intros fx2 R2 M2 model2 LB2 RP2 ELB2 HP2 MBV2 HH2.
  pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh1 in Mh2.
  pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml1 in Ml2.
  pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm1 in Mm2.
  assert (ELB2' : LB2 = ostr oc ++ ostr ob ++ ostr sk ++ LB).
  { destruct OD1 as [_ ODB]. destruct (L5.bo_st bd) as [v0 v1|cap q]; subst od; rewrite ELB2; [reflexivity|].
    apply (lb_remove_mid [] q (8 * cap)). exact (proj1 (proj2 (hio_wf L SCFG HI HIok _ _ _ _ HH1))). }
  clear ELB2. subst LB2.
  assert (TI2 : TI LB S M0 m1 M2).
  { eapply (TI_step LB _ S OPDEL_SCR []); [exact TI1| exact HP2| apply cgrows_nil; exact HP2| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (ST2 : L5PS.e1_statics M2 gd fl av uid rnd canary hw).
  { eapply (stat_step _ S OPDEL_SCR []); [exact ST1| exact AVS| exact HP2| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor]. }
  pose proof (cs_ok_canon_call R S R1 R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as CS2.
  pose proof (str_at_kept_nil _ _ _ _ sk HP2 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) STR1) as STR2.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 96) _ _ HP2 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OC1) as OC2.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 128) _ _ HP2 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OB1) as OB2.
  pose proof (big_kept_nil _ _ _ _ (S + 160) _ HP2 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) BA1) as BA2.
  pose proof (L5C.model_but_vm_trans _ _ _ MBV1' MBV2) as MBV2'.
  clear TI1 ST1 CS1 STR1 OD1 OC1 OB1 BA1 HP2 MBV1' MBV2 RP2 HH1 Mh1 Ml1 Mm1 R1 M1 model1.
  (* [comment removed for export] *)
  eapply (dtor_call fx2 0x20690 96 0x206b0 S R2 M2 model2 K _ crk bc); try eassumption; try lia.
  { apply TS.d_c; rewrite ?wz_unsigned by lia; lia. }
  { apply (cs_eqv R S R2 CS2). }
  { exact (proj1 OC2). }
  { intros cap q E. destruct OC2 as [_ OCB]. rewrite E in OCB. subst oc. apply in_app_iff. left. left. reflexivity. }
  { apply DEFS. exact TI2. }
  intros fx3 R3 M3 model3 LB3 RP3 ELB3 HP3 MBV3 HH3.
  pose proof (L5C.halted_but_vm _ _ MBV3) as Mh3. rewrite Mh2 in Mh3.
  pose proof (L5C.lazy_but_vm _ _ MBV3) as Ml3. rewrite Ml2 in Ml3.
  pose proof (L5C.materialized_but_vm _ _ MBV3) as Mm3. rewrite Mm2 in Mm3.
  assert (ELB3' : LB3 = ostr ob ++ ostr sk ++ LB).
  { destruct OC2 as [_ OCB]. destruct (L5.bo_st bc) as [v0 v1|cap q]; subst oc; rewrite ELB3; [reflexivity|].
    apply (lb_remove_mid [] q (8 * cap)). exact (proj1 (proj2 (hio_wf L SCFG HI HIok _ _ _ _ HH2))). }
  clear ELB3. subst LB3.
  assert (TI3 : TI LB S M0 m1 M3).
  { eapply (TI_step LB _ S OPDEL_SCR []); [exact TI2| exact HP3| apply cgrows_nil; exact HP3| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (ST3 : L5PS.e1_statics M3 gd fl av uid rnd canary hw).
  { eapply (stat_step _ S OPDEL_SCR []); [exact ST2| exact AVS| exact HP3| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor]. }
  pose proof (cs_ok_canon_call R S R2 R3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP3) as CS3.
  pose proof (str_at_kept_nil _ _ _ _ sk HP3 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) STR2) as STR3.
  pose proof (obj_at_kept_nil _ _ _ _ (S + 128) _ _ HP3 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) OB2) as OB3.
  pose proof (big_kept_nil _ _ _ _ (S + 160) _ HP3 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) BA2) as BA3.
  pose proof (L5C.model_but_vm_trans _ _ _ MBV2' MBV3) as MBV3'.
  clear TI2 ST2 CS2 STR2 OC2 OB2 BA2 HP3 MBV2' MBV3 RP3 HH2 Mh2 Ml2 Mm2 R2 M2 model2.
  (* [comment removed for export] *)
  eapply (dtor_call fx3 0x206b0 128 0x206d0 S R3 M3 model3 K _ crk bb); try eassumption; try lia.
  { apply TS.d_b; rewrite ?wz_unsigned by lia; lia. }
  { apply (cs_eqv R S R3 CS3). }
  { exact (proj1 OB3). }
  { intros cap q E. destruct OB3 as [_ OBB]. rewrite E in OBB. subst ob. apply in_app_iff. left. left. reflexivity. }
  { apply DEFS. exact TI3. }
  intros fx4 R4 M4 model4 LB4 RP4 ELB4 HP4 MBV4 HH4.
  pose proof (L5C.halted_but_vm _ _ MBV4) as Mh4. rewrite Mh3 in Mh4.
  pose proof (L5C.lazy_but_vm _ _ MBV4) as Ml4. rewrite Ml3 in Ml4.
  pose proof (L5C.materialized_but_vm _ _ MBV4) as Mm4. rewrite Mm3 in Mm4.
  assert (ELB4' : LB4 = ostr sk ++ LB).
  { destruct OB3 as [_ OBB]. destruct (L5.bo_st bb) as [v0 v1|cap q]; subst ob; rewrite ELB4; [reflexivity|].
    apply (lb_remove_mid [] q (8 * cap)). exact (proj1 (proj2 (hio_wf L SCFG HI HIok _ _ _ _ HH3))). }
  clear ELB4. subst LB4.
  assert (TI4 : TI LB S M0 m1 M4).
  { eapply (TI_step LB _ S OPDEL_SCR []); [exact TI3| exact HP4| apply cgrows_nil; exact HP4| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (ST4 : L5PS.e1_statics M4 gd fl av uid rnd canary hw).
  { eapply (stat_step _ S OPDEL_SCR []); [exact ST3| exact AVS| exact HP4| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor]. }
  pose proof (cs_ok_canon_call R S R3 R4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP4) as CS4.
  pose proof (str_at_kept_nil _ _ _ _ sk HP4 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) STR3) as STR4.
  pose proof (big_kept_nil _ _ _ _ (S + 160) _ HP4 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(lia) ltac:(lia) BA3) as BA4.
  pose proof (L5C.model_but_vm_trans _ _ _ MBV3' MBV4) as MBV4'.
  clear TI3 ST3 CS3 STR3 OB3 BA3 HP4 MBV3' MBV4 RP4 HH3 Mh3 Ml3 Mm3 R3 M3 model3.
  (* [comment removed for export] *)
  eapply (dtor_call fx4 0x206d0 160 0x206f0 S R4 M4 model4 K _ crk ba); try eassumption; try lia.
  { apply TS.d_a; rewrite ?wz_unsigned by lia; lia. }
  { apply (cs_eqv R S R4 CS4). }
  { intros cap q E. exfalso. destruct ba as [fb ln st]; cbn in E; subst st. unfold L5.bo_dyn in BAI. cbn in BAI.
    destruct BA4 as (_ & _ & _ & TB1 & _). cbn in TB1. rewrite TB1 in BAI. discriminate. }
  { apply DEFS. exact TI4. }
  intros fx5 R5 M5 model5 LB5 RP5 ELB5 HP5 MBV5 HH5.
  pose proof (L5C.halted_but_vm _ _ MBV5) as Mh5. rewrite Mh4 in Mh5.
  pose proof (L5C.lazy_but_vm _ _ MBV5) as Ml5. rewrite Ml4 in Ml5.
  pose proof (L5C.materialized_but_vm _ _ MBV5) as Mm5. rewrite Mm4 in Mm5.
  assert (ELB5' : LB5 = ostr sk ++ LB).
  { destruct (L5.bo_st ba) as [v0 v1|cap q] eqn:E; [exact ELB5|]. exfalso. destruct ba as [fb ln st]; cbn in E; subst st.
    unfold L5.bo_dyn in BAI. cbn in BAI. destruct BA4 as (_ & _ & _ & TB1 & _). cbn in TB1. rewrite TB1 in BAI. discriminate. }
  clear ELB5. subst LB5.
  assert (TI5 : TI LB S M0 m1 M5).
  { eapply (TI_step LB _ S OPDEL_SCR []); [exact TI4| exact HP5| apply cgrows_nil; exact HP5| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (ST5 : L5PS.e1_statics M5 gd fl av uid rnd canary hw).
  { eapply (stat_step _ S OPDEL_SCR []); [exact ST4| exact AVS| exact HP5| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor]. }
  pose proof (cs_ok_canon_call R S R4 R5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP5) as CS5.
  pose proof (str_at_kept_nil _ _ _ _ sk HP5 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) STR4) as STR5.
  (* [comment removed for export] *)
  eapply (ph_strdtor fx5 R5 M5 model5 crk gd fl sk); [exact TI5| exact ST5| | eapply L5C.model_but_vm_trans; [exact MBV4'| exact MBV5]
    | exact Mh5| exact Ml5| exact Mm5| exact CK| exact CB| exact STR5| exact CS5].
  destruct sk as [[p cap]|]; exact HH5.
Qed.
(* [comment removed for export] *)
Definition objL (Mk : word -> option byte) (o : Z) (b : L5.bigobj) (ws : list Z) (blk : option (Z * Z)) : Prop :=
  L5.big_at rsegs Mk o b /\ L5C.obj_limbs rsegs Mk b ws /\
  match L5.bo_st b with
  | L5.BInl _ _ => blk = None
  | L5.BDyn cap q => blk = Some (q, 8 * cap) /\ L5.defined Mk q (8 * cap)
  end.

Lemma objL_obj_at : forall Mk o b ws blk, objL Mk o b ws blk -> obj_at Mk o b blk.
Proof. intros Mk o b ws blk (A & B & C). split; [exact A|]. destruct (L5.bo_st b); [exact C| exact (proj1 C)]. Qed.

(* [comment removed for export] *)
Lemma u8_at_defined : forall Mk a, Mk (Z_to_bv 64 a) <> None -> 0 <= a -> a + 1 <= 2 ^ 64 -> (a + 1 <= 0x10000 \/ 0x91000 <= a) ->
  exists v, L5.u8_at rsegs Mk a v /\ 0 <= v < 256.
Proof.
  intros Mk a D Ha H1 OUT. destruct (Mk (Z_to_bv 64 a)) as [b|] eqn:E; [| congruence].
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. split; [| lia].
  unfold L5.u8_at. rewrite rdn_unfold. change (mrd rsegs Mk (Z_to_bv 64 a)) with (mrd rsegs Mk (wa a)).
  rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). unfold wa. rewrite E. cbn. f_equal. f_equal. symmetry. apply (definitions.Z_to_bv_bv_unsigned 8 b).
Qed.

(* [comment removed for export] *)
Lemma ph_copy_d : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk oy oc ob : option (Z * Z)) (byo bc bb ba : L5.bigobj) (wy : list Z),
  let LBk := ostr oy ++ ostr oc ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 8) <= fst crk -> snd cr - (TOPB len - 8 * L5.bo_cap byo - 2 ^ 23) <= snd crk -> 0 <= fst crk -> 0 <= snd crk ->
  str_at Mk sk ->
  objL Mk S byo wy oy -> L5.bo_cap byo <= 268 -> obj_at Mk (S + 96) bc oc -> obj_at Mk (S + 128) bb ob ->
  L5.big_at rsegs Mk (S + 160) ba -> L5.bo_dyn ba = false ->
  cs_ok R S Rk -> getr Rk 10%bv = wz S ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x20644) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until wy. intros LBk TIk ST HH MBV Mh Ml Mm CK CB CK0 CB0 STR OY CAPYO OC OB BA BAI CS RA0.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct OY as (YB & YL & YBLK).
  (* [comment removed for export] *)
  destruct (u8_at_defined Mk (S + 32) (T4 (S + 32) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). rewrite RA0. apply (TS.s10 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  (* [comment removed for export] *)
  eapply (COPYC fx R1 Mk modelk K LBk crk (S + 32) S S 0x20650 fbo byo wy).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. reflexivity.
  - intros DYN. split; [lia|]. split; [rewrite K8; unfold TOPK in CK, CRK; lia|]. unfold TOPB in CB, CRB. lia.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - exact YB.
  - exact YL.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - intros cap q E. rewrite E in YBLK. destruct YBLK as [-> _]. subst LBk. left. reflexivity.
  - lia.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 g LB2 cr2 [RP12 POST] MBV2 HH2. unfold L5CS.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    assert (SKP : match sk with None => True | Some (p, cap) => 0 < cap end).
    { destruct sk as [[p cap]|]; [| exact I]. destruct STR as (w0 & _ & _ & _ & _ & C0 & _). exact C0. }
    assert (D2 : L5.defined Mk (S - COPY_SCR) COPY_SCR) by (intros i Hi; apply T2; unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *; lia).
    assert (CAPY : 1 <= L5.bo_cap byo).
    { destruct byo as [fb ln [v0 v1|cap q]]; cbn; [lia|]. destruct YB as (_ & _ & _ & _ & _ & _ & _ & CAP & _). cbn in CAP. lia. }
    assert (GO : forall od bd, LB2 = ostr od ++ LBk ->
              L5C.hpres L LBk S COPY_SCR [(S + 32, 32)] Mk M2 -> cgrows LBk S COPY_SCR Mk M2 ->
              obj_at M2 (S + 32) bd od -> fst cr - TOPK <= fst cr2 -> snd cr - TOPB len <= snd cr2 ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x20650) M2 (seg_rom rsegs)) model2) K).
    { intros od bd ELB HP2 CG2 OD CK2 CB2.
      pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia) ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
      assert (APy : apart S 32 [(S + 32, 32)]) by (constructor; [cbn; lia| constructor]).
      assert (APc : apart (S + 96) 32 [(S + 32, 32)]) by (constructor; [cbn; lia| constructor]).
      assert (APb : apart (S + 128) 32 [(S + 32, 32)]) by (constructor; [cbn; lia| constructor]).
      assert (APa : apart (S + 160) 32 [(S + 32, 32)]) by (constructor; [cbn; lia| constructor]).
      assert (APs : apart (S + 192) 24 [(S + 32, 32)]) by (constructor; [cbn; lia| constructor]).
      subst LB2.
      eapply (ph_dtors fx1 R2 M2 model2 cr2 gd fl sk oy od oc ob byo bd bc bb ba).
      - eapply (TI_step LB LBk S COPY_SCR [(S + 32, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
        + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
        + constructor; [left; cbn; lia| constructor].
      - eapply (stat_step LBk S COPY_SCR [(S + 32, 32)]); [exact ST| exact AVS| exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia|].
        constructor; [left; cbn; lia| constructor].
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - exact CK2.
      - exact CB2.
      - eapply str_at_kept; [exact AG2| exact APs| exact STR].
      - exact SKP.
      - eapply obj_at_kept; [exact AG2| lia| lia| exact APy|]. split; [exact YB|]. destruct (L5.bo_st byo); [exact YBLK| exact (proj1 YBLK)].
      - exact OD.
      - eapply obj_at_kept; [exact AG2| lia| lia| exact APc| exact OC].
      - eapply obj_at_kept; [exact AG2| lia| lia| exact APb| exact OB].
      - eapply big_kept; [exact AG2| lia| lia| exact APa| exact BA].
      - exact BAI.
      - exact CS2. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct POST as (DYF & ELB & ECR & BD & FB & MG).
      destruct (hpres_frame LBk COPY_SCR [(S + 32, 32)] Mk M2 FB MG D2) as [HP2 CG2].
      apply (GO None (L5.BO (copy_fb fbo (L5.bo_fb byo) false) (L5.bo_len byo) (L5.bo_st byo)));
        [exact ELB| exact HP2| exact CG2| | subst cr2; lia| subst cr2; lia].
      split; [exact BD|]. cbn [L5.bo_st]. destruct byo as [fb ln [v0 v1|cap q]]; cbn; [reflexivity|].
      exfalso. unfold L5.bo_dyn in DYF. cbn in DYF. destruct YB as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYF. discriminate.
    + (* [comment removed for export] *)
      destruct POST as (DYT & ECAP & ELB & ECR & FRESH & BD & BL & HP2).
      apply (GO (Some (A, 8 * cap)) (L5.BO (copy_fb fbo (L5.bo_fb byo) true) (L5.bo_len byo) (L5.BDyn cap A)));
        [exact ELB| exact HP2| apply HPG in HP2; exact HP2| split; [exact BD| reflexivity]
        | subst cr2; unfold debit; cbn [fst snd]; rewrite K8; lia| subst cr2 cap; unfold debit; cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
Lemma ph_opmod2 : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk oy oc ob : option (Z * Z)) (byo bc bb : L5.bigobj) (wy : list Z) (fba : Z),
  let LBk := ostr oy ++ ostr oc ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 104) <= fst crk -> snd cr - (TOPB len - (9600 + 13 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  objL Mk S byo wy oy -> L5DS.reduced wy -> L5.bo_cap byo <= 268 ->
  (1 <= L5.bo_len byo)%nat ->      (* [comment removed for export] *)
  (forall cap q, L5.bo_st byo = L5.BDyn cap q -> Z.of_nat (L5.bo_len byo) + 1 <= cap) ->
  obj_at Mk (S + 96) bc oc -> obj_at Mk (S + 128) bb ob ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x20638) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR OY RED CAPY YLEN1 YCAP OC OB AOK CS.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct OY as (YB & YL & YBLK).
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  assert (CAPY1 : 1 <= L5.bo_cap byo).
  { destruct byo as [fb ln [v0 v1|cap q]]; cbn; [lia|]. destruct YB as (_ & _ & _ & _ & _ & _ & _ & CAP & _). cbn in CAP. lia. }
  (* [comment removed for export] *)
  assert (YBR : forall cap q, L5.bo_st byo = L5.BDyn cap q ->
            oy = Some (q, 8 * cap) /\ L5.defined Mk q (8 * cap) /\ (4096 <= q /\ (q + 8 * cap <= hl_img_lo L \/ hl_img_hi L <= q)) /\ q + 8 * cap <= hl_ceil L /\ blocks_apart q (8 * cap) LB).
  { intros cap q E. rewrite E in YBLK. destruct YBLK as [EO DEF]. subst oy.
    destruct (WFB (q, 8 * cap) ltac:(subst LBk; left; reflexivity)) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & BA). cbn [fst snd] in B1lo. cbn [fst snd] in B1, B2, B3, B4, BA.
    repeat split; try assumption; try reflexivity.
    eapply blocks_apart_sub; [exact BA|]. intros b Hb. subst LBk. cbn [ostr app lb_remove fst]. rewrite Z.eqb_refl. rewrite !in_app_iff. tauto. }
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). apply (TS.s9 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (OPMOD2 fx R1 Mk modelk K LBk crk S (S + 160) fba byo wy).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. reflexivity.
  - greg REQ1 11. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - reflexivity.
  - greg REQ1 1. reflexivity.
  - greg REQ1 2. reflexivity.
  - greg REQ1 3. exact Rgp.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold L5DS.SCR_OPMOD; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold L5DS.SCR_OPMOD in Hi |- *. lia.
  - exact SHI.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - intros cap q E. destruct (YBR cap q E) as (_ & DEF & Q1 & Q2 & _). apply (L5C.writable_of_defined rsegs); [exact DEF| lia| lia].
  - eapply e1_img. exact ST.
  - split; [exact YB|]. split; [exact YL|]. split; [exact RED|].
    destruct (L5.bo_st byo) as [v0 v1|cap q] eqn:E; [exact I|].
    destruct (YBR cap q eq_refl) as (EO & DEF & _). split; [subst oy LBk; left; reflexivity|]. split; [exact DEF| exact (YCAP cap q eq_refl)].
  - exact YLEN1.
  - exact CAPY.
  - exact AOK.
  - unfold L5DS.credit_for, L5DS.OPMOD2_K, L5DS.opmod2_bytes. rewrite K8. split; [unfold TOPK in CK, CRK; lia| unfold TOPB in CB, CRB; lia].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 POST MBV2 HH2. unfold L5DS.cfg.
    destruct POST as (RP12 & A02 & YA & AOK2 & CRA & HP2).
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    unfold L5DS.credit_after, L5DS.OPMOD2_K, L5DS.opmod2_bytes in CRA. rewrite K8 in CRA. destruct CRA as [CRA1 CRA2].
    set (W := [(S, 32); (L5.bo_data S byo, 8 * L5.bo_cap byo)]) in HP2.
    assert (WOK : Forall (wok LB S) W).
    { subst W. constructor; [left; cbn; lia|]. constructor; [| constructor].
      unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st byo) as [v0 v1|cap q] eqn:E; [left; cbn; lia|].
      destruct (YBR cap q eq_refl) as (_ & _ & Q1 & Q2 & BA). right. left. cbn [fst snd]. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY). repeat split; [lia| lia| lia| exact BA]. }
    assert (WST : Forall (fun r => (S <= fst r /\ fst r + snd r <= S + 240) \/ ((4096 <= fst r /\ (fst r + snd r <= hl_img_lo L \/ hl_img_hi L <= fst r)) /\ fst r + snd r <= hl_ceil L)) W).
    { subst W. constructor; [left; cbn; lia|]. constructor; [| constructor].
      unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st byo) as [v0 v1|cap q] eqn:E; [left; cbn; lia|].
      destruct (YBR cap q eq_refl) as (_ & _ & Q1 & Q2 & BA). right. cbn [fst snd]. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY). lia. }
    assert (APW : forall o n, S + 32 <= o -> o + n <= S + 240 -> apart o n W).
    { intros o n Ho Hn. subst W. constructor; [cbn; lia|]. constructor; [| constructor].
      unfold L5.bo_data, L5.bo_cap. destruct (L5.bo_st byo) as [v0 v1|cap q] eqn:E; [cbn; lia|].
      destruct (YBR cap q eq_refl) as (_ & _ & Q1 & Q2 & _). cbn. lia. }
    pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
    pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold L5DS.SCR_OPMOD; lia) ltac:(unfold L5DS.SCR_OPMOD; lia)) as AG2.
    pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (_ & _ & CK2 & CB2).
    destruct YA as (by' & wy' & YB2 & YL2 & REL).
    assert (GO : forall oy', LB2 = ostr oy' ++ ostr oc ++ ostr ob ++ ostr sk ++ LB ->
              match L5.bo_st by' with L5.BInl _ _ => oy' = None | L5.BDyn cap q => oy' = Some (q, 8 * cap) /\ L5.defined M2 q (8 * cap) end ->
              L5.bo_cap by' <= 268 ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x20644) M2 (seg_rom rsegs)) model2) K).
    { intros oy' ELB OBLK CAP2. subst LB2.
      eapply (ph_copy_d fx1 R2 M2 model2 cr2 gd fl sk oy' oc ob by' bc bb (L5.BO fba 2 (L5.BInl L5DS.A0 L5DS.A1)) wy').
      - eapply (TI_step LB LBk S L5DS.SCR_OPMOD W); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold L5DS.SCR_OPMOD; lia| lia| lia| exact WOK].
        intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
      - eapply (stat_step LBk S L5DS.SCR_OPMOD W); [exact ST| exact AVS| exact HP2| unfold L5DS.SCR_OPMOD; lia| unfold L5DS.SCR_OPMOD; lia| lia| exact WST].
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - unfold TOPK in CK, CRK |- *. lia.
      - unfold TOPB in CB, CRB |- *. lia.
      - exact CK2.
      - exact CB2.
      - eapply str_at_kept; [exact AG2| apply APW; lia| exact STR].
      - split; [exact YB2|]. split; [exact YL2|]. exact OBLK.
      - exact CAP2.
      - eapply obj_at_kept; [exact AG2| lia| lia| apply APW; lia| exact OC].
      - eapply obj_at_kept; [exact AG2| lia| lia| apply APW; lia| exact OB].
      - exact (proj1 AOK2).
      - unfold L5.bo_dyn. cbn [L5.bo_fb]. destruct AOK2 as [(_ & _ & _ & TB & _) _]. exact TB.
      - exact CS2.
      - exact A02. }
    destruct (L5.bo_st byo) as [v0 v1|cap q] eqn:EY; destruct (L5.bo_st by') as [v0' v1'|cap' q'] eqn:EY'.
    + (* [comment removed for export] *) subst oy. apply (GO None); [exact REL| rewrite ?EY'; reflexivity| unfold L5.bo_cap; rewrite ?EY'; lia].
    + (* [comment removed for export] *) subst oy. destruct REL as (EC & ELB & FR). subst cap'.
      apply (GO (Some (q', 64))); [exact ELB| rewrite ?EY'; split; [reflexivity| exact (proj2 (proj2 FR))]| unfold L5.bo_cap; rewrite ?EY'; lia].
    + (* [comment removed for export] *) destruct REL.
    + (* [comment removed for export] *) destruct YBLK as [EO _]. subst oy. destruct REL as (EC & EQ & ELB & DEF). subst cap' q'.
      apply (GO (Some (q, 8 * cap))); [exact ELB| rewrite ?EY'; split; [reflexivity| exact DEF]| unfold L5.bo_cap in CAPY |- *; rewrite ?EY in CAPY; rewrite ?EY'; lia].
Qed.

(* [comment removed for export] *)
Lemma ph_copy_y : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk oc ob : option (Z * Z)) (bc bb : L5.bigobj) (wb : list Z) (fba : Z),
  let LBk := ostr oc ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 112) <= fst crk -> snd cr - (TOPB len - (11744 + 14 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  obj_at Mk (S + 96) bc oc ->
  objL Mk (S + 128) bb wb ob -> L5DS.reduced wb -> L5.bo_cap bb <= 268 ->
  (1 <= L5.bo_len bb)%nat ->      (* [comment removed for export] *)
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x2062c) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR OC OB RED CAPB BLEN1 BCAP AOK CS.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct OB as (BB & BL & BBLK).
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  assert (CAPB1 : 1 <= L5.bo_cap bb).
  { destruct bb as [fb ln [v0 v1|cap q]]; cbn; [lia|]. destruct BB as (_ & _ & _ & _ & _ & _ & _ & CAP & _). cbn in CAP. lia. }
  destruct (u8_at_defined Mk S (T4 S ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). apply (TS.s8 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  (* [comment removed for export] *)
  eapply (COPYC fx R1 Mk modelk K LBk crk S (S + 128) S 0x20638 fbo bb wb).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. reflexivity.
  - greg REQ1 11. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - intros DYN. split; [lia|]. split; [rewrite K8; unfold TOPK in CK, CRK; lia|]. unfold TOPB in CB, CRB. lia.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - exact BB.
  - exact BL.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - intros cap q E. rewrite E in BBLK. destruct BBLK as [-> _]. subst LBk. rewrite !in_app_iff. cbn. tauto.
  - lia.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 g LB2 cr2 [RP12 POST] MBV2 HH2. unfold L5CS.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    assert (D2 : L5.defined Mk (S - COPY_SCR) COPY_SCR) by (intros i Hi; apply T2; unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *; lia).
    assert (GO : forall oy byo, LB2 = ostr oy ++ LBk ->
              L5C.hpres L LBk S COPY_SCR [(S, 32)] Mk M2 -> cgrows LBk S COPY_SCR Mk M2 ->
              objL M2 S byo wb oy -> L5.bo_cap byo <= 268 -> (1 <= L5.bo_len byo)%nat ->
              (forall cap q, L5.bo_st byo = L5.BDyn cap q -> Z.of_nat (L5.bo_len byo) + 1 <= cap) ->
              fst cr - (TOPK - 104) <= fst cr2 -> snd cr - (TOPB len - (9600 + 13 * 2 ^ 23)) <= snd cr2 ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x20638) M2 (seg_rom rsegs)) model2) K).
    { intros oy byo ELB HP2 CG2 OY CAP2 YLEN1 YCAP CK2 CB2.
      pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia) ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
      assert (APW : forall o n, S + 32 <= o -> o + n <= S + 240 -> apart o n [(S, 32)]) by (intros o n Ho Hn; constructor; [cbn; lia| constructor]).
      subst LB2.
      eapply (ph_opmod2 fx1 R2 M2 model2 cr2 gd fl sk oy oc ob byo bc bb wb fba).
      - eapply (TI_step LB LBk S COPY_SCR [(S, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
        + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
        + constructor; [left; cbn; lia| constructor].
      - eapply (stat_step LBk S COPY_SCR [(S, 32)]); [exact ST| exact AVS| exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia|].
        constructor; [left; cbn; lia| constructor].
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - exact CK2.
      - exact CB2.
      - eapply str_at_kept; [exact AG2| apply APW; lia| exact STR].
      - exact OY.
      - exact RED.
      - exact CAP2.
      - exact YLEN1.
      - exact YCAP.
      - eapply obj_at_kept; [exact AG2| lia| lia| apply APW; lia| exact OC].
      - eapply obj_at_kept; [exact AG2| lia| lia| apply APW; lia|]. split; [exact BB|]. destruct (L5.bo_st bb); [exact BBLK| exact (proj1 BBLK)].
      - destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG2| lia| lia| apply APW; lia| exact BA].
      - exact CS2. }
    destruct g as [|A cap].
    + (* [comment removed for export] *)
      destruct POST as (DYF & ELB & ECR & BD & FB & MG).
      destruct (hpres_frame LBk COPY_SCR [(S, 32)] Mk M2 FB MG D2) as [HP2 CG2].
      destruct bb as [fb ln [v0 v1|capb qb]].
      * apply (GO None (L5.BO (copy_fb fbo fb false) ln (L5.BInl v0 v1))); [exact ELB| exact HP2| exact CG2| | cbn; lia| exact BLEN1| intros cap q E; discriminate E| subst cr2; lia| subst cr2; lia].
        split; [exact BD|]. split; [| reflexivity]. destruct BL as (L1 & L2 & L3). exact (conj L1 (conj L2 L3)).
      * exfalso. unfold L5.bo_dyn in DYF. cbn in DYF. destruct BB as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYF. discriminate.
    + (* [comment removed for export] *)
      destruct POST as (DYT & ECAP & ELB & ECR & FRESH & BD & BL2 & HP2).
      pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
      destruct bb as [fb ln [v0 v1|capb qb]].
      * exfalso. unfold L5.bo_dyn in DYT. cbn in DYT. destruct BB as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYT. discriminate.
      * cbn [L5.bo_cap L5.bo_fb L5.bo_len L5.bo_st] in ECAP, CAPB, BCAP, BD, BL2. subst cap.
        apply (GO (Some (A, 8 * capb)) (L5.BO (copy_fb fbo fb true) ln (L5.BDyn capb A))); [exact ELB| exact HP2| exact CG2| | cbn; lia| exact BLEN1| | |].
        -- split; [exact BD|]. split; [exact BL2|]. cbn. split; [reflexivity| exact (proj2 (proj2 FRESH))].
        -- intros cap q E. cbn in E |- *. injection E. intros _ <-. exact (BCAP capb qb eq_refl).
        -- subst cr2. unfold debit. cbn [fst snd]. rewrite K8. unfold TOPK in CK, CRK |- *. lia.
        -- subst cr2. unfold debit. cbn [fst snd]. unfold TOPB in CB, CRB |- *. lia.
Qed.

(* [comment removed for export] *)
Lemma ph_xdtor : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk ox oc ob : option (Z * Z)) (bx bc bb : L5.bigobj) (wb : list Z) (fba : Z),
  let LBk := ostr oc ++ ostr ox ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 112) <= fst crk -> snd cr - (TOPB len - (11744 + 14 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  obj_at Mk (S + 64) bx ox -> obj_at Mk (S + 96) bc oc ->
  objL Mk (S + 128) bb wb ob -> L5DS.reduced wb -> L5.bo_cap bb <= 268 ->
  (1 <= L5.bo_len bb)%nat ->      (* [comment removed for export] *)
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x2060c) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR OX OC OB RED CAPB BLEN1 BCAP AOK CS.
  pose proof TIk as (T1 & T2 & T3 & T4).
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  assert (RA1 : L5.ra_ok 0x2062c) by (split; [lia| reflexivity]).
  eapply (dtor_call fx 0x2060c 64 0x2062c S Rk Mk modelk K LBk crk bx); try eassumption; try lia.
  { apply TS.d_x; rewrite ?wz_unsigned by lia; lia. }
  { apply (cs_eqv R S Rk CS). }
  { exact (proj1 OX). }
  { intros cap q E. destruct OX as [_ OXB]. rewrite E in OXB. subst ox LBk. rewrite !in_app_iff. cbn. tauto. }
  { intros i Hi. apply T2. unfold OPDEL_SCR, HEAP_STACK in Hi |- *. lia. }
  intros fx1 R1 M1 model1 LB1 RP1 ELB1 HP1 MBV1 HH1.
  pose proof (L5C.halted_but_vm _ _ MBV1) as Mh1. rewrite Mh in Mh1.
  pose proof (L5C.lazy_but_vm _ _ MBV1) as Ml1. rewrite Ml in Ml1.
  pose proof (L5C.materialized_but_vm _ _ MBV1) as Mm1. rewrite Mm in Mm1.
  assert (ELB1' : LB1 = ostr oc ++ ostr ob ++ ostr sk ++ LB).
  { destruct OX as [_ OXB]. destruct (L5.bo_st bx) as [v0 v1|cap q]; subst ox; rewrite ELB1; [reflexivity|]. subst LBk.
    apply (lb_remove_mid (ostr oc) q (8 * cap)). exact WFND. }
  clear ELB1. 
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (WFB1 & WFND1 & _ & _).
  pose proof (ags_hpres _ _ _ _ _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia)) as AG1.
  assert (APN : forall o n, apart o n []) by (intros; constructor).
  subst LB1.
  eapply (ph_copy_y fx1 R1 M1 model1 crk gd fl sk oc ob bc bb wb fba).
  - eapply (TI_step LB _ S OPDEL_SCR []); [exact TIk| exact HP1| apply cgrows_nil; exact HP1| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto.
  - eapply (stat_step _ S OPDEL_SCR []); [exact ST| exact AVS| exact HP1| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor].
  - exact HH1.
  - eapply L5C.model_but_vm_trans; [exact MBV| exact MBV1].
  - exact Mh1.
  - exact Ml1.
  - exact Mm1.
  - exact CK.
  - exact CB.
  - eapply str_at_kept; [exact AG1| apply APN| exact STR].
  - eapply obj_at_kept; [exact AG1| lia| lia| apply APN| exact OC].
  - destruct OB as (BB & BL & BBLK). split; [| split].
    + eapply big_kept; [exact AG1| lia| lia| apply APN| exact BB].
    + eapply (limbs_kept _ OPDEL_SCR [] Mk M1 bb wb HP1); [| exact BL].
      intros cap q E. rewrite E in BBLK. destruct BBLK as [EO _]. subst ob.
      assert (IN1 : In (q, 8 * cap) (ostr oc ++ ostr (Some (q, 8 * cap)) ++ ostr sk ++ LB)) by (rewrite !in_app_iff; cbn; tauto).
      destruct (WFB1 (q, 8 * cap) IN1) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo. cbn [fst snd] in B1, B2, B3, B4.
      destruct bb as [fb ln st]; cbn in E; subst st. destruct BB as (_ & _ & _ & _ & _ & _ & LC & _). cbn in LC.
      repeat split; [exact IN1| lia| lia| lia| exact LC| apply APN].
    + destruct (L5.bo_st bb) as [v0 v1|cap q] eqn:E; [exact BBLK|]. destruct BBLK as [EO _]. split; [exact EO|]. subst ob.
      assert (IN1 : In (q, 8 * cap) (ostr oc ++ ostr (Some (q, 8 * cap)) ++ ostr sk ++ LB)) by (rewrite !in_app_iff; cbn; tauto).
      exact (proj1 (proj2 (WFB1 (q, 8 * cap) IN1))).
  - exact RED.
  - exact CAPB.
  - exact BLEN1.
  - exact BCAP.
  - destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG1| lia| lia| apply APN| exact BA].
  - eapply (cs_ok_canon_call R S Rk R1). exact RP1.
Qed.

(* [comment removed for export] *)
Lemma objL_kept : forall LBk scr W Mk Mk1 LB1 (VMk VM1 : VmMaps) crk1 crk0 o b ws blk,
  L5C.hpres L LBk S scr W Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S -> S <= o -> o + 32 <= S + 240 -> apart o 32 W ->
  hi_heap HI LBk crk0 Mk VMk -> hi_heap HI LB1 crk1 Mk1 VM1 ->
  (forall q n, blk = Some (q, n) -> In (q, n) LBk /\ In (q, n) LB1 /\ apart q n W) ->
  objL Mk o b ws blk -> objL Mk1 o b ws blk.
Proof using HIok LY S16 SHI SLO SPW STOP len.
  intros until blk. intros HP Hscr Hlo Ho Hn AP HH HH1 BLK (B & LM & BK).
  pose proof (ags_hpres _ _ _ _ _ HP Hscr Hlo) as AG.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & _). pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (WFB1 & _).
  split; [eapply big_kept; [exact AG| lia| lia| exact AP| exact B]|].
  destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E.
  - split; [| exact BK]. destruct LM as (L1 & L2 & L3). rewrite E in L3. split; [exact L1|]. split; [exact L2|]. rewrite E. exact L3.
  - destruct BK as [EO DEF]. destruct (BLK q (8 * cap) EO) as (IN & IN1 & APq).
    destruct (WFB (q, 8 * cap) IN) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo. cbn [fst snd] in B1, B2, B3, B4.
    split; [| split; [exact EO| exact (proj1 (proj2 (WFB1 (q, 8 * cap) IN1)))]].
    eapply (limbs_kept LBk scr W Mk Mk1 b ws HP); [| exact LM].
    intros cap' q' E'. rewrite E in E'. injection E'. intros <- <-.
    destruct b as [fb ln st]; cbn in E; subst st. destruct B as (_ & _ & _ & _ & _ & _ & LC & _). cbn in LC |- *.
    repeat split; [exact IN| lia| lia| lia| exact LC| exact APq].
Qed.

(* [comment removed for export] *)
Lemma ph_copy_c : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk ox ob : option (Z * Z)) (bx bb : L5.bigobj) (wx wb : list Z) (fba : Z),
  let LBk := ostr ox ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 120) <= fst crk -> snd cr - (TOPB len - (13888 + 15 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  objL Mk (S + 64) bx wx ox -> L5.bo_cap bx <= 8 ->
  objL Mk (S + 128) bb wb ob -> L5DS.reduced wb -> L5.bo_cap bb <= 268 ->
  (1 <= L5.bo_len bb)%nat ->      (* [comment removed for export] *)
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk -> getr Rk 10%bv = wz (S + 64) ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x20600) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR OX CAPX OB RED CAPB BLEN1 BCAP AOK CS RA0.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct OX as (XB & XL & XBLK).
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  assert (CAPX1 : 1 <= L5.bo_cap bx).
  { destruct bx as [fb ln [v0 v1|cap q]]; cbn; [lia|]. destruct XB as (_ & _ & _ & _ & _ & _ & _ & CAP & _). cbn in CAP. lia. }
  destruct (u8_at_defined Mk (S + 96) (T4 (S + 96) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). rewrite RA0. apply (TS.s6 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (COPYC fx R1 Mk modelk K LBk crk (S + 96) (S + 64) S 0x2060c fbo bx wx).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. reflexivity.
  - intros DYN. split; [lia|]. split; [rewrite K8; unfold TOPK in CK, CRK; lia|]. unfold TOPB in CB, CRB. lia.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - exact XB.
  - exact XL.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - intros cap q E. rewrite E in XBLK. destruct XBLK as [-> _]. subst LBk. left. reflexivity.
  - lia.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 g LB2 cr2 [RP12 POST] MBV2 HH2. unfold L5CS.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    assert (D2 : L5.defined Mk (S - COPY_SCR) COPY_SCR) by (intros i Hi; apply T2; unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *; lia).
    assert (GO : forall oc bc, LB2 = ostr oc ++ LBk ->
              L5C.hpres L LBk S COPY_SCR [(S + 96, 32)] Mk M2 -> cgrows LBk S COPY_SCR Mk M2 ->
              obj_at M2 (S + 96) bc oc ->
              fst cr - (TOPK - 112) <= fst cr2 -> snd cr - (TOPB len - (11744 + 14 * 2 ^ 23)) <= snd cr2 ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x2060c) M2 (seg_rom rsegs)) model2) K).
    { intros oc bc ELB HP2 CG2 OC CK2 CB2.
      pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia) ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
      assert (APW : forall o n, (o + n <= S + 96 \/ S + 128 <= o) -> apart o n [(S + 96, 32)]) by (intros o n Ho; constructor; [cbn; lia| constructor]).
      subst LB2.
      eapply (ph_xdtor fx1 R2 M2 model2 cr2 gd fl sk ox oc ob bx bc bb wb fba).
      - eapply (TI_step LB LBk S COPY_SCR [(S + 96, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
        + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
        + constructor; [left; cbn; lia| constructor].
      - eapply (stat_step LBk S COPY_SCR [(S + 96, 32)]); [exact ST| exact AVS| exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia|].
        constructor; [left; cbn; lia| constructor].
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - exact CK2.
      - exact CB2.
      - eapply str_at_kept; [exact AG2| apply APW; lia| exact STR].
      - eapply obj_at_kept; [exact AG2| lia| lia| apply APW; lia|]. split; [exact XB|]. destruct (L5.bo_st bx); [exact XBLK| exact (proj1 XBLK)].
      - exact OC.
      - eapply (objL_kept LBk COPY_SCR [(S + 96, 32)] Mk M2); [exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia| apply APW; lia| exact HH| exact HH2| | exact OB].
        intros q n EO. destruct OB as (_ & _ & BBLK). destruct (L5.bo_st bb) as [v0 v1|cap' q']; [subst ob; discriminate EO|].
        destruct BBLK as [EO' _]. rewrite EO' in EO. injection EO. intros <- <-. subst ob LBk.
        assert (IN : In (q', 8 * cap') (ostr ox ++ ostr (Some (q', 8 * cap')) ++ ostr sk ++ LB)) by (rewrite !in_app_iff; cbn; tauto).
        split; [exact IN|]. split; [apply in_or_app; right; exact IN|].
        destruct (WFB _ IN) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo. cbn [fst snd] in B4. apply APW. lia.
      - exact RED.
      - exact CAPB.
      - exact BLEN1.
      - exact BCAP.
      - destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG2| lia| lia| apply APW; lia| exact BA].
      - exact CS2. }
    destruct g as [|A cap].
    + destruct POST as (DYF & ELB & ECR & BD & FB & MG).
      destruct (hpres_frame LBk COPY_SCR [(S + 96, 32)] Mk M2 FB MG D2) as [HP2 CG2].
      destruct bx as [fb ln [v0 v1|capx qx]].
      * apply (GO None (L5.BO (copy_fb fbo fb false) ln (L5.BInl v0 v1))); [exact ELB| exact HP2| exact CG2| split; [exact BD| reflexivity]| subst cr2; lia| subst cr2; lia].
      * exfalso. unfold L5.bo_dyn in DYF. cbn in DYF. destruct XB as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYF. discriminate.
    + destruct POST as (DYT & ECAP & ELB & ECR & FRESH & BD & BL2 & HP2).
      pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
      destruct bx as [fb ln [v0 v1|capx qx]].
      * exfalso. unfold L5.bo_dyn in DYT. cbn in DYT. destruct XB as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYT. discriminate.
      * cbn [L5.bo_cap L5.bo_fb L5.bo_len L5.bo_st] in ECAP, CAPX, BD, BL2. subst cap.
        apply (GO (Some (A, 8 * capx)) (L5.BO (copy_fb fbo fb true) ln (L5.BDyn capx A))); [exact ELB| exact HP2| exact CG2| split; [exact BD| reflexivity]| |].
        -- subst cr2. unfold debit. cbn [fst snd]. rewrite K8. unfold TOPK in CK, CRK |- *. lia.
        -- subst cr2. unfold debit. cbn [fst snd]. unfold TOPB in CB, CRB |- *. lia.
Qed.

(* [comment removed for export] *)
Definition E2_obl (sk : option (Z * Z)) (gd fl : bool) : Prop :=
  forall (ob : option (Z * Z)) (bb : L5.bigobj) (wb : list Z) (fba fbx : Z) (Mk' : word -> option byte) (crk' : credit)
         (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
    cs_ok R S R' -> e2_landed (xs_of gd fl av uid rnd canary hw) (ostr ob ++ ostr sk ++ LB) crk' S M' R' LB' cr' ->
    TI LB S M0 m1 Mk' -> L5PS.e1_statics Mk' gd fl av uid rnd canary hw -> str_at Mk' sk -> L5DS.a_ok Mk' (S + 160) fba ->
    objL Mk' (S + 128) bb wb ob -> (exists VM, hi_heap HI (ostr ob ++ ostr sk ++ LB) crk' Mk' VM) ->
    fst cr - (TOPK - 248) <= fst crk' -> snd cr - (TOPB len - (17568 + 31 * 2 ^ 23)) <= snd crk' ->
    L5DS.x_is_a M' (S + 64) fbx -> L5.big_at rsegs M' (S + 128) bb -> L5C.obj_limbs rsegs M' bb wb ->
    L5C.hpres L (ostr ob ++ ostr sk ++ LB) S L5DS.SCR_OPMOD ((S + 64, 32) :: xs_foot) Mk' M' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 L5DS.TOP_PAD) M' (seg_rom rsegs)) model') K.
Definition E3_obl (sk : option (Z * Z)) (gd fl : bool) : Prop :=
  forall (ob : option (Z * Z)) (bb : L5.bigobj) (wb : list Z) (fba : Z) (Mk' : word -> option byte) (crk' : credit)
         (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit)
         (fbx' : Z) (nx : nat) (qx : Z) (cr1 : credit),
    cs_ok R S R' ->
    TI LB S M0 m1 Mk' -> L5PS.e1_statics Mk' gd fl av uid rnd canary hw -> str_at Mk' sk -> L5DS.a_ok Mk' (S + 160) fba ->
    objL Mk' (S + 128) bb wb ob -> (exists VM, hi_heap HI (ostr ob ++ ostr sk ++ LB) crk' Mk' VM) ->
    fst cr - (TOPK - 248) <= fst crk' -> snd cr - (TOPB len - (17568 + 31 * 2 ^ 23)) <= snd crk' -> L5.bo_cap bb <= 268 ->
    L5.big_at rsegs M' (S + 64) (L5.BO fbx' nx (L5.BDyn 8 qx)) -> L5C.fresh_block L (ostr ob ++ ostr sk ++ LB) M' qx 64 ->
    L5DS.credit_after L crk' L5DS.OPMOD1_K (L5DS.opmod1_bytes (L5.bo_cap bb)) cr1 ->
    e3_landed (xs_of gd fl av uid rnd canary hw) ((qx, 64) :: ostr ob ++ ostr sk ++ LB) cr1 S M' R' LB' cr' ->
    L5.big_at rsegs M' (S + 128) bb -> L5C.obj_limbs rsegs M' bb wb ->
    L5C.hpres L (ostr ob ++ ostr sk ++ LB) S L5DS.SCR_OPMOD ((S + 64, 32) :: xs_foot) Mk' M' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 L5DS.TOP_PAD) M' (seg_rom rsegs)) model') K.

(* [comment removed for export] *)
Lemma ph_opmod1 : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk ob : option (Z * Z)) (bb : L5.bigobj) (wb : list Z) (fbx fba : Z),
  let LBk := ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 248) <= fst crk -> snd cr - (TOPB len - (17568 + 31 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  L5DS.x_is_a Mk (S + 64) fbx ->
  objL Mk (S + 128) bb wb ob -> L5DS.reduced wb -> L5.bo_cap bb <= 268 ->
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->      (* [comment removed for export] *)
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk -> E2_obl sk gd fl -> E3_obl sk gd fl ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x205f4) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR XA OB RED CAPB BCAP DYN3 AOK CS PE2 PE3.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct OB as (BB & BL & BBLK).
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  assert (CAPB1 : 1 <= L5.bo_cap bb).
  { destruct bb as [fb ln [v0 v1|cap q]]; cbn; [lia|]. destruct BB as (_ & _ & _ & _ & _ & _ & _ & CAP & _). cbn in CAP. lia. }
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). apply (TS.s5 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (OPMOD1 fx R1 Mk modelk K LBk crk S fbx (S + 128) bb wb (xs_of gd fl av uid rnd canary hw)).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - reflexivity.
  - greg REQ1 1. reflexivity.
  - greg REQ1 2. reflexivity.
  - greg REQ1 3. exact Rgp.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold L5DS.SCR_OPMOD; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold L5DS.SCR_OPMOD in Hi |- *. lia.
  - exact SHI.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - eapply e1_img. exact ST.
  - exact XA.
  - split; [exact BB|]. split; [exact BL|]. split; [exact RED|].
    destruct (L5.bo_st bb) as [v0 v1|cap q] eqn:E; [exact I|]. destruct BBLK as [EO DEF]. split; [subst ob LBk; left; reflexivity| exact DEF].
  - exact CAPB.
  - exact DYN3.
  - unfold L5DS.credit_for, L5DS.OPMOD1_K, L5DS.opmod1_bytes. rewrite K8. split; [unfold TOPK in CK, CRK; lia| unfold TOPB in CB, CRB; lia].
  - eapply XSP; [exact ST| exact AVS].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 POST MBV2 HH2. unfold L5DS.cfg.
    destruct POST as (RP12 & A02 & XA2 & BB2 & BL2 & BLEN1 & CRA & HP2).
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
    pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold L5DS.SCR_OPMOD; lia) ltac:(unfold L5DS.SCR_OPMOD; lia)) as AG2.
    pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (WFB2 & _ & CK2 & CB2).
    unfold L5DS.credit_after, L5DS.OPMOD1_K, L5DS.opmod1_bytes in CRA. rewrite K8 in CRA. destruct CRA as [CRA1 CRA2].
    assert (APW : forall o n, (o + n <= S + 64 \/ S + 96 <= o) -> apart o n [(S + 64, 32)]) by (intros o n Ho; constructor; [cbn; lia| constructor]).
    destruct XA2 as (bx & wx & XB & XL & XNEG & XST).
    assert (GO : forall ox, LB2 = ostr ox ++ LBk ->
              match L5.bo_st bx with L5.BInl _ _ => ox = None | L5.BDyn cap q => ox = Some (q, 8 * cap) /\ L5.defined M2 q (8 * cap) end ->
              L5.bo_cap bx <= 8 ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x20600) M2 (seg_rom rsegs)) model2) K).
    { intros ox ELB OXB CAPX. subst LB2.
      eapply (ph_copy_c fx1 R2 M2 model2 cr2 gd fl sk ox ob bx bb wx wb fba).
      - eapply (TI_step LB LBk S L5DS.SCR_OPMOD [(S + 64, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold L5DS.SCR_OPMOD; lia| lia| lia|].
        + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
        + constructor; [left; cbn; lia| constructor].
      - eapply (stat_step LBk S L5DS.SCR_OPMOD [(S + 64, 32)]); [exact ST| exact AVS| exact HP2| unfold L5DS.SCR_OPMOD; lia| unfold L5DS.SCR_OPMOD; lia| lia|].
        constructor; [left; cbn; lia| constructor].
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - unfold TOPK in CK, CRK |- *. lia.
      - unfold TOPB in CB, CRB |- *. lia.
      - eapply str_at_kept; [exact AG2| apply APW; lia| exact STR].
      - split; [exact XB|]. split; [exact XL|]. exact OXB.
      - exact CAPX.
      - split; [exact BB2|]. split; [exact BL2|].
        destruct (L5.bo_st bb) as [v0 v1|cap q] eqn:E; [exact BBLK|]. destruct BBLK as [EO _]. split; [exact EO|]. subst ob.
        refine (proj1 (proj2 (WFB2 (q, 8 * cap) _))). apply in_or_app. right. subst LBk. left. reflexivity.
      - exact RED.
      - exact CAPB.
      - exact BLEN1.
      - exact BCAP.
      - destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG2| lia| lia| apply APW; lia| exact BA].
      - exact CS2.
      - exact A02. }
    destruct (L5.bo_st bx) as [v0 v1|cap q] eqn:EX.
    + apply (GO None); [exact XST| reflexivity| unfold L5.bo_cap; rewrite EX; lia].
    + destruct XST as (EC & ELB & FR). subst cap. apply (GO (Some (q, 64))); [exact ELB| split; [reflexivity| exact (proj2 (proj2 FR))]| unfold L5.bo_cap; rewrite EX; lia].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 POST MBV2 HH2. unfold L5DS.cfg.
    destruct POST as (RP12 & LANDED & XA2 & BB2 & BL2 & HP2).
    eapply (PE2 ob bb wb fba fbx Mk crk); [exact (cs_ok_call R S R1 R2 CS1 RP12)| exact LANDED| exact TIk| exact ST| exact STR| exact AOK
      | exact (conj BB (conj BL BBLK))| exists (m_vmmaps modelk); exact HH| exact CK| exact CB
      | exact XA2| exact BB2| exact BL2| exact HP2| exact (L5C.model_but_vm_trans _ _ _ MBV MBV2)| exact HH2].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 POST MBV2 HH2. unfold L5DS.cfg.
    destruct POST as (RP12 & (fbx' & nx & qx & cr1 & LB1 & XB2 & ELB1 & FR & CRA & LANDED) & BB2 & BL2 & HP2). subst LB1.
    eapply (PE3 ob bb wb fba Mk crk); [exact (cs_ok_call R S R1 R2 CS1 RP12)| exact TIk| exact ST| exact STR| exact AOK
      | exact (conj BB (conj BL BBLK))| exists (m_vmmaps modelk); exact HH| exact CK| exact CB| exact CAPB
      | exact XB2| exact FR| exact CRA| exact LANDED| exact BB2| exact BL2| exact HP2| exact (L5C.model_but_vm_trans _ _ _ MBV MBV2)| exact HH2].
Qed.

Lemma copy_fb_bit1 : forall fbo fba, Z.testbit fba 1 = false -> Z.testbit (copy_fb fbo fba false) 1 = false.
Proof.
  intros fbo fba H. unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec, H.
  change (Z.testbit 252 1) with false. change (Z.testbit 0 1) with false. change (Z.testbit 2 1) with true.
  rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_copy_x : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk ob : option (Z * Z)) (bb : L5.bigobj) (wb : list Z) (fba : Z),
  let LBk := ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 248) <= fst crk -> snd cr - (TOPB len - (17568 + 31 * 2 ^ 23)) <= snd crk ->
  str_at Mk sk ->
  objL Mk (S + 128) bb wb ob -> L5DS.reduced wb -> L5.bo_cap bb <= 268 ->
  (forall cap q, L5.bo_st bb = L5.BDyn cap q -> Z.of_nat (L5.bo_len bb) + 1 <= cap) ->
  (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->      (* [comment removed for export] *)
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk -> E2_obl sk gd fl -> E3_obl sk gd fl ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x205e8) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB STR OB RED CAPB BCAP DYN3 AOK CS PE2 PE3.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct AOK as [BA TBA].
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  destruct (u8_at_defined Mk (S + 64) (T4 (S + 64) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). apply (TS.s4 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (COPYC fx R1 Mk modelk K LBk crk (S + 64) (S + 160) S 0x205f4 fbo (L5.BO fba 2 (L5.BInl L5DS.A0 L5DS.A1)) [L5DS.A0; L5DS.A1]).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - intros DYN. exfalso. unfold L5.bo_dyn in DYN. cbn in DYN. destruct BA as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYN. discriminate.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - exact BA.
  - split; [reflexivity|]. split; [| reflexivity]. unfold L5DS.A0, L5DS.A1. repeat constructor; cbn; lia.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - intros cap q E. discriminate E.
  - lia.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 g LB2 cr2 [RP12 POST] MBV2 HH2. unfold L5CS.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    assert (D2 : L5.defined Mk (S - COPY_SCR) COPY_SCR) by (intros i Hi; apply T2; unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *; lia).
    destruct g as [|A cap].
    2:{ exfalso. destruct POST as (DYT & _). unfold L5.bo_dyn in DYT. cbn in DYT. destruct BA as (_ & _ & _ & TB & _). cbn in TB. rewrite TB in DYT. discriminate. }
    destruct POST as (_ & ELB & ECR & XB & FB & MG). subst LB2 cr2. cbn [L5.bo_fb L5.bo_len L5.bo_st] in XB.
    destruct (hpres_frame LBk COPY_SCR [(S + 64, 32)] Mk M2 FB MG D2) as [HP2 CG2].
    pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia) ltac:(unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
    assert (APW : forall o n, (o + n <= S + 64 \/ S + 96 <= o) -> apart o n [(S + 64, 32)]) by (intros o n Ho; constructor; [cbn; lia| constructor]).
    assert (TI2 : TI LB S M0 m1 M2).
    { eapply (TI_step LB LBk S COPY_SCR [(S + 64, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
      + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
      + constructor; [left; cbn; lia| constructor]. }
    assert (ST2 : L5PS.e1_statics M2 gd fl av uid rnd canary hw).
    { eapply (stat_step LBk S COPY_SCR [(S + 64, 32)]); [exact ST| exact AVS| exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia|].
      constructor; [left; cbn; lia| constructor]. }
    assert (STR2 : str_at M2 sk) by (eapply str_at_kept; [exact AG2| apply APW; lia| exact STR]).
    assert (AOK2 : L5DS.a_ok M2 (S + 160) fba) by (split; [| exact TBA]; eapply big_kept; [exact AG2| lia| lia| apply APW; lia| exact BA]).
    assert (OB2 : objL M2 (S + 128) bb wb ob).
    { eapply (objL_kept LBk COPY_SCR [(S + 64, 32)] Mk M2); [exact HP2| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold COPY_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia| apply APW; lia| exact HH| exact HH2| | exact OB].
      intros q n EO. destruct OB as (_ & _ & BBLK). destruct (L5.bo_st bb) as [v0 v1|cap' q']; [subst ob; discriminate EO|].
      destruct BBLK as [EO' _]. rewrite EO' in EO. injection EO. intros <- <-. subst ob LBk.
      assert (IN : In (q', 8 * cap') (ostr (Some (q', 8 * cap')) ++ ostr sk ++ LB)) by (left; reflexivity).
      split; [exact IN|]. split; [exact IN|].
      destruct (WFB _ IN) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo. cbn [fst snd] in B4. apply APW. lia. }
    eapply (ph_opmod1 fx1 R2 M2 model2 crk gd fl sk ob bb wb (copy_fb fbo fba false) fba);
      [exact TI2| exact ST2| exact HH2| exact MBV2'| exact Mh2| exact Ml2| exact Mm2| exact CK| exact CB| exact STR2
      | split; [exact XB| apply copy_fb_bit1; exact TBA]| exact OB2| exact RED| exact CAPB| exact BCAP| exact DYN3| exact AOK2| exact CS2| exact PE2| exact PE3].
Qed.

(* [comment removed for export] *)
Definition str_full (Mk : word -> option byte) (sk : option (Z * Z)) (s : list Z) : Prop :=
  match sk with
  | None => L5.lstr_short rsegs Mk (S + 192) s
  | Some (p, cap) => L5.lstr_long rsegs Mk (S + 192) s (cap + 1) p /\ Z.of_nat (length s) + 1 <= cap /\ 0 < cap
                     /\ (4096 <= p /\ (p + cap <= hl_img_lo L \/ hl_img_hi L <= p)) /\ p + cap <= hl_ceil L
  end.

Lemma str_full_at : forall Mk sk s, str_full Mk sk s -> str_at Mk sk.
Proof using IMGHI IMGLO S16 SLO SPW STOP len.
  intros Mk [[p cap]|] s SF.
  - destruct SF as ((TB & U0 & U8 & U16 & _) & LC & C0 & P0 & PC). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in P0. exists (cap + 1). split; [exact U0|]. split; [replace (S + 208) with (S + 192 + 16) by lia; exact U16|]. repeat split; try assumption; lia.
  - destruct SF as (LS & U0 & _). exists (2 * Z.of_nat (length s)). repeat split; [exact U0| lia| lia| apply Z.testbit_even_0].
Qed.

Lemma str_full_kept : forall LBk scr W Mk Mk1 sk s, L5C.hpres L LBk S scr W Mk Mk1 -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  apart (S + 192) 24 W -> (forall p cap, sk = Some (p, cap) -> In (p, cap) LBk /\ apart p cap W) ->
  str_full Mk sk s -> str_full Mk1 sk s.
Proof using IMGLO S16 SHI SLO SPW STOP len.
  intros LBk scr W Mk Mk1 sk s HP Hscr Hlo AP BLK SF. pose proof (ags_hpres _ _ _ _ _ HP Hscr Hlo) as AG.
  pose proof (ags_agree W Mk Mk1 (S + 192) 24 AG ltac:(lia) ltac:(lia) AP) as A24.
  destruct sk as [[p cap]|].
  - destruct SF as ((TB & U0 & U8 & U16 & BY & NUL) & LC & C0 & P0 & PC). destruct (BLK p cap eq_refl) as [IN APp].
    pose proof (blk_agree LBk scr W Mk Mk1 p cap HP IN P0 PC APp) as AB. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in P0.
    split; [| repeat split; try assumption; rewrite ?(ly_img_hi L LY); lia].
    split; [exact TB|]. split; [| split; [| split; [| split]]].
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [intros i Hi; apply A24; lia| lia| lia| exact U0].
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [intros i Hi; apply A24; lia| lia| lia| exact U8].
    + eapply (L5C.u64_at_agree rsegs Mk Mk1); [intros i Hi; apply A24; lia| lia| lia| exact U16].
    + eapply (L5C.bytes_at_agree rsegs Mk Mk1); [intros i Hi; apply AB; lia| lia| lia| exact BY].
    + eapply (L5C.u8_at_agree rsegs Mk Mk1); [intros i Hi; apply AB; lia| lia| lia| exact NUL].
  - eapply (L5C.lstr_short_agree rsegs Mk Mk1); [exact A24| lia| lia| exact SF].
Qed.

(* [comment removed for export] *)
Definition E1_obl (sk : option (Z * Z)) (gd fl : bool) : Prop :=
  forall (s : list Z) (fba fbo : Z) (Mk' : word -> option byte) (crk' : credit) (R1 : bvmap 5 word)
         (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
    cs_ok R S R1 -> L5PS.no_parse s -> (length s <= 4999)%nat -> str_full Mk' sk s ->
    L5PS.e1_landing L (ostr sk ++ LB) crk' Mk' M' R1 R' (S + 128) S fbo (length (snd (L5PS.split_sign s))) av uid rnd canary hw LB' cr' ->
    TI LB S M0 m1 Mk' -> L5PS.e1_statics Mk' gd fl av uid rnd canary hw -> L5DS.a_ok Mk' (S + 160) fba ->
    (exists VM, hi_heap HI (ostr sk ++ LB) crk' Mk' VM) ->
    fst cr - (TOPK - 264) <= fst crk' -> snd cr - (TOPB len - (21856 + 33 * 2 ^ 23)) <= snd crk' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes rsegs SCFG (mkCfg (mkst R' (Z_to_bv 64 L5PS.E1_LANDING) M' (seg_rom rsegs)) model') K.

(* [comment removed for export] *)
Lemma ph_strctor : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk : option (Z * Z)) (s : list Z) (fba : Z),
  let LBk := ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 264) <= fst crk -> snd cr - (TOPB len - (21856 + 33 * 2 ^ 23)) <= snd crk ->
  str_full Mk sk s -> (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk -> E1_obl sk gd fl -> E2_obl sk gd fl -> E3_obl sk gd fl ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x205dc) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros LBk TIk ST HH MBV Mh Ml Mm CK CB SF SLEN SRNG AOK CS PE1 PE2 PE3.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct AOK as [BA TBA].
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  destruct (u8_at_defined Mk (S + 128) (T4 (S + 128) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  pose proof (split_sign_length s) as SSL. pose proof (vblk_bound (length (snd (L5PS.split_sign s))) ltac:(lia)) as VB.
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). apply (TS.s3 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (STRCTOR fx R1 Mk modelk K LBk crk (S + 128) (S + 192) S fbo s gd fl av uid rnd canary hw).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - exact SLEN.
  - exact SRNG.
  - unfold L5PS.parse_credit, credit_ok, debit. cbn [fst snd]. rewrite K8. unfold TOPK in CK, CRK. unfold TOPB in CB, CRB. lia.
  - unfold credit_ok, L5PS.parse_debit, debit. cbn [fst snd]. rewrite K8. unfold TOPK in CK, CRK. unfold TOPB in CB, CRB. lia.
  - unfold credit_ok, L5PS.parse_debit, debit. cbn [fst snd]. rewrite K8. unfold TOPK in CK, CRK. unfold TOPB in CB, CRB. lia.
  - greg REQ1 1. reflexivity.
  - greg REQ1 2. reflexivity.
  - greg REQ1 3. exact Rgp.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - lia.
  - destruct sk as [[p cap]|]; [right| left; exact SF].
    destruct SF as (LL & LC & C0 & P0 & PC). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in P0. exists (cap + 1), p. split; [exact LL|]. split; [| lia].
    replace (cap + 1 - 1) with cap by lia. subst LBk. left. reflexivity.
  - exact ST.
  - exact AVS.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 POST ST2 MBV2 HH2. unfold L5CS.cfg.
    destruct POST as (RP12 & PARSES & (st' & BB2 & BL2 & STC & CRLE & HP2)).
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
    pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)
                  ltac:(unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
    assert (APW : forall o n, (o + n <= S + 128 \/ S + 160 <= o) -> apart o n [(S + 128, 32)]) by (intros o n Ho; constructor; [cbn; lia| constructor]).
    unfold credit_le, L5PS.parse_debit, debit in CRLE. cbn [fst snd] in CRLE. rewrite K8 in CRLE. destruct CRLE as [CRA1 CRA2].
    destruct PARSES as [PLEN PDIG].
    set (ds := snd (L5PS.split_sign s)) in *. set (neg := fst (L5PS.split_sign s)) in *. set (n := nwords (dec ds)) in *.
    pose proof (nwords_cap ds PDIG ltac:(lia)) as NC.
    pose proof (dec_bound ds (digits_all ds PDIG)) as DB.
    assert (TI2 : TI LB S M0 m1 M2).
    { eapply (TI_step LB LBk S L5PS.STRCTOR_SCR [(S + 128, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR
        | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
      + intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
      + constructor; [left; cbn; lia| constructor]. }
    assert (SF2 : str_full M2 sk s).
    { eapply (str_full_kept LBk L5PS.STRCTOR_SCR [(S + 128, 32)] Mk M2); [exact HP2
        | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
        | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
        | apply APW; lia| | exact SF].
      intros p cap E. subst sk LBk. split; [left; reflexivity|]. destruct SF as (_ & _ & _ & P0 & PC). apply APW. lia. }
    assert (AOK2 : L5DS.a_ok M2 (S + 160) fba) by (split; [| exact TBA]; eapply big_kept; [exact AG2| lia| lia| apply APW; lia| exact BA]).
    set (bb := L5.BO (L5PS.res_fb (Z.land fbo 252) n neg) n st') in *.
    assert (GO : forall ob, LB2 = ostr ob ++ LBk ->
              match st' with L5.BInl _ _ => ob = None | L5.BDyn cap q => ob = Some (q, 8 * cap) /\ L5.defined M2 q (8 * cap) /\ cap = Z.of_nat (BigModel.round_up n) /\ (3 <= n)%nat end ->
              srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x205e8) M2 (seg_rom rsegs)) model2) K).
    { intros ob ELB OBB. subst LB2.
      eapply (ph_copy_x fx1 R2 M2 model2 cr2 gd fl sk ob bb (wlist (dec ds) n) fba).
      - exact TI2.
      - exact ST2.
      - exact HH2.
      - exact MBV2'.
      - exact Mh2.
      - exact Ml2.
      - exact Mm2.
      - unfold TOPK in CK, CRK |- *. lia.
      - unfold TOPB in CB, CRB |- *. lia.
      - eapply str_full_at. exact SF2.
      - split; [exact BB2|]. split; [exact BL2|]. subst bb. cbn [L5.bo_st]. destruct st' as [v0 v1|cap q]; [exact OBB| exact (conj (proj1 OBB) (proj1 (proj2 OBB)))].
      - subst n. apply reduced_wlist. lia.
      - subst bb. unfold L5.bo_cap. cbn [L5.bo_st]. destruct st' as [v0 v1|cap q]; [lia|]. destruct OBB as (_ & _ & -> & _).
        pose proof (round_up_le n). lia.
      - subst bb. cbn [L5.bo_st L5.bo_len]. intros cap q E. destruct st' as [v0 v1|cap' q']; [discriminate E|]. injection E. intros <- <-.
        destruct OBB as (_ & _ & -> & _). pose proof (round_up_ge_S n). lia.
      - (* [comment removed for export] *)
        subst bb. unfold L5.bo_dyn. cbn [L5.bo_fb L5.bo_len L5.bo_st]. intros DY. destruct st' as [v0 v1|cap' q'].
        + exfalso. destruct BB2 as (_ & _ & _ & TB & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in TB. rewrite TB in DY. discriminate DY.
        + destruct OBB as (_ & _ & _ & N3'). exact N3'.
      - exact AOK2.
      - exact CS2.
      - exact PE2.
      - exact PE3. }
    destruct st' as [v0 v1|cap A].
    + destruct STC as [N2 ELB]. apply (GO None); [exact ELB| reflexivity].
    + destruct STC as (N3 & EC & ELB & FR). apply (GO (Some (A, 8 * cap))); [exact ELB|]. split; [reflexivity|]. split; [exact (proj2 (proj2 FR))| split; [exact EC| exact N3]].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 LB2 cr2 NOP LANDING MBV2 HH2. unfold L5CS.cfg.
    eapply (PE1 s fba fbo Mk crk R1); [exact CS1| exact NOP| exact SLEN| exact SF| exact LANDING| exact TIk| exact ST| exact (conj BA TBA)
      | exists (m_vmmaps modelk); exact HH| exact CK| exact CB| exact (L5C.model_but_vm_trans _ _ _ MBV MBV2)| exact HH2].
Qed.

(* [comment removed for export] *)
Lemma hpres_scratch_irrel : forall LBk scr W Mk Mk1 (VM : VmMaps) crk0,
  hi_heap HI LBk crk0 Mk VM -> 0 <= scr -> hl_sptop L - 2 ^ 23 + scr <= S ->
  L5C.hpres L LBk S scr ((S - scr, scr) :: W) Mk Mk1 -> L5C.hpres L LBk S scr W Mk Mk1.
Proof using HIok LY SLO SPW len.
  intros LBk scr W Mk Mk1 VM crk0 HH Hscr Hlo HP. hp_split HP KEPT DEF.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & _).
  split; [| first [exact DEF | split; [exact DEF| exact (proj2 (proj2 HP))]]].
  intros a (Ha & CA & NE & OW). apply KEPT. split; [exact Ha|]. split; [exact CA|]. split; [exact NE|].
  intros r [<-|Hr]; [| exact (OW r Hr)]. unfold L5.in_rng. cbn [fst snd]. intros IN.
  destruct CA as [(b & Hb & Hrb)|[[A1 A2]|[A1 A2]]].
  - destruct (WFB b Hb) as ((B1lo & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B1lo. lia.
  - lia.
  - rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in A1. lia.
Qed.

Lemma land252_bit1 : forall fbo, Z.testbit (Z.land fbo 252) 1 = false.
Proof. intros fbo. rewrite Z.land_spec. change (Z.testbit 252 1) with false. apply Bool.andb_false_r. Qed.

(* [comment removed for export] *)
Lemma ph_cstr : forall (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd fl : bool)
    (sk : option (Z * Z)) (s : list Z),
  let LBk := ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  L5PS.e1_statics Mk gd fl av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  m_halted modelk = None -> m_vm_lazy modelk = [] -> m_vm_materialized modelk = [] ->
  fst cr - (TOPK - 280) <= fst crk -> snd cr - (TOPB len - (21984 + 35 * 2 ^ 23)) <= snd crk ->
  str_full Mk sk s -> (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
  cs_ok R S Rk -> getr Rk 8%bv = wz len -> 0 <= len < 5000 ->
  E1_obl sk gd fl -> E2_obl sk gd fl -> E3_obl sk gd fl ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x205bc) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until s. intros LBk TIk ST HH MBV Mh Ml Mm CK CB SF SLEN SRNG CS RS0 SMALL PE1 PE2 PE3.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & CK0 & CB0).
  destruct (u8_at_defined Mk (S + 160) (T4 (S + 160) ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia)) as (fbo & FBO & FBOR).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). rewrite RS0. apply (TS.s2_small (wz S)). exact SMALL. }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  eapply (CSTR fx R1 Mk modelk K LBk crk (S + 160) S 0x205dc fbo).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
  - greg REQ1 11. reflexivity.
  - unfold L5PS.parse_credit, credit_ok, debit. cbn [fst snd]. rewrite K8. change (L5PS.vblk 38) with 64. unfold TOPK in CK, CRK. unfold TOPB in CB, CRB. lia.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. reflexivity.
  - greg REQ1 3. exact Rgp.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *. lia.
  - eapply e1_img. exact ST.
  - exact FBO.
  - exact FBOR.
  - clear -S16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply T4. lia.
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 cr2 POST MBV2 HH2. unfold L5CS.cfg.
    destruct POST as (RP12 & BA2 & CRLE & HP2).
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV2) as MBV2'.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    pose proof (HPG _ _ _ _ _ _ HP2) as CG2.
    pose proof (ags_hpres _ _ _ _ _ HP2 ltac:(unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)
                  ltac:(unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG2.
    assert (APW : forall o n, (o + n <= S + 160 \/ S + 192 <= o) -> apart o n [(S + 160, 32)]) by (intros o n Ho; constructor; [cbn; lia| constructor]).
    unfold credit_le, L5PS.parse_debit, debit in CRLE. cbn [fst snd] in CRLE. rewrite K8 in CRLE. change (L5PS.vblk 38) with 64 in CRLE. destruct CRLE as [CRA1 CRA2].
    eapply (ph_strctor fx1 R2 M2 model2 cr2 gd fl sk s (Z.land fbo 252)).
    + eapply (TI_step LB LBk S L5PS.CSTR_SCR [(S + 160, 32)]); [exact TIk| exact HP2| exact CG2| | exact LBR
        | unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia|].
      * intros b Hb. subst LBk. rewrite !in_app_iff. tauto.
      * constructor; [left; cbn; lia| constructor].
    + eapply (stat_step LBk S L5PS.CSTR_SCR [(S + 160, 32)]); [exact ST| exact AVS| exact HP2
        | unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
        | unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia| lia|].
      constructor; [left; cbn; lia| constructor].
    + exact HH2.
    + exact MBV2'.
    + exact Mh2.
    + exact Ml2.
    + exact Mm2.
    + unfold TOPK in CK, CRK |- *. lia.
    + unfold TOPB in CB, CRB |- *. lia.
    + eapply (str_full_kept LBk L5PS.CSTR_SCR [(S + 160, 32)] Mk M2); [exact HP2
        | unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
        | unfold L5PS.CSTR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
        | apply APW; lia| | exact SF].
      intros p cap E. subst sk LBk. split; [left; reflexivity|]. destruct SF as (_ & _ & _ & P0 & PC). apply APW. lia.
    + exact SLEN.
    + exact SRNG.
    + split; [exact BA2| apply land252_bit1].
    + exact CS2.
    + exact PE1.
    + exact PE2.
    + exact PE3.
Qed.

(* [comment removed for export] *)
Lemma ph_small : forall (fx : FPState) (R1 R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (gd fl : bool)
    (gr : growth) (LB2 : list (Z * Z)) (cr2 : credit) (VM1 : VmMaps),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S <= a < S + 240) -> m1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, S + 240 - 65536 <= a < S + 240 -> m1 (Z_to_bv 64 a) <> None) ->
  hi_heap HI LB cr m1 VM1 ->
  L5PS.e1_statics M0 gd fl av uid rnd canary hw ->
  cs_ok R S R1 -> getr R1 8%bv = wz len ->
  strinit_post L LB cr m1 M2 R1 R2 (S + 192) S (map bv_unsigned payload) gr LB2 cr2 ->
  model_but_vm model0 model2 -> hi_heap HI LB2 cr2 M2 (m_vmmaps model2) ->
  m_halted model2 = None -> m_vm_lazy model2 = [] -> m_vm_materialized model2 = [] ->
  len < 5000 ->
  (forall sk, E1_obl sk gd fl) -> (forall sk, E2_obl sk gd fl) -> (forall sk, E3_obl sk gd fl) ->
  srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x205bc) M2 (seg_rom rsegs)) model2) K.
Proof.
  intros until VM1. intros OUT1 DEF1 HH1 ST0 CS1 RS0 [RP12 POSTg] MBV2 HH2 Mh2 Ml2 Mm2 SMALL PE1 PE2 PE3.
  pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (WF & _).
  assert (LEN0 : 0 <= len) by (unfold len; lia).
  assert (TI1 : TI LB S M0 m1 m1).
  { split; [| split; [| split]].
    - intros a (Ha & CA & NE & NF). apply OUT1; [exact Ha|].
      destruct CA as [(b & Hb & Hr)|[[A1 A2]|[A1 A2]]]; [destruct (WF b Hb) as ((B1lo & B1 & B2 & B3 & B4) & _); lia| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in A1; lia].
    - intros a Ha. apply DEF1. lia.
    - intros; reflexivity.
    - intros a Ha. apply DEF1. lia. }
  assert (STm1 : L5PS.e1_statics m1 gd fl av uid rnd canary hw).
  { eapply e1_statics_agree; [exact ST0|]. intros a Da. change Plain.M.loaded_segments with rsegs. apply OUT1; unfold e1_dom in Da.
    - destruct ST0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVlo & AVhi & _). lia.
    - lia. }
  (* [comment removed for export] *)
  assert (POST1 : exists sk, LB2 = ostr sk ++ LB /\ L5C.hpres L LB S STRINIT_SCR [(S + 192, 24)] m1 M2 /\ cgrows LB S STRINIT_SCR m1 M2
                  /\ str_full M2 sk (map bv_unsigned payload)
                  /\ fst cr - 8 <= fst cr2 /\ snd cr - (len + 10 + 2 ^ 23) <= snd cr2).
  { destruct gr as [|p cap].
    - destruct POSTg as (L22 & ELB2 & Ecr2 & LSTR & FB & MG). subst LB2 cr2. exists None.
      assert (D1 : L5.defined m1 (S - STRINIT_SCR) STRINIT_SCR) by (intros i Hi; apply DEF1; unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in Hi |- *; lia).
      destruct (hpres_frame LB STRINIT_SCR [(S - STRINIT_SCR, STRINIT_SCR); (S + 192, 24)] m1 M2 FB MG D1) as [HP CG].
      split; [reflexivity|]. split; [| split; [| split; [exact LSTR| lia]]].
      + eapply (hpres_scratch_irrel LB STRINIT_SCR); [exact HH1| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| exact HP].
      + intros a Ha CA NE X. apply MG. exact X.
    - destruct POSTg as (L23 & Hcap & ELB2 & Ecr2 & FRESH & LSTR & HPRES). rewrite length_map in L23, Hcap. subst LB2 cr2. exists (Some (p, cap)).
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FRESH) as (PB1 & PB2 & PB3 & PB4 & PB5).
      pose proof (TK.str_cap_bound len LEN0) as CAPB. rewrite <- Hcap in CAPB.
      split; [reflexivity|]. split; [exact HPRES|]. split; [exact (HPG _ _ _ _ _ _ HPRES)|]. split; [| unfold debit; cbn [fst snd]; rewrite K8; lia].
      cbn [str_full]. rewrite length_map. split; [exact LSTR|]. split; [lia|]. split; [lia|]. split; [split; [exact PB1| exact PB2]| exact PB5]. }
  destruct POST1 as (sk & ELB2 & HP2 & CG2 & SF2 & CK2 & CB2). subst LB2.
  eapply (ph_cstr fx R2 M2 model2 cr2 gd fl sk (map bv_unsigned payload)).
  - eapply (TI_step LB LB S STRINIT_SCR [(S + 192, 24)]); [exact TI1| exact HP2| exact CG2| auto| exact LBR| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia| constructor; [left; cbn; lia| constructor]].
  - eapply (stat_step LB S STRINIT_SCR [(S + 192, 24)]); [exact STm1| exact AVS| exact HP2| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| constructor; [left; cbn; lia| constructor]].
  - exact HH2.
  - exact MBV2.
  - exact Mh2.
  - exact Ml2.
  - exact Mm2.
  - unfold TOPK in CRK |- *. lia.
  - unfold TOPB in CRB |- *. lia.
  - exact SF2.
  - rewrite length_map. unfold len. lia.
  - apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. cbn. lia.
  - eapply cs_ok_call; [exact CS1| exact RP12].
  - rewrite (RP12 8%bv) by (cbn; tauto). exact RS0.
  - lia.
  - apply PE1.
  - apply PE2.
  - apply PE3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ph_catch : forall (exc : (word -> option byte) -> Z -> list (Z * Z) -> Prop)
    (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd : bool)
    (sk : option (Z * Z)) (LBX : list (Z * Z)) (obj : Z),
  catch_spec exc ->
  let LBk := LBX ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  statics_landed Mk gd av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  str_at Mk sk ->
  exc Mk obj LBX ->
  cs_ok R S Rk -> getr Rk 8%bv = Z_to_bv 64 (obj - 32) -> getr Rk 9%bv = Z_to_bv 64 1 ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x20800) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until obj. intros CATCH LBk TIk STL HH MBV CK CB SF EXC CS RS0 RS1.
  pose proof TIk as (T1 & T2 & T3 & T4).
  pose proof (L5C.halted_but_vm _ _ MBV) as Mh. rewrite Mh0 in Mh.
  pose proof (L5C.lazy_but_vm _ _ MBV) as Ml. rewrite Ml0 in Ml.
  pose proof (L5C.materialized_but_vm _ _ MBV) as Mm. rewrite Mm0 in Mm.
  pose proof STL as (C1 & C2 & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _ & _ & _ & _ & _ & I1 & I2 & I3).
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). rewrite RS0, RS1. apply (TS.c1' (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 E REQ1. inversion E; subst R1c pc1 m1'; clear E.
  pose proof (cs_ok_of_eqv R S R1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REQ1) as CS1.
  (* [comment removed for export] *)
  eapply (CATCH fx R1 Mk modelk K (ostr sk ++ LB) LBX crk obj S).
  - exact HH.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. reflexivity.
  - greg REQ1 2. reflexivity.
  - greg REQ1 3. exact Rgp.
  - greg REQ1 4. reflexivity.
  - split; [exact S16|]. split; [unfold CATCH_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply T2. unfold CATCH_SCR, HEAP_STACK in Hi |- *. lia.
  - exact EXC.
  - exact C1.
  - exact C2.
  - exact I1.
  - exact I2.
  - exact I3.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 RP12 C1' C2' HP2 MBV2 HH2.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    pose proof (cs_ok_call R S R1 R2 CS1 RP12) as CS2.
    eapply (TK.srz_evt_canonMS _ R2 _ M2 model2 K Mh2 Ml2).
    { rewrite (canon_cs R S R2 CS2). apply (TS.j1 (wz S)). }
    2:{ intros ms' ->. eexists _, _, _. reflexivity. }
    intros R3c pc3 m3 R3 E REQ3. inversion E; subst R3c pc3 m3; clear E.
    set (W := [(L5PS.EH_CAUGHT, 8); (L5PS.EH_UNCAUGHT, 4)]) in HP2.
    assert (WOK : Forall (wok LB S) W).
    { subst W. unfold L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT. constructor; [| constructor; [| constructor]]; right; right; intros a Ha; unfold L5.in_rng in Ha; cbn in Ha; unfold in_footZ; lia. }
    eapply (ph_strdtor fx2 R3 M2 model2 crk gd true sk).
    + eapply (TI_step LB (ostr sk ++ LB) S CATCH_SCR W); [exact TIk| exact HP2| exact (HPG _ _ _ _ _ _ HP2)| | exact LBR| unfold CATCH_SCR, HEAP_STACK; lia| lia| lia| exact WOK].
      intros b Hb. rewrite in_app_iff. tauto.
    + eapply (e1_statics_of_landed Mk M2); [exact STL| | exact C1'| exact C2'].
      intros a [Da NEH]. change Plain.M.loaded_segments with rsegs.
      eapply (dom_kept (ostr sk ++ LB) S CATCH_SCR W Mk M2 av a); [exact HP2| exact AVS| exact AVlo| exact AVhi| unfold CATCH_SCR, HEAP_STACK; lia| unfold CATCH_SCR, HEAP_STACK; lia| lia| exact Da|].
      subst W. unfold L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT. intros r [<-|[<-|[]]]; unfold L5.in_rng; cbn; lia.
    + exact HH2.
    + eapply L5C.model_but_vm_trans; [exact MBV| exact MBV2].
    + exact Mh2.
    + exact Ml2.
    + exact Mm2.
    + exact CK.
    + exact CB.
    + eapply str_at_kept; [eapply (ags_hpres _ _ _ _ _ HP2); unfold CATCH_SCR, HEAP_STACK; lia| | exact SF].
      subst W. unfold L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT. constructor; [cbn; lia| constructor; [cbn; lia| constructor]].
    + eapply cs_ok_of_eqv. exact REQ3.
Qed.

(* [comment removed for export] *)
Lemma ph_pada : forall (exc : (word -> option byte) -> Z -> list (Z * Z) -> Prop)
    (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd : bool)
    (sk : option (Z * Z)) (LBX : list (Z * Z)) (obj fba : Z),
  catch_spec exc ->
  let LBk := LBX ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  statics_landed Mk gd av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  str_at Mk sk ->
  exc Mk obj LBX ->
  L5DS.a_ok Mk (S + 160) fba ->
  cs_ok R S Rk -> getr Rk 8%bv = Z_to_bv 64 (obj - 32) -> getr Rk 9%bv = Z_to_bv 64 1 ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x207e0) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until fba. intros CATCH LBk TIk STL HH MBV CK CB SF EXC AOK CS RS0 RS1.
  pose proof (L5C.halted_but_vm _ _ MBV) as Mh. rewrite Mh0 in Mh.
  pose proof (L5C.lazy_but_vm _ _ MBV) as Ml. rewrite Ml0 in Ml.
  destruct AOK as [BA TBA]. destruct BA as (FB & FBR & LEN' & TB0 & U16 & U24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in FB, FBR, LEN', TB0, U16, U24.
  eapply (TK.srz_evt_canonMS _ Rk _ Mk modelk K Mh Ml).
  { rewrite (canon_cs R S Rk CS). rewrite RS0, RS1.
    eapply (TS.pd_a (wz S)) with (fb := fba) (cap := 2) (q := S + 160 + 16); rewrite ?wz_unsigned by lia.
    - apply TK.ro_cells_u8; [exact FB| lia| lia].
    - exact FBR.
    - intros DYN. exfalso. rewrite TB0 in DYN. discriminate. }
  2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
  intros R1c pc1 m1' R1 (a0' & a1' & CASES) REQ1.
  destruct CASES as [[_ E]|(TB1 & _ & _ & E)]; [| exfalso; rewrite TB0 in TB1; discriminate].
  inversion E; subst R1c pc1 m1'; clear E.
  eapply (ph_catch exc fx R1 Mk modelk crk gd sk LBX obj CATCH TIk STL HH MBV CK CB SF EXC).
  - eapply cs_ok_of_eqv. exact REQ1.
  - greg REQ1 8. reflexivity.
  - greg REQ1 9. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_padb : forall (exc : (word -> option byte) -> Z -> list (Z * Z) -> Prop)
    (fx : FPState) (Rk : bvmap 5 word) (Mk : word -> option byte) (modelk : Model) (crk : credit) (gd : bool)
    (sk ob : option (Z * Z)) (LBX : list (Z * Z)) (obj fba : Z) (bb : L5.bigobj),
  catch_spec exc ->
  (forall M M', (forall b, In b LBX -> L5C.agree_on M M' (fst b) (snd b)) -> exc M obj LBX -> exc M' obj LBX) ->
  let LBk := LBX ++ ostr ob ++ ostr sk ++ LB in
  TI LB S M0 m1 Mk ->
  statics_landed Mk gd av uid rnd canary hw ->
  hi_heap HI LBk crk Mk (m_vmmaps modelk) -> model_but_vm model0 modelk ->
  fst cr - TOPK <= fst crk -> snd cr - TOPB len <= snd crk ->
  str_at Mk sk ->
  exc Mk obj LBX ->
  L5DS.a_ok Mk (S + 160) fba -> obj_at Mk (S + 128) bb ob ->
  cs_ok R S Rk -> getr Rk 8%bv = Z_to_bv 64 (obj - 32) -> getr Rk 9%bv = Z_to_bv 64 1 ->
  srealizes rsegs SCFG (mkCfg (mkst Rk (Z_to_bv 64 0x207c0) Mk (seg_rom rsegs)) modelk) K.
Proof.
  intros until bb. intros CATCH EXCA LBk TIk STL HH MBV CK CB SF EXC AOK OB CS RS0 RS1.
  pose proof TIk as (T1 & T2 & T3 & T4).
  pose proof (L5C.halted_but_vm _ _ MBV) as Mh. rewrite Mh0 in Mh.
  pose proof (L5C.lazy_but_vm _ _ MBV) as Ml. rewrite Ml0 in Ml.
  pose proof (L5C.materialized_but_vm _ _ MBV) as Mm. rewrite Mm0 in Mm.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & WFND & _ & _).
  pose proof STL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _).
  eapply (dtor_call fx 0x207c0 128 0x207e0 S Rk Mk modelk K LBk crk bb); try eassumption; try lia.
  { apply TS.pd_b; rewrite ?wz_unsigned by lia; lia. }
  { split; [lia| reflexivity]. }
  { apply (cs_eqv R S Rk CS). }
  { exact (proj1 OB). }
  { intros cap q E. destruct OB as [_ OBB]. rewrite E in OBB. subst ob LBk. rewrite !in_app_iff. cbn. tauto. }
  { intros i Hi. apply T2. unfold OPDEL_SCR, HEAP_STACK in Hi |- *. lia. }
  intros fx1 R1 M1 model1 LB1 RP1 ELB1 HP1 MBV1 HH1.
  assert (ELB1' : LB1 = LBX ++ ostr sk ++ LB).
  { destruct OB as [_ OBB]. destruct (L5.bo_st bb) as [v0 v1|cap q]; subst ob; rewrite ELB1; [reflexivity|]. subst LBk.
    apply (lb_remove_mid LBX q (8 * cap)). exact WFND. }
  clear ELB1. subst LB1.
  pose proof (ags_hpres _ _ _ _ _ HP1 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia)) as AG1.
  assert (APN : forall o n, apart o n []) by (intros; constructor).
  eapply (ph_pada exc fx1 R1 M1 model1 crk gd sk LBX obj fba CATCH).
  - eapply (TI_step LB _ S OPDEL_SCR []); [exact TIk| exact HP1| apply cgrows_nil; exact HP1| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
    intros b Hb. rewrite !in_app_iff. tauto.
  - eapply (landed_step _ S OPDEL_SCR []); [exact STL| exact AVS| exact HP1| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor].
  - exact HH1.
  - eapply L5C.model_but_vm_trans; [exact MBV| exact MBV1].
  - exact CK.
  - exact CB.
  - eapply str_at_kept; [exact AG1| apply APN| exact SF].
  - eapply EXCA; [| exact EXC]. intros b Hb.
    assert (IN : In b (LBX ++ ostr ob ++ ostr sk ++ LB)) by (rewrite in_app_iff; left; exact Hb).
    assert (IN1 : In b (LBX ++ ostr sk ++ LB)) by (rewrite in_app_iff; left; exact Hb).
    destruct (WFB b IN) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo.
    destruct b as [q n]. cbn [fst snd] in *. eapply (blk_agree _ OPDEL_SCR [] Mk M1 q n HP1 IN1); [lia| lia| apply APN].
  - destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG1| lia| lia| apply APN| exact BA].
  - eapply (cs_ok_canon_call R S Rk R1). exact RP1.
  - rewrite (RP1 8%bv) by (cbn; tauto). rewrite <- RS0. reflexivity.
  - rewrite (RP1 9%bv) by (cbn; tauto). rewrite <- RS1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_pad1 : forall sk gd fl, E1_obl sk gd fl.
Proof.
  intros sk gd fl s fba fbo Mk crk R1 fx R' M' model' LB' cr' CS1 NOP SLEN SF LANDING TIk ST AOK [VM HH] CK CB MBV' HH'.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct LANDING as (obj & ref & RP1 & A0 & A1 & ELB & CRLE & FRX & FRR & EXC & STL & BB0 & HP).
  subst LB'.
  pose proof (L5C.halted_but_vm _ _ MBV') as Mh'. rewrite Mh0 in Mh'.
  pose proof (L5C.lazy_but_vm _ _ MBV') as Ml'. rewrite Ml0 in Ml'.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _).
  pose proof (split_sign_length s) as SSL. pose proof (vblk_bound (length (snd (L5PS.split_sign s))) ltac:(lia)) as VB.
  unfold credit_le, L5PS.parse_debit, debit in CRLE. cbn [fst snd] in CRLE. rewrite K8 in CRLE. destruct CRLE as [CRA1 CRA2].
  set (W := [(S + 128, 32); (L5PS.EH_UNCAUGHT, 4); (L5PS.SYSCAT_GUARD, 2); (L5PS.UW_FLAGS, 6)]) in HP.
  assert (WOK : Forall (wok LB S) W).
  { subst W. unfold L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS.
    constructor; [left; cbn; lia|]. constructor; [| constructor; [| constructor; [| constructor]]]; right; right; intros a Ha; unfold L5.in_rng in Ha; cbn in Ha; unfold in_footZ; lia. }
  assert (APW : forall o n, (o + n <= 0x10000 \/ 0x91000 <= o) -> (o + n <= S + 128 \/ S + 160 <= o) -> apart o n W).
  { intros o n Ho Hn. subst W. unfold L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS.
    constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
  pose proof (ags_hpres _ _ _ _ _ HP ltac:(unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)
                ltac:(unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia)) as AG.
  assert (TI' : TI LB S M0 m1 M').
  { eapply (TI_step LB (ostr sk ++ LB) S L5PS.STRCTOR_SCR W); [exact TIk| exact HP| exact (HPG _ _ _ _ _ _ HP)| | exact LBR
      | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| lia| exact WOK].
    intros b Hb. rewrite in_app_iff. tauto. }
  assert (SF' : str_full M' sk s).
  { eapply (str_full_kept (ostr sk ++ LB) L5PS.STRCTOR_SCR W Mk M'); [exact HP
      | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
      | unfold L5PS.STRCTOR_SCR, L5PS.TOBIG_SCR, L5PS.DETAIL_SCR, ADDD_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK; lia
      | apply APW; lia| | exact SF].
    intros p cap E. subst sk. split; [left; reflexivity|]. destruct SF as (_ & _ & _ & P0 & PC). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in P0. apply APW; lia. }
  assert (AOK' : L5DS.a_ok M' (S + 160) fba).
  { destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG| lia| lia| apply APW; lia| exact BA]. }
  pose proof (statics_landed_e1 M' Mk gd fl av uid rnd canary hw ST STL) as STL'.
  pose proof (cs_ok_call R S R1 R' CS1 RP1) as CS'.
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ R' _ M' model' K Mh' Ml').
  { rewrite (canon_cs R S R' CS'). rewrite A0, A1. apply (TS.p1 (wz S)). }
  2:{ intros ms' ->. eexists _, _, _. reflexivity. }
  intros R2c pc2 m2 R2 E REQ2. inversion E; subst R2c pc2 m2; clear E.
  eapply (ph_pada exc1 fx R2 M' model' cr' true sk [(ref, 41); (obj - 128, 160)] obj fba CATCH1 TI' STL').
  - exact HH'.
  - exact MBV'.
  - unfold TOPK in CK, CRK |- *. lia.
  - unfold TOPB in CB, CRB |- *. lia.
  - eapply str_full_at. exact SF'.
  - eapply EXC1_of_landing; [exact EXC| exact FRX| exact FRR].
  - exact AOK'.
  - eapply cs_ok_of_eqv. exact REQ2.
  - greg REQ2 8. reflexivity.
  - greg REQ2 9. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xs_foot_wok : forall Sx, Forall (wok LB Sx) xs_foot.
Proof using S16 SLO SPW XSF len.
  intros Sx. eapply List.Forall_impl; [| exact XSF]. intros r Hr. cbn in Hr. right. right. intros a Ha. unfold L5.in_rng in Ha. unfold in_footZ. lia.
Qed.
Lemma xs_foot_apart : forall o n, (o + n <= 0x10000 \/ 0x90758 <= o) -> apart o n xs_foot.
Proof using S16 SLO SPW XSF len.
  intros o n Ho. eapply List.Forall_impl; [| exact XSF]. intros r Hr. cbn in Hr |- *. lia.
Qed.

(* [comment removed for export] *)
Lemma ph_pad2 : forall sk gd fl, E2_obl sk gd fl.
Proof.
  intros sk gd fl ob bb wb fba fbx Mk crk fx R' M' model' LB' cr' CS' LANDED TIk ST STR AOK OB [VM HH] CK CB XA BB' BL' HP MBV' HH'.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct (E2L _ _ _ _ _ _ _ _ _ _ _ _ _ _ LANDED) as (obj & LBX & A0 & A1 & ELB & EXC & STL & CR1 & CR2). subst LB'.
  pose proof (L5C.halted_but_vm _ _ MBV') as Mh'. rewrite Mh0 in Mh'.
  pose proof (L5C.lazy_but_vm _ _ MBV') as Ml'. rewrite Ml0 in Ml'.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _).
  set (W := (S + 64, 32) :: xs_foot) in HP.
  assert (WOK : Forall (wok LB S) W) by (subst W; constructor; [left; cbn; lia| apply xs_foot_wok]).
  assert (APW : forall o n, (o + n <= 0x10000 \/ 0x91000 <= o) -> (o + n <= S + 64 \/ S + 96 <= o) -> apart o n W).
  { intros o n Ho Hn. subst W. constructor; [cbn; lia| apply xs_foot_apart; lia]. }
  pose proof (ags_hpres _ _ _ _ _ HP ltac:(unfold L5DS.SCR_OPMOD; lia) ltac:(unfold L5DS.SCR_OPMOD; lia)) as AG.
  assert (TI' : TI LB S M0 m1 M').
  { eapply (TI_step LB (ostr ob ++ ostr sk ++ LB) S L5DS.SCR_OPMOD W); [exact TIk| exact HP| exact (HPG _ _ _ _ _ _ HP)| | exact LBR| unfold L5DS.SCR_OPMOD; lia| lia| lia| exact WOK].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (STR' : str_at M' sk) by (eapply str_at_kept; [exact AG| apply APW; lia| exact STR]).
  assert (AOK' : L5DS.a_ok M' (S + 160) fba).
  { destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG| lia| lia| apply APW; lia| exact BA]. }
  assert (OB' : obj_at M' (S + 128) bb ob).
  { split; [exact BB'|]. destruct OB as (_ & _ & BBLK). destruct (L5.bo_st bb); [exact BBLK| exact (proj1 BBLK)]. }
  destruct XA as [XB XNEG]. destruct XB as (FB & FBR & LEN' & TB0 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in FB, FBR, LEN', TB0.
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ R' _ M' model' K Mh' Ml').
  { rewrite (canon_cs R S R' CS'). rewrite A0, A1.
    eapply (TS.p3 (wz S)) with (fb := fbx) (cap := 2) (q := S + 64 + 16); rewrite ?wz_unsigned by lia.
    - apply TK.ro_cells_u8; [exact FB| lia| lia].
    - exact FBR.
    - intros DYN. exfalso. rewrite TB0 in DYN. discriminate. }
  2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
  intros R2c pc2 m2 R2 (a0' & a1' & CASES) REQ2.
  destruct CASES as [[_ E]|(TB1 & _ & _ & E)]; [| exfalso; rewrite TB0 in TB1; discriminate].
  inversion E; subst R2c pc2 m2; clear E.
  eapply (ph_padb exc2 fx R2 M' model' cr' gd sk ob LBX obj fba bb CATCH2 (fun Ma Mb => EXC2_agree Ma Mb obj LBX) TI' STL).
  - exact HH'.
  - exact MBV'.
  - unfold TOPK in CK, CRK |- *. lia.
  - unfold TOPB in CB, CRB |- *. lia.
  - exact STR'.
  - exact EXC.
  - exact AOK'.
  - exact OB'.
  - eapply cs_ok_of_eqv. exact REQ2.
  - greg REQ2 8. reflexivity.
  - greg REQ2 9. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_pad3 : forall sk gd fl, E3_obl sk gd fl.
Proof.
  intros sk gd fl ob bb wb fba Mk crk fx R' M' model' LB' cr' fbx' nx qx cr1 CS' TIk ST STR AOK OB [VM HH] CK CB CAPB XB FRX CRA LANDED BB' BL' HP MBV' HH'.
  pose proof TIk as (T1 & T2 & T3 & T4). pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV.
  destruct (E3L _ _ _ _ _ _ _ _ _ _ _ _ _ _ LANDED) as (obj & LBX & A0 & A1 & ELB & EXC & STL & CR1 & CR2). subst LB'.
  pose proof (L5C.halted_but_vm _ _ MBV') as Mh'. rewrite Mh0 in Mh'.
  pose proof (L5C.lazy_but_vm _ _ MBV') as Ml'. rewrite Ml0 in Ml'.
  pose proof (L5C.materialized_but_vm _ _ MBV') as Mm'. rewrite Mm0 in Mm'.
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _).
  unfold L5DS.credit_after, L5DS.OPMOD1_K, L5DS.opmod1_bytes in CRA. rewrite K8 in CRA. destruct CRA as [CRA1 CRA2].
  pose proof (L5C.fresh_block_bounds _ _ _ _ _ FRX) as (QB1 & QB2 & QB3 & QB4). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in QB1.
  set (W := (S + 64, 32) :: xs_foot) in HP.
  assert (WOK : Forall (wok LB S) W) by (subst W; constructor; [left; cbn; lia| apply xs_foot_wok]).
  assert (APW : forall o n, (o + n <= 0x10000 \/ 0x91000 <= o) -> (o + n <= S + 64 \/ S + 96 <= o) -> apart o n W).
  { intros o n Ho Hn. subst W. constructor; [cbn; lia| apply xs_foot_apart; lia]. }
  pose proof (ags_hpres _ _ _ _ _ HP ltac:(unfold L5DS.SCR_OPMOD; lia) ltac:(unfold L5DS.SCR_OPMOD; lia)) as AG.
  assert (TI' : TI LB S M0 m1 M').
  { eapply (TI_step LB (ostr ob ++ ostr sk ++ LB) S L5DS.SCR_OPMOD W); [exact TIk| exact HP| exact (HPG _ _ _ _ _ _ HP)| | exact LBR| unfold L5DS.SCR_OPMOD; lia| lia| lia| exact WOK].
    intros b Hb. rewrite !in_app_iff. tauto. }
  assert (STR' : str_at M' sk) by (eapply str_at_kept; [exact AG| apply APW; lia| exact STR]).
  assert (AOK' : L5DS.a_ok M' (S + 160) fba).
  { destruct AOK as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG| lia| lia| apply APW; lia| exact BA]. }
  assert (OB' : obj_at M' (S + 128) bb ob).
  { split; [exact BB'|]. destruct OB as (_ & _ & BBLK). destruct (L5.bo_st bb); [exact BBLK| exact (proj1 BBLK)]. }
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH') as (WFB' & WFND' & CK' & CB').
  destruct XB as (FB & FBR & LEN' & TB1 & U16 & U24 & _). cbn [L5.bo_fb L5.bo_len L5.bo_st] in FB, FBR, LEN', TB1, U16, U24.
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ R' _ M' model' K Mh' Ml').
  { rewrite (canon_cs R S R' CS'). rewrite A0, A1.
    eapply (TS.p3 (wz S)) with (fb := fbx') (cap := 8) (q := qx); rewrite ?wz_unsigned by lia.
    - apply TK.ro_cells_u8; [exact FB| lia| lia].
    - exact FBR.
    - intros _. split; [| lia]. split; [exact (conj I (conj I I))|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
      + apply (TK.bytes_at_of_rdn M' 8); [exact U16| apply (TK.rdn_length _ _ _ _ U16)| lia| lia].
      + cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite length_le8. replace (S + 64 + 16 + 8) with (S + 64 + 24) by lia.
        apply (TK.bytes_at_of_rdn M' 8); [exact U24| apply (TK.rdn_length _ _ _ _ U24)| lia| lia]. }
  2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
  intros R2c pc2 m2 R2 (a0' & a1' & CASES) REQ2.
  destruct CASES as [[TB0 E]|(_ & -> & -> & E)]; [exfalso; rewrite TB1 in TB0; discriminate|].
  inversion E; subst R2c pc2 m2; clear E.
  (* [comment removed for export] *)
  eapply (OPDELS fx R2 M' model' K (LBX ++ (qx, 64) :: ostr ob ++ ostr sk ++ LB) cr' qx 64 S 0x207c0).
  - exact HH'.
  - split; [exact Mh'| split; [exact Ml'| exact Mm']].
  - exact HK0.
  - rewrite in_app_iff. right. left. reflexivity.
  - greg REQ2 10. reflexivity.
  - greg REQ2 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ2 2. reflexivity.
  - greg REQ2 4. reflexivity.
  - split; [exact S16|]. split; [unfold OPDEL_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply (proj1 (proj2 TI')). unfold OPDEL_SCR, HEAP_STACK in Hi |- *. lia.
  - (* [comment removed for export] *)
    intros fx3 R3 M3 model3 RP23 HP3 MBV3 HH3. unfold L5CS.cfg.
    replace (lb_remove qx (LBX ++ (qx, 64) :: ostr ob ++ ostr sk ++ LB)) with (LBX ++ ostr ob ++ ostr sk ++ LB) in HP3, HH3
      by (symmetry; apply (lb_remove_mid LBX qx 64); exact WFND').
    pose proof (ags_hpres _ _ _ _ _ HP3 ltac:(unfold OPDEL_SCR, HEAP_STACK; lia) ltac:(unfold OPDEL_SCR, HEAP_STACK; lia)) as AG3.
    assert (APN : forall o n, apart o n []) by (intros; constructor).
    eapply (ph_padb exc3 fx3 R3 M3 model3 cr' gd sk ob LBX obj fba bb CATCH3 (fun Ma Mb => EXC3_agree Ma Mb obj LBX)).
    + eapply (TI_step LB _ S OPDEL_SCR []); [exact TI'| exact HP3| apply cgrows_nil; exact HP3| | exact LBR| unfold OPDEL_SCR, HEAP_STACK; lia| lia| lia| constructor].
      intros b Hb. rewrite !in_app_iff. tauto.
    + eapply (landed_step _ S OPDEL_SCR []); [exact STL| exact AVS| exact HP3| unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| constructor].
    + exact HH3.
    + eapply L5C.model_but_vm_trans; [exact MBV'| exact MBV3].
    + unfold TOPK in CK, CRK |- *. lia.
    + unfold TOPB in CB, CRB |- *. lia.
    + eapply str_at_kept; [exact AG3| apply APN| exact STR'].
    + eapply EXC3_agree; [| exact EXC]. intros b Hb.
      assert (IN : In b (LBX ++ (qx, 64) :: ostr ob ++ ostr sk ++ LB)) by (rewrite in_app_iff; left; exact Hb).
      assert (IN1 : In b (LBX ++ ostr ob ++ ostr sk ++ LB)) by (rewrite in_app_iff; left; exact Hb).
      destruct (WFB' b IN) as ([B1lo [B1 [B2 [B3 B4]]]] & _ & _). cbn [fst snd] in B1lo.
      destruct b as [q n]. cbn [fst snd] in *. eapply (blk_agree _ OPDEL_SCR [] M' M3 q n HP3 IN1); [lia| lia| apply APN].
    + destruct AOK' as [BA TBA]. split; [| exact TBA]. eapply big_kept; [exact AG3| lia| lia| apply APN| exact BA].
    + eapply obj_at_kept; [exact AG3| lia| lia| apply APN| exact OB'].
    + eapply cs_ok_call; [eapply cs_ok_of_eqv; exact REQ2| exact RP23].
    + rewrite (RP23 8%bv) by (cbn; tauto). greg REQ2 8. reflexivity.
    + rewrite (RP23 9%bv) by (cbn; tauto). greg REQ2 9. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ph_top : forall (fx : FPState) (R1 R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (gd fl : bool)
    (gr : growth) (LB2 : list (Z * Z)) (cr2 : credit) (VM1 : VmMaps),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S <= a < S + 240) -> m1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, S + 240 - 65536 <= a < S + 240 -> m1 (Z_to_bv 64 a) <> None) ->
  hi_heap HI LB cr m1 VM1 ->
  L5PS.e1_statics M0 gd fl av uid rnd canary hw ->
  cs_ok R S R1 -> getr R1 8%bv = wz len ->
  strinit_post L LB cr m1 M2 R1 R2 (S + 192) S (map bv_unsigned payload) gr LB2 cr2 ->
  model_but_vm model0 model2 -> hi_heap HI LB2 cr2 M2 (m_vmmaps model2) ->
  m_halted model2 = None -> m_vm_lazy model2 = [] -> m_vm_materialized model2 = [] ->
  len < 5000 ->
  srealizes rsegs SCFG (mkCfg (mkst R2 (Z_to_bv 64 0x205bc) M2 (seg_rom rsegs)) model2) K.
Proof.
  intros. eapply ph_small; try eassumption; intros sk0; [apply ph_pad1| apply ph_pad2| apply ph_pad3].
Qed.
End PHASES.

Theorem top_call_ok : lib_call_ok (TopLay L) SCFG HI (TopLS L).
Proof.
  intros fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm HK0 CONT.
  unfold lib_cfg in *. cbn [ll_heap ll_entry TopLay] in *. rewrite (ly_segs L LY) in *. change Plain.M.loaded_segments with rsegs in *.
  destruct PRE as [Rra RAok Rsp Rgp Rtp Ra0 Ra1 LEN PTR PAY STK CRED STAT]. cbn [ll_heap ll_stack ll_empty ll_credit ll_gp TopLay] in *.
  rewrite (ly_segs L LY) in *. rewrite (ly_tp L LY) in Rtp.
  destruct STK as (SP16 & SPLO & SPHI & SPTOP & STOK & SDEF).
  set (len := Z.of_nat (length payload)) in *.
  set (S := sp - 240).
  (* [comment removed for export] *)
  assert (ST0 : stk rsegs M (sp - 65536) sp).
  { apply TK.stk_of_defined; [| lia| lia| lia]. replace (sp - (sp - 65536)) with 65536 by lia. intros i Hi. apply SDEF. lia. }
  (* [comment removed for export] *)
  eapply (TK.srz_evt_canonMS _ R _ M model K Mh Ml).
  { unfold canon_regs. rewrite Rra, Rsp, Rtp, Ra0, Ra1.
    eapply (TS.s1 _ (Z_to_bv 64 sp)); rewrite ?L5.unsigned_lit by lia; [exact ST0| lia| lia]. }
  2:{ intros ms' (junk & m1 & -> & _). eexists _, _, _. reflexivity. }
  intros R1c pc1 m1 R1 (junk & m1' & E & FR1 & MU1 & WM1 & MG1 & ST1) REQ1.
  inversion E. subst R1c pc1 m1'. clear E.
  rewrite ?L5.unsigned_lit in FR1, MU1, ST1, REQ1 by lia.
  (* [comment removed for export] *)
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 240 <= a < sp) -> m1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU1. cbn. rewrite wa_unsigned by lia. split; [lia| exact I]. }
  assert (HH1 : hi_heap HI LB cr m1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M m1); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| pose proof (tly_sptop TLY_); lia| | exact MG1].
    intros a Ha. destruct (Z_lt_le_dec a (sp - 240)) as [Hlt|Hge]; [left; apply OUT1; lia|].
    destruct (Z_lt_le_dec a sp) as [Hlt'|Hge']; [right; left; lia| left; apply OUT1; lia]. }
  assert (DEF1 : forall a, sp - 65536 <= a < sp -> m1 (Z_to_bv 64 a) <> None).
  { intros a Ha. apply MG1. apply SDEF. exact Ha. }
  (* [comment removed for export] *)
  pose proof (hio_wf L SCFG HI HIok LB cr M _ HH) as [WF _].
  assert (PAYF : (length payload = 0%nat /\ ptr = 0x6f8d0) \/ (0 < len /\ In (ptr, len) LB /\ (4096 <= ptr /\ (ptr + len <= hl_img_lo L \/ hl_img_hi L <= ptr)) /\ ptr + len <= hl_ceil L /\ L5.defined M ptr len)).
  { destruct PTR as [[P0 P1]|[P0 P1]]; [left; auto| right]. destruct (WF _ P1) as ((B1lo & B1 & B2 & B3 & B4) & BD & _). cbn [fst snd] in B1lo. cbn [fst snd] in *.
    repeat split; try assumption; try lia. }
  assert (PAY1 : rdn rsegs m1 (Z_to_bv 64 ptr) (length payload) = Some payload).
  { rewrite <- PAY. pose proof (ly_img_hi L LY) as IH. apply (L5C.rdn_agree rsegs M m1 (length payload) ptr); subst len.
    - destruct PAYF as [[E0 E1]|(P0 & _ & P2 & P3 & _)]; [rewrite E1; lia| lia].
    - destruct PAYF as [[E0 E1]|(P0 & _ & P2 & P3 & _)]; [rewrite E0, E1; cbn; lia| lia].
    - intros i Hi. apply OUT1; destruct PAYF as [[E0 E1]|(P0 & _ & P2 & P3 & _)]; rewrite ?E0, ?E1 in Hi |- *; cbn in Hi; lia. }
  (* [comment removed for export] *)
  pose proof (tly_k TLY_) as K8. pose proof (tly_b TLY_) as BOV. pose proof (tly_sptop TLY_) as SPT0.
  destruct CRED as [CRK CRB]. cbn [fst snd] in CRK, CRB. unfold TOPK, TOPB in CRK, CRB.
  eapply (STRINIT fx R1 m1 model K LB cr (sp - 240 + 192) ptr (sp - 240) 0x205bc (map bv_unsigned payload)); rewrite ?length_map.
  - exact HH1.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK0.
  - greg REQ1 10. unfold wz. f_equal; lia.
  - greg REQ1 11. reflexivity.
  - greg REQ1 12. subst len. reflexivity.
  - subst len. lia.
  - apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. cbn. lia.
  - intros H23. split; [rewrite K8; lia|]. pose proof (TK.str_cap_bound len ltac:(lia)). subst len. lia.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. unfold wz. f_equal; lia.
  - greg REQ1 4. reflexivity.
  - (* [comment removed for export] *) split; [| split; [unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| split; [lia| split; [lia|]]]].
    { clear -SP16. Z.div_mod_to_equations. lia. }
    unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. apply DEF1. lia.
  - clear -SP16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - apply (L5C.writable_of_defined rsegs); [| lia| lia]. intros i Hi. apply DEF1. lia.
  - subst len. apply (L5C.rdn_bytes_at rsegs m1 payload ptr); [| | exact PAY1];
      destruct PAYF as [[E0 E1]|(P0 & _ & P2 & P3 & _)]; rewrite ?E0, ?E1; cbn [length Z.of_nat]; rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in *; lia.
  - subst len. destruct PAYF as [[E0 E1]|(P0 & _ & P2 & P3 & PD)]; [rewrite E0; intros i Hi; cbn in Hi; lia|].
    intros i Hi. apply MG1. apply PD. exact Hi.
  - subst len. destruct PAYF as [[E0 E1]|(P0 & P1 & P2 & P3 & _)]; [left; exact E0| right; left]. exists ptr, (Z.of_nat (length payload)). split; [exact P1| lia].
  - subst len. destruct PAYF as [[E0 E1]|(P0 & P1 & P2 & P3 & _)]; [rewrite E0, E1; cbn; lia| right; lia].
  - (* [comment removed for export] *)
    intros fx1 R2 M2 model2 gr LB2 cr2 [RP12 POSTg] MBV2 HH2. unfold L5CS.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV2) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV2) as Ml2. rewrite Ml in Ml2.
    pose proof (L5C.materialized_but_vm _ _ MBV2) as Mm2. rewrite Mm in Mm2.
    destruct (Z_le_gt_dec 5000 len) as [BIG|SMALL].
    + (* [comment removed for export] *)
      destruct gr as [|p cap].
      { exfalso. destruct POSTg as (L22 & _). rewrite length_map in L22. subst len. lia. }
      destruct POSTg as (L23 & Hcap & ELB2 & Ecr2 & FRESH & LSTR & HPRES). rewrite length_map in L23, Hcap.
      pose proof (L5C.fresh_block_bounds _ _ _ _ _ FRESH) as (PB1 & PB2 & PB3 & PB4). rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in PB1.
      pose proof (TK.str_cap_bound len ltac:(lia)) as CAPB. subst len. rewrite <- Hcap in CAPB.
      eapply (TK.srz_evt_canonMS _ R2 _ M2 model2 K Mh2 Ml2).
      { rewrite (TK.canon_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 R2 REQ1 RP12).
        apply (TS.s2_big (wz (sp - 240))); rewrite ?wz_unsigned by lia; lia. }
      2:{ intros ms' ->. eexists _, _, _. reflexivity. }
      intros R3c pc3 m3 R3 E REQ3. inversion E; subst R3c pc3 m3; clear E.
      (* [comment removed for export] *)
      destruct LSTR as (TB & U0 & U8 & U16 & BY & NUL). rewrite length_map in U8.
      assert (SR' : 0x7fff7f800000 <= bv_unsigned (wz (sp - 240)) /\ bv_unsigned (wz (sp - 240)) + 240 <= 2 ^ 47) by (rewrite wz_unsigned by lia; lia).
      eapply (TK.srz_evt_canonMS _ R3 _ M2 model2 K Mh2 Ml2).
      { rewrite (TK.canon_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R3 REQ3).
        eapply (TS.s16 (wz (sp - 240))) with (b0 := (cap + 1) mod 256) (w0 := cap + 1) (p := p); rewrite ?wz_unsigned by lia.
        - apply TK.ro_cells_u8; [| lia| lia]. replace (sp - 240 + 192) with (sp - 240 + 192) by lia. apply TK.u8_of_u64; [exact U0| lia].
        - pose proof (Z.mod_pos_bound (cap + 1) 256). lia.
        - intros _. split; [| split; [| lia]].
          + apply TK.ro_cells_u64; [exact U0| lia| lia].
          + replace (sp - 240 + 208) with (sp - 240 + 192 + 16) by lia. apply TK.ro_cells_u64; [exact U16| lia| lia]. }
      2:{ intros ms' (a0' & a1' & [[_ ->]|(_ & _ & _ & ->)]); eexists _, _, _; reflexivity. }
      intros R4c pc4 m4 R4 (a0' & a1' & CASES) REQ4.
      destruct CASES as [[TB0 E]|(TB1 & -> & -> & E)].
      { exfalso. change 256 with (2 ^ 8) in TB0. rewrite Z.mod_pow2_bits_low in TB0 by lia. rewrite TB in TB0. discriminate. }
      inversion E; subst R4c pc4 m4; clear E.
      (* [comment removed for export] *)
      hp_split HPRES KEPT2 SDEF2.
      eapply (OPDELS fx1 R4 M2 model2 K LB2 cr2 p cap (sp - 240) 0x2070c).
      * exact HH2.
      * split; [exact Mh2| split; [exact Ml2| exact Mm2]].
      * exact HK0.
      * rewrite ELB2. left. reflexivity.
      * greg REQ4 10. reflexivity.
      * greg REQ4 1. reflexivity.
      * split; [lia| reflexivity].
      * greg REQ4 2. unfold wz. f_equal; lia.
      * greg REQ4 4. reflexivity.
      * split; [clear -SP16; Z.div_mod_to_equations; lia|]. split; [unfold OPDEL_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
        eapply L5.defined_sub; [exact SDEF2| unfold OPDEL_SCR, STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia].
      * (* [comment removed for export] *)
        intros fx2 R5 M5 model5 RP45 HPRES5 MBV5 HH5. unfold L5CS.cfg.
        pose proof (L5C.halted_but_vm _ _ MBV5) as Mh5. rewrite Mh2 in Mh5.
        pose proof (L5C.lazy_but_vm _ _ MBV5) as Ml5. rewrite Ml2 in Ml5.
        replace (lb_remove p LB2) with LB in HPRES5, HH5 by (rewrite ELB2; cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
        hp_split HPRES5 KEPT5 SDEF5.
        (* [comment removed for export] *)
        assert (SAVED : ro_cells rsegs M5 (sp - 240 + 216) [C8 (getr R 9%bv); C8 (getr R 8%bv); C8 (Z_to_bv 64 ra)]).
        { pose proof (TK.ro_cells_skip1 _ _ _ _ (TK.ro_of_rw _ _ _ FR1)) as X. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in X.
          replace (sp - 240 + 216) with (sp - 240 + 216) in X by lia.
          eapply TK.ro_cells_agree; [eapply TK.ro_cells_agree; [exact X|]|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; unfold wa.
          - apply KEPT2. apply (L5C.kept_stack L); [unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia|].
            intros r [<-|[]]. unfold L5.in_rng. cbn. lia.
          - apply KEPT5. apply (L5C.kept_stack L); [unfold OPDEL_SCR, HEAP_STACK; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia|].
            intros r []. }
        eapply (TK.srz_evt_canonMS _ R5 _ M5 model5 K Mh5 Ml5).
        { rewrite (TK.canon_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R4 R5 REQ4 RP45).
          eapply (TS.s17 (wz (sp - 240))). rewrite wz_unsigned by lia. exact SAVED. }
        2:{ intros ms' ->. eexists _, _, _. reflexivity. }
        intros R6c pc6 m6 R6 E REQ6. inversion E; subst R6c pc6 m6; clear E.
        rewrite (TK.ret_pc_lit ra RAok).
        (* [comment removed for export] *)
        assert (FRAME : forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp 65536 a -> ~ in_errno L a -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha CA NE.
          assert (NS : ~ (sp - 240 <= a < sp)).
          { destruct CA as [(b & Hb & Hr)|[[A1 A2]|[A1 A2]]]; [| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in A1; lia].
            destruct (WF b Hb) as ((B1lo & B1 & _ & _ & B4) & _). cbn [fst snd] in B1lo. lia. }
          rewrite <- (OUT1 a Ha NS).
          assert (KA : forall scr W, 0 <= scr <= 65536 - 240 -> L5.outside W a -> L5C.kept L LB (sp - 240) scr W a).
          { intros scr W Hscr HW. split; [exact Ha|]. split; [| split; [exact NE| exact HW]].
            destruct CA as [IB|[[A1 A2]|IM]]; [left; exact IB| right; left; split; [exact A1| lia]| right; right; exact IM]. }
          rewrite <- (KEPT2 a). 2:{ apply KA; [unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia|]. intros r [<-|[]]. unfold L5.in_rng; cbn. lia. }
          apply KEPT5. apply KA; [unfold OPDEL_SCR, HEAP_STACK; lia| intros r []]. }
        (* [comment removed for export] *)
        assert (SCR : forall a, sp - 65536 <= a < sp -> M5 (Z_to_bv 64 a) <> None).
        { intros a Ha.
          destruct (Z_lt_le_dec a (sp - 240 - OPDEL_SCR)) as [B1|B1].
          - rewrite (KEPT5 a). 2:{ apply (L5C.kept_below L); [unfold OPDEL_SCR, HEAP_STACK in *; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia| intros r []]. }
            destruct (Z_lt_le_dec a (sp - 240 - STRINIT_SCR)) as [B2|B2].
            + rewrite (KEPT2 a). 2:{ apply (L5C.kept_below L); [unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in *; lia| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia|].
                                     intros r [<-|[]]. unfold L5.in_rng; cbn. unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in *. lia. }
              apply DEF1. lia.
            + eapply TK.defined_at; [exact SDEF2|]. unfold OPDEL_SCR, STRINIT_SCR, OPNEW_SCR, HEAP_STACK in *. lia.
          - destruct (Z_lt_le_dec a (sp - 240)) as [B2|B2].
            + eapply TK.defined_at; [exact SDEF5|]. lia.
            + rewrite (KEPT5 a). 2:{ apply (L5C.kept_stack L); [unfold OPDEL_SCR, HEAP_STACK in *; lia| unfold OPDEL_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia| intros r []]. }
              assert (KS : ~ (sp - 240 + 192 <= a < sp - 240 + 216) -> M2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
              { intros NI. apply KEPT2. apply (L5C.kept_stack L); [unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK in *; lia| unfold STRINIT_SCR, OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia|].
                intros r [<-|[]]. unfold L5.in_rng; cbn. lia. }
              destruct (Z_lt_le_dec a (sp - 240 + 192)) as [B3|B3]; [rewrite KS by lia; apply DEF1; lia|].
              destruct (Z_lt_le_dec a (sp - 240 + 216)) as [B4|B4]; [| rewrite KS by lia; apply DEF1; lia].
              (* [comment removed for export] *)
              destruct (Z_lt_le_dec a (sp - 240 + 200)) as [B5|B5].
              { eapply TK.defined_at; [eapply (TK.defined_of_rdn M2 _ 8); [exact U0| lia| lia| lia]| cbn; lia]. }
              destruct (Z_lt_le_dec a (sp - 240 + 208)) as [B6|B6].
              { eapply TK.defined_at; [eapply (TK.defined_of_rdn M2 _ 8); [exact U8| lia| lia| lia]| cbn; lia]. }
              eapply TK.defined_at; [eapply (TK.defined_of_rdn M2 _ 8); [exact U16| lia| lia| lia]| cbn; lia]. }
        (* [comment removed for export] *)
        eapply (CONT fx2 g R6 M5 model5 cr2); [| exact HH5| eapply L5C.model_but_vm_trans; [exact MBV2| exact MBV5]].
        constructor.
        -- greg REQ6 10. reflexivity.
        -- eapply (TK.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R6 REQ6); try reflexivity.
           ++ rewrite Rsp. unfold wz. f_equal. rewrite wz_unsigned by lia. lia.
           ++ rewrite Rtp. reflexivity.
        -- cbn [ll_credit TopLay fst snd credit_sub credit_le]. rewrite Ecr2. unfold debit, credit_le, credit_sub. cbn [fst snd].
           unfold TOPK, TOPB. rewrite K8. lia.
        -- cbn [ll_stack ll_heap TopLay]. intros a Ha CA NF NE. apply FRAME; assumption.
        -- cbn [ll_stack TopLay]. exact SCR.
        -- (* [comment removed for export] *)
           cbn [ls_ok TopLS]. destruct STAT as (av & uid & rnd & canary & hw & AVS & ST). exists av, uid, rnd, canary, hw. split; [exact AVS|].
           eapply e1_statics_agree; [exact ST|]. intros a Da. change Plain.M.loaded_segments with rsegs. apply FRAME.
           ++ unfold e1_dom in Da. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVhi & _). lia.
           ++ unfold e1_dom in Da. destruct (Z_lt_le_dec a 0x90730) as [Lo|Hi].
              ** right. right. rewrite (ly_img_lo L LY), (ly_img_hi L LY). split; [lia|]. intros X. apply (ly_static L LY) in X. lia.
              ** right. left. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVhi & _). lia.
           ++ unfold in_errno. rewrite (ly_errno L LY). unfold e1_dom in Da. destruct ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AVlo & _). lia.
    + (* [comment removed for export] *)
      cbn [ls_ok TopLS] in STAT. destruct STAT as (av & uid & rnd & canary & hw & AVS & STE).
      refine (ph_top R M m1 model K LB cr (sp - 240) ra payload junk av uid rnd canary hw _
                _ Rgp Rtp RAok _ _ (proj2 SPTOP) _ HK0 _ _ _ AVS FR1 Mh Ml Mm
                fx1 R1 R2 M2 model2 (fst g) (snd g) gr LB2 cr2 (m_vmmaps model) _ _ HH1 STE _ _ (conj RP12 POSTg) MBV2 HH2 Mh2 Ml2 Mm2 _).
      * intros fx' g' R' M' model' cr' LP HH' MBV'. replace (sp - 240 + 240) with sp in LP by lia. exact (CONT fx' g' R' M' model' cr' LP HH' MBV').
      * replace (sp - 240 + 240) with sp by lia. exact Rsp.
      * lia.
      * lia.
      * clear -SP16. Z.div_mod_to_equations. lia.
      * intros b Hb. destruct (WF b Hb) as ((B1lo & B1 & B2 & B3 & B4) & _). cbn [fst snd] in B1lo. lia.
      * cbn [fst]. unfold TOPK. lia.
      * cbn [snd]. unfold TOPB. subst len. lia.
      * intros a Ha Hn. apply OUT1; lia.
      * intros a Ha. apply DEF1. lia.
      * eapply cs_ok_of_eqv. exact REQ1.
      * greg REQ1 8. subst len. reflexivity.
      * subst len. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma img_cell : forall (M : word -> option byte) (a : Z) (n : nat) bs,
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn rsegs (fun _ => None) (Z_to_bv 64 a) n = Some bs -> rdn rsegs M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n bs CLR Ha Hn E. rewrite (L5C.rdn_agree rsegs (fun _ => None) M n a Ha Hn); [exact E|]. intros i Hi. apply CLR. exact Hi.
Qed.

Theorem top_statics_init : lib_statics_init (TopLay L) (TopLS L).
Proof.
  intros av uid rnd tid canary hw M IF. unfold lib_init_facts in IF.
  cbn [ll_heap ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp TopLay] in IF.
  rewrite (ly_segs L LY) in IF. change Plain.M.loaded_segments with rsegs in IF.
  destruct IF as (IMG & SELF & TID & TIDR & LOC & GL & CAN & GRD & CANR & AXP & AVS & AVH & AV8 & AW & UID & HW & RND1 & RND2).
  pose proof (tly_sptop TLY_) as SPT.
  assert (CLR : forall i, (0x10000 <= i < 0x5f870 \/ 0x6f8c5 <= i < 0x70368 \/ 0x90440 <= i < 0x90460) -> M (Z_to_bv 64 i) = None).
  { intros i [Hi|[Hi|Hi]]; [eapply (IMG (0x10000, 0x5f870))| eapply (IMG (0x6f8c5, 0x70368))| eapply (IMG (0x90440, 0x90460))]; cbn; auto; lia. }
  exists av, uid, rnd, canary, hw. split; [exact AVS|]. cbn [fst snd].
  unfold L5PS.e1_statics, L5PS.EH_CAUGHT, L5PS.EH_UNCAUGHT, L5PS.SYSCAT_GUARD, L5PS.UW_FLAGS, L5PS.TD_LOCALE, L5PS.GLOBAL_LOCALE,
    L5PS.LOCALE_MSGCAT, L5PS.CANARY, L5PS.AUXVP.
  repeat split; try lia.
  - apply (img_cell M 0x6f8f8 8); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x6f900 4); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x6fb20 1); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x6fb21 1); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x70361 1); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x70363 1); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - apply (img_cell M 0x70365 1); [intros i Hi; apply CLR; lia| lia| lia| vm_compute; reflexivity].
  - exact LOC.
  - exact (GL 5%nat ltac:(lia)).
  - exact GRD.
  - exact AXP.
  - intros j Hj. unfold L5.u64_at. rewrite (AW j ltac:(lia)). cbn [ll_phdr ll_phent ll_phnum TopLay auxv_words L5PS.auxv20].
    do 20 (destruct j as [|j]; [reflexivity|]). lia.
  - intros i Hi. apply CLR. lia.
  - intros i Hi. apply CLR. lia.
  - intros i Hi. apply CLR. lia.
Qed.

Theorem top_statics_frame : lib_statics_frame (TopLay L) (TopLS L).
Proof.
  intros g M M' LS FOOT RO INITC. cbn [ls_ok TopLS top_ls_ok ll_heap TopLay] in *.
  destruct LS as (av & uid & rnd & canary & hw & AVS & ST). exists av, uid, rnd, canary, hw. split; [exact AVS|].
  pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AV8 & AVlo & AVhi & _ & _ & _ & _ & _ & I1 & I2 & I3).
  eapply e1_statics_agree; [exact ST|]. intros a Da. unfold e1_dom in Da.
  destruct (Z_lt_le_dec a 0x5f668) as [A|A].
  { (* [comment removed for export] *)
    assert (E : M (Z_to_bv 64 a) = None).
    { destruct Da as [[D|[D|D]]|D]; [apply I1; lia| apply I2; lia| apply I3; lia| lia]. }
    rewrite E. apply RO; [rewrite L5.unsigned_lit by lia; cbn [ll_rw_lo TopLay]; lia| exact E]. }
  destruct (Z_lt_le_dec a 0x70367) as [B|B].
  { apply FOOT; [lia|]. unfold in_foot. cbn [ll_foot TopLay].
    destruct (Z_lt_le_dec a 0x6f908); [exists (0x6f8f8, 0x6f908); cbn; split; [auto| lia]|].
    destruct (Z_lt_le_dec a 0x6fb22); [exists (0x6fb20, 0x6fb22); cbn; split; [auto| lia]|].
    exists (0x70361, 0x70367); cbn; split; [auto 10| lia]. }
  apply INITC; [lia|]. unfold in_initc. cbn [ll_initc ll_heap TopLay].
  destruct (Z_lt_le_dec a av) as [C|C]; [left| right; lia].
  destruct (Z_lt_le_dec a 0x70438); [exists (0x70370, 0x70438); cbn; split; [auto| lia]|].
  destruct (Z_lt_le_dec a 0x906b0); [exists (0x906a8, 0x906b0); cbn; split; [auto| lia]|].
  destruct (Z_lt_le_dec a 0x906d8); [exists (0x906d0, 0x906d8); cbn; split; [auto 10| lia]|].
  exists (0x90700, 0x90730); cbn; split; [auto 10| lia].
Qed.

(* [comment removed for export] *)
Theorem top_iface_ok : lib_iface_ok (TopLay L) SCFG HI (TopLS L).
Proof. exact (LIOK _ _ _ _ top_call_ok top_statics_init top_statics_frame). Qed.

End TOP.
End SCFG_1.

End L5TOP.
