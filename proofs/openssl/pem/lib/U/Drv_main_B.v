(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Driver Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Exit Startup Stdio_iface Printf_lib Printf_stdio_iface Fz_iface Driver_iface Drv_kit Drv_facts Drv_main_defs Drv_main_A.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_walk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Exit_ax.     (* [comment removed for export] *)   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Drv_sys F_memcpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Str_cpy.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Ubsan.M.phdrs.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Lemma implM_unfold__ : forall {St A : Type} (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment)
  (c : @OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Monad.M St A) (s : St)
  (Q : A -> St -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state -> Prop) ms,
  OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Monad.implM segs c s Q ms ->
  OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ITree.impl segs (OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Nodes.at_node segs) (c s)
    (OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ITree.epost (fun p => Q (fst p) (snd p))) ms.
Proof. intros St A segs c s Q ms H. exact H. Qed.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition S_OOM : Z := 0x194ee.    Definition s_oom : list Z := (str "cli: out of memory"%string ++ [10])%list.
Definition S_SHORT : Z := 0x3631c.  Definition s_short : list Z := (str "cli: input shorter than header"%string ++ [10])%list.
Definition S_OVER : Z := 0x1bc4c.   Definition s_over : list Z := (str "cli: config_len overruns input"%string ++ [10])%list.
Lemma s_oom_ro : ro_bytes_b usegs S_OOM (to_bytes s_oom) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_short_ro : ro_bytes_b usegs S_SHORT (to_bytes s_short) = true. Proof. vm_compute. reflexivity. Qed.
Lemma s_over_ro : ro_bytes_b usegs S_OVER (to_bytes s_over) = true. Proof. vm_compute. reflexivity. Qed.

Lemma rodata_bytes : forall m A (s : list Z),
  mem_inv usegs m -> ro_bytes_b usegs A (to_bytes s) = true -> 0x10000 <= A -> A + zlength s <= 0x353000 ->
  bytes_at usegs m A (to_bytes s).
Proof.
  intros m A s MI RO LO HI. apply ro_bytes_at; [exact MI| lia| rewrite to_bytes_length; unfold zlength in HI; lia| apply (ro_bytes_b_sound usegs); exact RO].
Qed.

Lemma str_range : forall s, Forall (fun c => 0 <= c < 256) (str s).
Proof.
  intros s. unfold str. induction (list_ascii_of_string s) as [|a l IH]; cbn; constructor; [| exact IH].
  pose proof (Ascii.N_ascii_bounded a). lia.
Qed.
Lemma lit_range : forall s, Forall (fun c => 0 <= c < 256) (str s ++ [10]).
Proof. intros s. apply Forall_app. split; [apply str_range| constructor; [lia| constructor]]. Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

(* [comment removed for export] *)
Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
  impl usegs (at_node usegs) (enode n pl) (epost P) ms ->
  implM usegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
  intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
  eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells usegs m A [CB 0%nat []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma shiftr26_zero_iff : forall a, 0 <= a -> Z.shiftr a 26 = 0 <-> a < 67108864.
Proof.
  intros a Ha. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 26) with 67108864.
  split; intros H; [| apply Z.div_small; lia].
  destruct (Z.lt_ge_cases a 67108864) as [L|G]; [exact L|]. exfalso.
  pose proof (Z.div_le_mono 67108864 a 67108864 ltac:(lia) G) as M. rewrite Z.div_same in M by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_second : forall p b1 b2, blk_id b2 = p -> List.NoDup (map blk_id [b1; b2]) -> lb_remove p [b1; b2] = [b1].
Proof.
  intros p [[p1 A1] n1] [[p2 A2] n2] E ND. cbn [blk_id fst] in E. subst p2. cbn [map blk_id fst] in ND.
  inversion ND as [|x l NI _]; subst.
  unfold lb_remove. cbn.
  destruct (bptr_eqb p1 p) eqn:E1; cbn.
  - exfalso. apply bptr_eqb_eq in E1. subst p1. apply NI. left. reflexivity.
  - replace (bptr_eqb p p) with true by (symmetry; apply bptr_eqb_eq; reflexivity). cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CTXB.
  Variable CS : cli_sig.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis HT : 0 < TID < 4194304.

  Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling <= LO' /\ LO' + 8388608 = usp0 /\ 0x353000 <= LO'.
  Proof. destruct VSP as (A & B & C). unfold ceil_ok in CEIL. unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

  (* [comment removed for export] *)
  Definition EXTRA (mm : mem) (s : PState) : Prop :=
    stdout_file mm (ps_so s) /\ stderr_wfile0 mm /\ (exists fl, lx_flags mm fl)
    /\ (rw_cells usegs mm RINIT_FLAG [C1 (Z_to_bv 8 0)] /\ AXSTAT false mm)   (* [comment removed for export] *)
    /\ CLI0 CS mm.                                                            (* [comment removed for export] *)

  Definition extra_addr (a : Z) : Prop :=
    stdout_addr a \/ stderr_addr a \/ flags_addr a \/ (RINIT_FLAG <= a < RINIT_FLAG + 1) \/ axstat_addr a \/ rin_ivs LXW_CLIENT a.

  Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
    agree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
  Proof.
    intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
    exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
    eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. unfold file_cells in Ha. cbn in Ha. lia.
  Qed.

  Lemma EXTRA_agree : forall (P : Z -> Prop) m m' s s',
    agree_on P m m' -> (forall a, extra_addr a -> P a) -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros P m m' s s' AG HP ESO (X1 & X2 & [fl X3] & [X4 XA] & X5). unfold EXTRA. rewrite ESO.
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; left; exact Ha| exact X1]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; right; left; exact Ha| exact X2]|].
    split; [exists fl; eapply lx_flags_agree; [exact AG| intros a Ha; apply HP; right; right; left; exact Ha| exact X3]|].
    split. { split; [eapply rw_cells_agree; [exact AG| exact X4|]; intros a Ha; apply HP; right; right; right; left; cbn in Ha; lia|].
             eapply AXSTAT_agree; [exact AG| | exact XA]. intros a Ha. apply HP. right; right; right; right; left. exact Ha. }   (* [comment removed for export] *)
    eapply (cli0_stable CS); [exact X5|]. intros a Ha Hw. apply AG; [exact Ha|]. apply HP. right; right; right; right; right. exact Hw.
  Qed.

  Lemma ESTAT_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, estat_addr a -> P a) -> ESTAT TID m -> ESTAT TID m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & (ij0 & ij1 & ij2 & ij3 & ij4 & A13) & A14). unfold ESTAT, RGOT_LLVMINIT, RDSO in *.
    Ltac tre AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold estat_addr; cbn in Ha; lia].
    split; [tre AG HP A1|]. split; [tre AG HP A2|]. split; [tre AG HP A3|]. split; [tre AG HP A4|].
    split; [tre AG HP A5|]. split; [tre AG HP A6|]. split; [tre AG HP A7|]. split; [tre AG HP A8|].
    split; [tre AG HP A9|]. split; [tre AG HP A10|]. split; [tre AG HP A11|]. split; [tre AG HP A12|].
    split; [exists ij0, ij1, ij2, ij3, ij4; tre AG HP A13|]. tre AG HP A14.
  Qed.

  (* [comment removed for export] *)
  Definition base_addr (a : Z) : Prop := estat_addr a \/ lxs_addr a \/ usp0 <= a.

  (* [comment removed for export] *)
  Lemma BASE_heap : forall LB m m' s' LB', BASE' m -> rheap_pres LB (usp0 + -128) m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> RHEAP s' LB' m' -> BASE' m'.
  Proof.
    intros LB m m' s' LB' (ST & MI & ES & AUX & SSP & LXS & IMG) HP MI' ST' AUX' HP'.
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    split; [exact ST'|]. split; [exact MI'|].
    split. { eapply ESTAT_agree; [exact AG| | exact ES]. intros a Ha. right; left.
             unfold estat_addr, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    split; [exact AUX'|]. split; [exact (RHEAP_ssp _ _ _ HP')|].
    split. { eapply lx_statics_agree; [exact AG| | exact LXS]. intros a Ha. right; left.
             unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia. }
    eapply bytes_at_agree; [exact AG| exact IMG| intros a Ha; left; lia].
  Qed.

  Lemma EXTRA_heap : forall LB m m' s s', rheap_pres LB (usp0 + -128) m m' -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros LB m m' s s' HP ESO. apply (EXTRA_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)); [| exact ESO].
    intros a Ha. right; left.
    unfold extra_addr, stdout_addr, stderr_addr, flags_addr, axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, LX_FLAGS, RINIT_FLAG, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP,
      LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in *. cbn [rin_ivs fst snd] in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition WOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RMallocRep.RERRNO /\ snd iv = RMallocRep.RERRNO + 4)
    \/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x353000 <= fst iv))
    \/ (fst iv = RSTAGE /\ RSTAGE <= snd iv <= RSTAGE + 65536).
  Definition WOKE (iv : Z * Z) : Prop := WOK iv \/ (fst iv = RSTDERR /\ snd iv = RSTDERR + 232).

  Lemma WOK_WOKE : forall W, Forall WOK W -> Forall WOKE W.
  Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv Hiv. left. exact Hiv. Qed.

  Lemma WOKE_outside : forall W a, Forall WOKE W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x353000 /\ ~ (RMallocRep.RERRNO <= a < RMallocRep.RERRNO + 4) /\ ~ (RSTDERR <= a < RSTDERR + 232)
                          /\ ~ (RSTAGE <= a < RSTAGE + 65536))) -> outside W a.
  Proof.
    pose proof sp_facts as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOKE, WOK, LO, RMallocRep.RERRNO in H1. cbn [fst snd] in H1. unfold RMallocRep.RERRNO in Ha. lia.
  Qed.

  Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x353000 /\ ~ (RMallocRep.RERRNO <= a < RMallocRep.RERRNO + 4) /\ ~ (RSTAGE <= a < RSTAGE + 65536))) -> outside W a.
  Proof.
    pose proof sp_facts as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOK, LO, RMallocRep.RERRNO in H1. cbn [fst snd] in H1. unfold RMallocRep.RERRNO in Ha. lia.
  Qed.

  Lemma BASE_munch : forall W m m', BASE' m -> Forall WOKE W -> munch W m m' -> wmono usegs m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> BASE' m'.
  Proof.
    intros W m m' (ST & MI & ES & AUX & SSP & LXS & IMG) HW MU WM MI' ST'. pose proof sp_facts as SF. unfold LO in *.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split; [exact ST'|]. split; [exact MI'|].
    split; [eapply ESTAT_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold estat_addr, RMallocRep.RERRNO in *; lia]| exact ES]|].
    split.
    { eapply rauxv_ok_agree; [exact AG| | | exact AUX]; intros a Ha; apply WOKE_outside; [exact HW| left; lia| exact HW|].
      unfold RAUXV_CELL, RMallocRep.RERRNO in *. lia. }
    split; [eapply ssp_cells_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold ssp_addr, got_ssp, ssp_guard, RMallocRep.RERRNO in *; lia]| exact SSP]|].
    split; [eapply lx_statics_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN, LX_DEBUG_STRICT, RMallocRep.RERRNO in *; lia]| exact LXS]|].
    eapply bytes_at_agree; [exact AG| exact IMG|]. intros a Ha. apply WOKE_outside; [exact HW| left; lia].
  Qed.

  Lemma EXTRA_munch : forall W m m' s s', Forall WOK W -> munch W m m' -> wmono usegs m m' -> ps_so s' = ps_so s -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros W m m' s s' HW MU WM ESO. apply (EXTRA_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)); [| exact ESO].
    intros a Ha. apply WOK_outside; [exact HW|].
    unfold extra_addr, stdout_addr, stderr_addr, flags_addr, axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, LX_FLAGS, RINIT_FLAG, RMallocRep.RERRNO, LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in *. cbn [rin_ivs fst snd] in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma AXSTAT_munchW : forall W m m' k, Forall WOKE W -> munch W m m' -> wmono usegs m m' -> AXSTAT k m -> AXSTAT k m'.
  Proof.
    intros W m m' k HW MU WM AX. eapply AXSTAT_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact AX].
    intros a Ha. apply WOKE_outside; [exact HW|]. unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, RMallocRep.RERRNO in *. lia.
  Qed.
  Lemma AXSTAT_heap : forall LB m m' k, rheap_pres LB (usp0 + -128) m m' -> AXSTAT k m -> AXSTAT k m'.
  Proof.
    intros LB m m' k HP AX. eapply AXSTAT_agree; [exact (agree_of_heap_pres _ _ _ _ HP)| | exact AX].
    intros a Ha. right; left.
    unfold axstat_addr, RAEF_INCB, RATEXIT, RATEXIT_A0, ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma EXTRA_stdio : forall W m m' s s', Forall WOKE W -> munch W m m' -> wmono usegs m m' -> ps_so s' = ps_so s ->
    stderr_wfile0 m' -> EXTRA m s -> EXTRA m' s'.
  Proof.
    intros W m m' s s' HW MU WM ESO SE' (X1 & X2 & [fl X3] & [X4 XA] & X5). pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    unfold EXTRA. rewrite ESO.
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold stdout_addr, RMallocRep.RERRNO in *; lia]| exact X1]|].
    split; [exact SE'|].
    split; [exists fl; eapply lx_flags_agree; [exact AG| intros a Ha; apply WOKE_outside; [exact HW| unfold flags_addr, LX_FLAGS, RMallocRep.RERRNO in *; lia]| exact X3]|].
    split. { split; [eapply rw_cells_agree; [exact AG| exact X4|]; intros a Ha; apply WOKE_outside; [exact HW|]; unfold RINIT_FLAG, RMallocRep.RERRNO in *; cbn in Ha; lia|].
             eapply (AXSTAT_munchW W); [exact HW| exact MU| exact WM| exact XA]. }   (* [comment removed for export] *)
    eapply (cli0_stable CS); [exact X5|]. intros a Ha Hw. apply AG; [exact Ha|]. apply WOKE_outside; [exact HW|].
    unfold RMallocRep.RERRNO, LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in *. cbn [rin_ivs fst snd] in Hw. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bie_munch : forall W m m' s, Forall WOKE W -> munch W m m' -> wmono usegs m m' -> EXTRA m s ->
    exists bi : byte, rw_cells usegs m' 0x32de20 [C1 bi].
  Proof.
    intros W m m' s HW MU WM (_ & _ & _ & _ & X5). apply (cli0_exit CS). eapply (cli0_stable CS); [exact X5|].
    intros a Ha Hw. apply (agree_on_of_munch _ _ _ MU WM); [exact Ha|]. apply WOKE_outside; [exact HW|].
    unfold RMallocRep.RERRNO, LXW_CLIENT, LXW_BASEINIT, LXW_LIBCRYPTO, LXW_PSELF, LXW_PKEYS, LXW_MREPL, LXW_DKEY in *. cbn [rin_ivs fst snd] in Hw. lia.
  Qed.
  Lemma bie_extra : forall m s, EXTRA m s -> exists bi : byte, rw_cells usegs m 0x32de20 [C1 bi].
  Proof. intros m s (_ & _ & _ & _ & X5). exact (cli0_exit CS m X5). Qed.

  Lemma RHEAP_munchW : forall s LB W m m', Forall WOKE W -> munch W m m' -> wmono usegs m m' ->
    (forall iv, In iv W -> snd iv <= alloc_ceiling -> (snd iv <= 0x10000 \/ 0x353000 <= fst iv) ->
                exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
    RHEAP s LB m -> RHEAP s LB m'.
  Proof.
    intros s LB W m m' HW MU WM HB HP. pose proof sp_facts as SF. unfold LO in *.
    eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    apply Forall_forall. intros [lo1 hi1] Hin. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as H.
    unfold WOKE, WOK, rclient_write_ok, RMallocRep.RERRNO, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, LO in *. cbn [fst snd] in *.
    destruct H as [[H|[H|[H|H]]]|H]; [left; lia| right; left; lia| right; right| right; left; lia| right; left; lia]. apply (HB (lo1, hi1)); [exact Hin| cbn; lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma MFRAME_heap : forall LB m m' pd a b c d, rheap_pres LB (usp0 + -128) m m' -> MFRAME sp0 argv m pd a b c d -> MFRAME sp0 argv m' pd a b c d.
  Proof. intros LB m m' pd a b c d HP FR. unfold MFRAME in *. eapply rheap_pres_rw_cells; [exact HP| exact FR| left; cbn; lia]. Qed.
  Lemma MFRAME_munch : forall W m m' pd a b c d, Forall WOKE W -> munch W m m' -> wmono usegs m m' -> MFRAME sp0 argv m pd a b c d -> MFRAME sp0 argv m' pd a b c d.
  Proof.
    intros W m m' pd a b c d HW MU WM FR. unfold MFRAME in *. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact FR|].
    intros x Hx. cbn in Hx. apply WOKE_outside; [exact HW| left; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma at_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo SP -> lo <= SP - 176 -> 0x353000 <= lo -> 0 <= SP < 2^64 ->
    ESTAT TID m -> (exists bi : byte, rw_cells usegs m 0x32de20 [C1 bi]) -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv usegs m ->
    forall k : bool, AXSTAT k m ->                                                     (* [comment removed for export] *)
    at_exit ps_so code s (MS (mkR ra (wz SP) (wz 0x10800) (wz RATP) t0 t1 t2 s0 s1 (wz code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (wz 0x2b06f8) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros ST LOS LOLO SPR (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) BIE HP SOF SEF MI k AX.
    destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC).
    pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
    unfold at_exit. cbv delta [MallocRep.wz] in *.
    do 31 eexists. exists F, fc, m, lo, TID, (Z_to_bv 64 0x3308a0), (Z_to_bv 64 0x3308a0), (Z_to_bv 64 0x3308a0), (Z_to_bv 64 0), rr_guard.
    exists cdt, thr, sec, tm1, k.
    split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact BIE|]. split; [exact E12|].
    split; [exact E5|]. split; [exact E6|]. split; [exact LC|]. split; [exact E7|]. split; [exact E8|]. split; [exact E13|]. split; [exact E9|]. split; [exact E10|].
    split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. split; [exact AX| exact E14].
  Qed.
End CTXB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section B.
  Variable CS : cli_sig.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (arg0 arg1 : list byte) (TID : Z) (PAD : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : ceil_ok sp0.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis EARGV : argv = [arg0; arg1].
  Hypothesis HT : 0 < TID < 4194304.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Hypothesis FWR : @fwrite_diag_stmt PState.

  Notation usp0 := (bv_unsigned sp0).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid TID).
  Notation EXTRA' := (EXTRA CS).
  Notation FRAME' mm := (MFRAME sp0 argv mm PAD S7 S6 S5 S4).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid run_hw run_draw).

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma IMGB_bound : usp0 + Z.of_nat (length IMGB) <= 2^64.
  Proof.
    pose proof (build_stack_bytes_length pph sp0 argv envp uid run_hw run_draw) as BL. pose proof (raw_len_nonneg pph sp0 argv envp uid run_hw run_draw) as RLN.
    destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *.
    destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _).
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    unfold raw_len, struct_size, argc, envc, total_arg_bytes, pad_len in *. rewrite BL.
    unfold raw_len, struct_size, argc, envc. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    stk usegs mm LO' (usp0 + -128) ->
    ESTAT TID mm -> (exists bi : byte, rw_cells usegs mm 0x32de20 [C1 bi]) -> RHEAP s LB mm -> stdout_file mm (ps_so s) -> stderr_file mm -> mem_inv usegs mm ->
    forall k : bool, AXSTAT k mm ->                                                    (* [comment removed for export] *)
    evt usegs (at_exit ps_so 2 s) (GST 0xe1878 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros ST ES BIE HP SOF SEF MI k AX. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    zstep. zstep.
    replace (ret_pc (Z_to_bv 64 0xe1884)) with (Z_to_bv 64 0xe1884) by (symmetry; rpc).
    apply evt_done. eapply (at_exit_intro TID HT 2 s LB); [exact ST| lia| lia| lia| exact ES| exact BIE| exact HP| exact SOF| exact SEF| exact MI| exact AX].
  Qed.

  (* [comment removed for export] *)
  Lemma fprintf_exit : forall (d : diag_msg) {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 (a1v a2v : word) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    diag_args d mm a1v a2v LO' (usp0 + -128) ->
    BASE' mm -> RHEAP s LB mm -> EXTRA' mm s -> frm0 fc ->
    (forall ms', at_exit ps_so 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag d ;;; K) s Q
      (GST 0xe1848 x1 t0 t1 t2 x9 (Z_to_bv 64 RSTDERR) a1v a2v x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros DA BA HP EX FRM HK.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    pose proof EX as (SOF & SE & FL & IB & CL0).
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s Q msx) end.
    eapply implM_bind.
    { eapply (FPR d) with (lo := usp0 - 8388608) (canary := rr_guard);
        [exact FWX| exact SWF| apply stderr_wfile0_wfile; exact SE| reflexivity
        | rewrite unsigned_lit by lia; unfold LO in DA; exact DA
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | exact SSP| exact MI| exact FRM]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0xe1850)) with (Z_to_bv 64 0xe1850) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 8388608, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (HP2 : RHEAP s LB m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact HP].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (SOF2 : stdout_file m2 (ps_so s)).
    { eapply stdout_file_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact SOF]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold stdout_addr, RMallocRep.RERRNO in *. lia. }
    pose proof BA2 as (ST3 & MI3 & ES3 & _).
    assert (AX2 : AXSTAT false m2) by (destruct IB as [_ AX0]; eapply (AXSTAT_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact AX0]).
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    zstep.
    eapply (exit2_tail s LB); [exact ST3| exact ES3| exact (bie_munch CS sp0 VSP CEIL _ _ _ _ WOKW MUc WMc EX)| exact HP2| exact SOF2| apply stderr_wfile_file; exact SEW| exact MI3| exact AX2].
  Qed.

  (* [comment removed for export] *)
  Lemma fwrite_exit : forall {R} (K : M PState R) (Q : R -> PState -> machine_state -> Prop) (s : PState) (LB : list block)
      x1 t0 t1 t2 x9 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem),
    BASE' mm -> RHEAP s LB mm -> EXTRA' mm s ->
    (forall ms', at_exit ps_so 2 s ms' -> implM usegs K s Q ms') ->
    implM usegs (s_diag DOom ;;; K) s Q
      (GST 0xe1870 x1 t0 t1 t2 x9 (Z_to_bv 64 S_OOM) (Z_to_bv 64 19) (Z_to_bv 64 1) (Z_to_bv 64 RSTDERR) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until mm. intros BA HP EX HK.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    pose proof EX as (SOF & SE & FL & IB & CL0).
    unfold implM. iprefix. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s Q msx) end.
    cbn [s_diag]. change (concat pieces_oom) with s_oom.
    eapply implM_bind.
    { eapply (FWR) with (lo := usp0 - 8388608) (canary := rr_guard) (s := s_oom);
        [exact SE
        | rewrite unsigned_lit by (unfold S_OOM; lia); change (map _ s_oom) with (to_bytes s_oom); apply rodata_bytes; [exact MI| apply s_oom_ro| unfold S_OOM; lia| unfold S_OOM, s_oom, zlength; cbn; lia]
        | apply lit_range
        | unfold s_oom, zlength; cbn; lia| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | rewrite !unsigned_lit by (unfold S_OOM; lia); unfold S_OOM, s_oom, zlength; cbn; lia
        | exact SSP| exact MI]. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0xe1878)) with (Z_to_bv 64 0xe1878) by (symmetry; rpc).
    assert (WOKW : Forall (WOKE sp0) [(usp0 - 8388608, usp0 + -128); (RSTDERR, RSTDERR + 232)]).
    { unfold WOKE, WOK, LO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (HP2 : RHEAP s LB m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| | exact HP].
      intros iv [<-|[<-|[]]]; cbn [fst snd]; intros H1 H2; lia. }
    assert (SOF2 : stdout_file m2 (ps_so s)).
    { eapply stdout_file_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| | exact SOF]. intros a Ha. apply (WOKE_outside sp0 VSP CEIL); [exact WOKW|]. unfold stdout_addr, RMallocRep.RERRNO in *. lia. }
    pose proof BA2 as (ST3 & MI3 & ES3 & _).
    assert (AX2 : AXSTAT false m2) by (destruct IB as [_ AX0]; eapply (AXSTAT_munchW sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| exact AX0]).
    eapply implM_evt; [| intros ms'' H; apply HK; exact H].
    eapply (exit2_tail s LB); [exact ST3| exact ES3| exact (bie_munch CS sp0 VSP CEIL _ _ _ _ WOKW MUc WMc EX)| exact HP2| exact SOF2| apply stderr_wfile0_file; exact SEW| exact MI3| exact AX2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition BUF (mm : mem) (s : PState) (bufp : bptr) (A cap : Z) (DATA junk : list byte) : Prop :=
    RHEAP s [(bufp, A, cap)] mm /\ A = ptr_addr s bufp
    /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
    /\ (65536 <= cap <= MAX_INPUT /\ exists k, 0 <= k /\ cap = 2 ^ k) /\ Z.of_nat (length DATA) <= cap /\ rblock_range A cap.

  (* [comment removed for export] *)
  Definition STG (mm : mem) : Prop := stk usegs mm RSTAGE (RSTAGE + 65536).

  Lemma STG_heap : forall LB mm mm', rheap_pres LB (usp0 + -128) mm mm' -> STG mm -> STG mm'.
  Proof.
    intros LB mm mm' HP SG. unfold STG in *. eapply stk_agree; [eapply agree_of_heap_pres; exact HP| exact SG|].
    intros a Ha. right; left.
    unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RERRNO, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
  Qed.

  Lemma STG_munch : forall W mm mm', munch W mm mm' -> wmono usegs mm mm' ->
    (forall a, RSTAGE <= a < RSTAGE + 65536 -> outside W a) -> STG mm -> STG mm'.
  Proof.
    intros W mm mm' MU WM HO SG. unfold STG in *. eapply stk_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact SG| exact HO].
  Qed.

  (* [comment removed for export] *)
  Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
    (GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).

  (* [comment removed for export] *)
  Definition RDHEAD (fd P1v : Z) (st : rd_st) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0xe1650 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength (rd_content st)) fd (rd_cap st) (Z_to_bv 64 A) t3 t4 t5 t6 F fc mm
      /\ rd_content st = map bv_unsigned DATA
      /\ BUF mm s (rd_buf st) A (rd_cap st) DATA junk /\ STG mm
      /\ FRAME' mm /\ BASE' mm /\ EXTRA' mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  (* [comment removed for export] *)
  Definition RDBRK (fd P1v : Z) (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap : Z) (DATA junk : list byte) (errv : word),
      ms = RST 0xe16cc x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
      /\ content = map bv_unsigned DATA
      /\ BUF mm s bufp A cap DATA junk /\ STG mm
      /\ FRAME' mm /\ BASE' mm /\ EXTRA' mm s /\ rw_cells usegs mm RMallocRep.RERRNO [C4 errv] /\ frm0 fc.

  Definition POSTBODY (fd P1v : Z) (r : rd_st + rd_result) (s : PState) (ms : machine_state) : Prop :=
    match r with
    | inl st' => RDHEAD fd P1v st' s ms
    | inr RdExit => at_exit ps_so 2 s ms
    | inr (RdDone b c) => RDBRK fd P1v b c s ms
    end.

  (* [comment removed for export] *)
  Definition rd_read_part (fd : Z) (path : list Z) (len : Z) (st1 : rd_st (ptr:=bptr)) : M PState (rd_st + rd_result) :=
    s <- mget ;;
    let buf := ustage in
    let cnt := Z.min (rd_cap st1 - len) 65536 in
    a <- msys (NRead fd buf cnt) (dec_read buf cnt) ;;
    match a with
    | RdErr _ => io_diag io (DReadError path) ;;; mret (inr RdExit)
    | RdData bs =>
        if (length bs =? 0)%nat then mret (inr (RdDone (rd_buf st1) (rd_content st1)))
        else mret (inl (mkRd (rd_buf st1) (rd_cap st1) (rd_content st1 ++ u8s_of_bytes bs)))
    end.

  Definition rd_grow_part (st : rd_st) : M PState (option rd_st) :=
    if zlength (rd_content st) =? rd_cap st then
      if MAX_INPUT <=? rd_cap st then io_diag io DTooBig ;;; mret None
      else
        nb <- raw_malloc (rd_cap st * 2) ;;
        match nb with
        | None => io_diag io DOom ;;; mret None
        | Some nb' => raw_free (rd_buf st) ;;; mret (Some (mkRd nb' (rd_cap st * 2) (rd_content st)))
        end
    else mret (Some st).

  Lemma read_loop_body_eq : forall fd path st,
    read_loop_body io raw_malloc raw_free ustage fd path st
    = (g <- rd_grow_part st ;; match g with None => mret (inr RdExit) | Some st1 => rd_read_part fd path (zlength (rd_content st)) st1 end).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk : list byte) (errv : word),
    3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
    rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> Z.of_nat (length DATA) < rd_cap st1 ->
    STG mm ->
    FRAME' mm -> BASE' mm -> EXTRA' mm s -> rw_cells usegs mm RMallocRep.RERRNO [C4 errv] -> frm0 fc ->
    implM usegs (rd_read_part fd (map bv_unsigned arg1) (zlength (rd_content st1)) st1) s (POSTBODY fd P1v)
      (GST 0xe16a0 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).
  Proof.
    intros until errv. intros FD HP1 HC BU LT SG FR BA EX ERR FRM.
    pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in SF. try (pose proof alloc_ceiling_range as CEIL_RANGE).
    destruct BU as (P0 & HA & BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). 
    pose proof BA as (ST & MI & ES & AUX & SSP & LXS & IMG). unfold LO in ST.
    assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
    rewrite LENZ. unfold MAX_INPUT in CAPR.
    unfold rd_read_part. apply implM_get_bind. cbv beta zeta.
    unfold MFRAME in FR. unfold RMallocRep.RERRNO in ERR. unfold STG in SG.
    set (LEN := Z.of_nat (length DATA)) in *. set (CNT := Z.min (rd_cap st1 - LEN) 65536).
    assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. assert (ECNT : CNT = Z.min (rd_cap st1 - LEN) 65536) by reflexivity. clearbody LEN CNT.
    assert (LEN0 : 0 <= LEN) by lia. assert (CNT1 : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - LEN) by lia.
    (* [comment removed for export] *)
    eapply (implM_evt usegs) with (P := fun ms1 => ms1 = GST 0xe16b0 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 RSTAGE) x23 t3 t4 t5 t6 F fc mm).
    { zstep. zstep. zstep. if_cases K; zify_cond K.
      - apply evt_done. replace CNT with (rd_cap st1 - LEN) by lia. replace (rd_cap st1 + - LEN) with (rd_cap st1 - LEN) by lia. reflexivity.
      - zstep. apply evt_done. replace CNT with 65536 by lia. reflexivity. }
    cbv beta. intros ms1 ->.
    unfold implM. iprefix. zstep. zstep. zstep.
    (* [comment removed for export] *)
    destruct (stk_split usegs mm RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SG ltac:(lia)) as [SGlo REST].
    destruct (stk_carve usegs mm RSTAGE (RSTAGE + CNT) (Z.to_nat CNT) SGlo ltac:(lia)) as [_ [sjk DST]].
    replace (RSTAGE + CNT - Z.of_nat (Z.to_nat CNT)) with RSTAGE in DST by lia. clear SGlo.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
    eapply implM_bind.
    { set (w1 := Z_to_bv 64 RSTAGE). unfold ustage. replace RSTAGE with (bv_unsigned w1) by (subst w1; rewrite unsigned_lit; lia).
      eapply implM_of_enode.
      eapply Drv_sys.read_spec with (lo := usp0 - 8388608) (junk := sjk) (errv := errv); subst w1; unfold RATP;
        rewrite ?(unsigned_lit RMallocRep.RATP) by (unfold RMallocRep.RATP; lia); rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit RSTAGE) by lia; try reflexivity;
        unfold RMallocRep.RATP; cbn [Z.add];
        first [exact ST | exact DST | exact ERR | exact MI | lia]. }
    cbv beta. intros a s' ms' [PO ->].
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
    unfold RATP in MUc, RES. rewrite ?(unsigned_lit RMallocRep.RATP) in MUc, RES by (unfold RMallocRep.RATP; lia).
    rewrite !(unsigned_lit (usp0 + -128)) in MUc by lia. rewrite !(unsigned_lit RSTAGE) in MUc by lia.
    rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit RSTAGE) in RES by lia.
    unfold RMallocRep.RATP in MUc, RES. cbn [Z.add] in MUc, RES.
    replace (ret_pc (Z_to_bv 64 0xe16c0)) with (Z_to_bv 64 0xe16c0) by (symmetry; rpc).
    assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (RSTAGE, RSTAGE + Z.of_nat (Z.to_nat CNT)); (3344580, 3344580 + 4)]).
    { unfold WOK, LO, RMallocRep.RERRNO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
    { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| | exact P0].
      intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; intros Hiv Hiv2; lia. }
    assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA| apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; exact ST2]).
    assert (EX2 : EXTRA' m2 s) by (eapply (EXTRA_munch CS sp0 VSP CEIL); [exact WOKW| exact MUc| exact WMc| reflexivity| exact EX]).
    assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKW| exact MUc| exact WMc| exact FR]).
    assert (REST2 : stk usegs m2 (RSTAGE + CNT) (RSTAGE + 65536)).
    { eapply stk_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact REST|]. intros x Hx. cbn. lia. }
    assert (BLK2 : rw_cells usegs m2 A [CB (length DATA) DATA; CB (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA))) junk]).
    { rewrite <- ELEN. eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUc| exact WMc]| exact BLK|]. intros x Hx. cbn in Hx |- *. lia. }
    clear MUc WMc BA WOKW REST DST BLK SG. 
    destruct a as [e|bs]; cbn [Drv_sys.read_ret] in *.
    - (* [comment removed for export] *)
      destruct RES as (DST2 & ERR2 & He).
      pose proof BA2 as (ST3 & MI3 & ES3 & AUX3 & SSP3 & LXS3 & IMG3). unfold LO in ST3.
      pose proof LXS3 as (G1 & G2 & _).
      pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
      destruct (argv_cstring sp0 argv envp uid m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
        as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
      pose proof IMGB_bound as IL.
      rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
      assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
      assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
      unfold implM. iprefix.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in G1, G2. cbv delta [MallocRep.wz] in G1, G2.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
      cbn [io_diag io io_S].
      eapply (fprintf_exit (DReadError (map bv_unsigned arg1)));
        [| exact BA2| exact P2| exact EX2| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
      cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
      rewrite zb_map_unsigned. unfold zlength. rewrite !length_map.
      split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
      split; [lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
    - destruct RES as (DST2 & ERR2 & Hbs).
      unfold implM. iprefix.
      zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNT1 LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
        assert (LBS : (1 <= length bs)%nat) by (destruct bs; [exfalso; apply K1; reflexivity| cbn; lia]).
        (* [comment removed for export] *)
        pose proof DST2 as SRC. apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SRC. destruct SRC as [SRC STG2b].
        pose proof (rw_cells_bytes_at _ _ _ _ SRC) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
        pose proof BLK2 as BLKx. rewrite <- ELEN in BLKx. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKx. destruct BLKx as [BLK1 BLKj].
        cbn [cells_size csize Nat.add] in BLKj. replace (length DATA + 0)%nat with (length DATA) in BLKj by lia.
        destruct (Str_cpy.rw_cells_CB_split_at usegs m2 (A + Z.of_nat (length DATA)) (Z.to_nat (rd_cap st1 - LEN)) junk (length bs) ltac:(lia) BLKj) as [DSTB RESTB].
        replace (A + Z.of_nat (length DATA)) with (A + LEN) in DSTB, RESTB by lia.
        zstep. zstep. zstep. zstep.
        eapply evt_cut.
        { eapply (F_memcpy.memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 bs (firstn (length bs) junk));
            rewrite ?unsigned_lit by lia;
            [exact SRCB| lia| replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; exact DSTB| lia| exact MI2]. }
        cbv beta. intros ms' PO.
        destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI3 & DSTB' & _).
        rewrite !unsigned_lit in MUd by lia. rewrite !unsigned_lit in DSTB' by lia.
        replace (ret_pc (Z_to_bv 64 0xe1648)) with (Z_to_bv 64 0xe1648) by (symmetry; rpc).
        assert (WOKV : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
        { unfold WOK. constructor; [cbn [fst snd]; lia| constructor]. }
        assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
        { eapply (RHEAP_munchW sp0 VSP CEIL); [apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| | exact P2].
          intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
        assert (ST3 : stk usegs m3 (usp0 - 8388608) (usp0 + -128)).
        { eapply stk_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| pose proof BA2 as (ST2' & _); unfold LO in ST2'; exact ST2'| intros y Hy; cbn; lia]. }
        assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid TID VSP CEIL); [exact BA2| apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| exact MI3| unfold LO; exact ST3]).
        assert (EX3 : EXTRA' m3 s) by (eapply (EXTRA_munch CS sp0 VSP CEIL); [exact WOKV| exact MUd| exact WMd| reflexivity| exact EX2]).
        assert (FR3 : FRAME' m3) by (unfold MFRAME; eapply (MFRAME_munch sp0 argv VSP CEIL); [apply WOK_WOKE; exact WOKV| exact MUd| exact WMd| exact FR2]).
        assert (ERR3 : rw_cells usegs m3 3344580 [C4 errv]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact ERR2|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (BLK1' : rw_cells usegs m3 A [CB (length DATA) DATA]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact BLK1|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (RESTB' : rw_cells usegs m3 (A + LEN + Z.of_nat (length bs)) [CB (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat (skipn (length bs) junk)]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact RESTB|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (SGab : rw_cells usegs m3 RSTAGE [CB (length bs) bs; CB (Z.to_nat CNT - length bs) (skipn (length bs) sjk)]).
        { eapply rw_cells_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact DST2|]. intros y Hy. cbn in Hy |- *. lia. }
        assert (SGc : stk usegs m3 (RSTAGE + CNT) (RSTAGE + 65536)).
        { eapply stk_agree; [eapply agree_on_of_munch; [exact MUd| exact WMd]| exact REST2|]. intros y Hy. cbn. lia. }
        (* [comment removed for export] *)
        pose proof (Str_cpy.rw_cells_CB_join _ _ _ _ _ _ _ BLK1' ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact DSTB')) as BLKab.
        assert (BLK3 : rw_cells usegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs);
                                           CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (skipn (length bs) junk)]).
        { apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split.
          - replace (length DATA + length bs)%nat with (length DATA + Z.to_nat (Z.of_nat (length bs)))%nat by lia. exact BLKab.
          - cbn [cells_size csize Nat.add]. replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + LEN + Z.of_nat (length bs)) by lia.
            replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact RESTB'. }
        (* [comment removed for export] *)
        pose proof (stk_release usegs m3 RSTAGE RSTAGE _ (stk_empty usegs m3 RSTAGE ltac:(lia)) SGab ltac:(lia)) as SGlo3.
        cbn [cells_size csize Nat.add] in SGlo3.
        replace (RSTAGE + Z.of_nat (length bs + (Z.to_nat CNT - length bs + 0)))%Z with (RSTAGE + CNT)%Z in SGlo3 by lia.
        pose proof (stk_merge usegs m3 RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SGlo3 SGc ltac:(lia)) as SG3.
        clear MUd WMd WOKV SRC STG2b DSTB RESTB REST2 BLK1 BLK1' RESTB' SGc SGab SGlo3 BLKab DSTB' BLK2 DST2.
        (* [comment removed for export] *)
        zstep. zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
        apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDHEAD. cbn [rd_content rd_cap rd_buf].
        assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
        { unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
        rewrite LEN'.
        do 16 eexists. exists F, fc, m3, A, (DATA ++ bs), (skipn (length bs) junk), errv.
        split; [rewrite ?(Z.add_comm (Z.of_nat (length bs)) LEN); reflexivity|].
        split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
        split; [| split; [exact SG3| split; [exact FR3| split; [exact BA3| split; [exact EX3| split; [exact ERR3| exact FRM]]]]]].
        split; [exact P3|]. split; [exact HA|]. split; [exact BLK3|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR].
      + (* [comment removed for export] *)
        assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
        cbn [length Nat.eqb]. apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => apply (implM_unfold__ usegs tm s (POSTBODY fd P1v) msx) end.
        apply implM_ret. apply evt_done.
        cbn [POSTBODY]. unfold RDBRK.
        pose proof (stk_release usegs m2 RSTAGE RSTAGE _ (stk_empty usegs m2 RSTAGE ltac:(lia)) DST2 ltac:(lia)) as SGlo2.
        cbn [cells_size csize Nat.add length] in SGlo2.
        replace (RSTAGE + Z.of_nat (0 + (Z.to_nat CNT - 0 + 0)))%Z with (RSTAGE + CNT)%Z in SGlo2 by lia.
        pose proof (stk_merge usegs m2 RSTAGE (RSTAGE + CNT) (RSTAGE + 65536) SGlo2 REST2 ltac:(lia)) as SG3.
        do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, errv.
        split; [rewrite LENZ; reflexivity|].
        split; [exact HC|]. split; [| split; [exact SG3| split; [exact FR2| split; [exact BA2| split; [exact EX2| split; [exact ERR2| exact FRM]]]]]].
        split; [exact P2|]. split; [exact HA|]. split; [exact BLK2|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
  Qed.
End B.
End WithCeiling0.
