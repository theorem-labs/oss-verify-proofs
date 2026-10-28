(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Definition XSP : expr := EVar 2.

Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).

Definition tls_icG (RT : rt_sig) (TPV entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 TPV ->
  0 < p -> p mod 8 = 0 -> bv_unsigned sp <= p -> p + 16 <= USTACK_TOP ->
  rw_cells asegs m p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc entry m)))
    (fun c => exists v : word, icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition unw_stmtG (RT : rt_sig) (TPV entry real : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TPV ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> rt_sp0 RT Σ - bv_unsigned sp <= NORET_DEPTH -> bv_unsigned sp + 0xb0 <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (ASTA RT Σ PMc (fun ms => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 real) fc None m' (seg_rom asegs)
       /\ ART RT Σ m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp)
       /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).

Definition fsdA_contract (FSDPC : Z) : Prop := fsd_contract asegs FSDPC.
Definition fldA_contract (FLDPC : Z) : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (ws : list word),
  fullR R -> length ws = 32%nat ->
  (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 512 <= 2 ^ 64)%Z ->
  cells_at asegs m (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256) (map (fun w => C8 w) ws) ->
  evt asegs (fun ms' => exists F', ms' = MS R F' (Z_to_bv 64 (FLDPC + 128)) fc None m (seg_rom asegs))
    (MS R F (Z_to_bv 64 FLDPC) fc None m (seg_rom asegs)).

Section CoreA.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis AF : art_facts RT.
Variable Σ : rts RT.
Variable t : itab.
Hypothesis Ht : itab_sound asegs t.
Variables TPV SETPC CPYPC TLSPC UNWPC UNWREAL FSDPC FLDPC : Z.

Variables (W CW : list wrange) (kro : list kentry) (lo SPLO SPTOP ROTOP : Z).
Hypothesis HW : wf_W W = true.
Hypothesis HW0 : In (XSP, SPLO, SPTOP) W.
Hypothesis HCW : wf_W CW = true.
Hypothesis KRO : forall E (m : mem), ART RT Σ m -> mem_inv asegs m -> know_ok asegs E m kro.
Hypothesis ROTOP_ok : forall i, 0x10000 <= i < ROTOP -> ro_addr asegs (wa i) = true.
Hypothesis Hset : memset_icontract RT SETPC.
Hypothesis Hcpy : memcpy_icontract RT CPYPC.
Hypothesis Htls : tls_icG RT TPV TLSPC.
Hypothesis Hunw : unw_stmtG RT TPV UNWPC UNWREAL.
Hypothesis Hfsd : fsdA_contract FSDPC.
Hypothesis Hfld : fldA_contract FLDPC.
Let rom := seg_rom asegs.
#[local] Notation aevt := (aevt RT PMc Σ).
#[local] Notation live := (rt_live RT Σ).
#[local] Notation frames := (rt_frames RT Σ).

Definition genvA (E : env) : Prop :=
  rt_sp0 RT Σ - STACK_WIN + 64 <= uE E XSP + SPLO /\ lo + RT_STACK <= uE E XSP + SPLO /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ 0 <= lo
  /\ uE E XSP + SPTOP + 0xb0 <= rt_sp0 RT Σ /\ rt_sp0 RT Σ - (uE E XSP + SPLO) <= NORET_DEPTH /\ rt_sp0 RT Σ <= USTACK_TOP
  /\ uE E XSP mod 16 = 0 /\ SPLO <= 0 <= SPTOP
  /\ (forall (x : Z) (a : word), x <= uE E XSP + SPTOP -> Wd E CW a -> aclient live frames x (bv_unsigned a))
  /\ (forall (x : Z) (a : word), x <= uE E XSP + SPLO -> Wd E W a -> aclient live frames x (bv_unsigned a)).

Definition CIA (fc : bv 32) (E : env) (m0 base : mem) (ss : sym_state) (ms : machine_state) : Prop :=
  exists (R F : bvmap 5 word),
    ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E base (s_log ss)) rom
    /\ regs_ok E (s_regs ss) R /\ log_flat E (s_log ss) /\ know_ok asegs E base (s_know ss) /\ fullR R
    /\ mem_inv asegs (ms_mem ms) /\ wmono asegs m0 (ms_mem ms)
    /\ (forall x : word, aclient live frames (uE E XSP + SPLO) (bv_unsigned x) -> ~ Wd E W x -> base x = m0 x)
    /\ log_inW W (s_log ss) = true
    /\ genvA E /\ ART RT Σ (ms_mem ms) /\ stk asegs (ms_mem ms) lo (uE E XSP + SPTOP).
Definition CIXA (fc : bv 32) (E : env) (m0 base : mem) (ss : sym_state) (ms : machine_state) : Prop :=
  (200 <= s_next ss)%nat /\ forall E', eagree (s_next ss) E E' -> CIA fc E' m0 base ss ms.

Definition nodeA_ok (fc : bv 32) (ss ss' : sym_state) (E : env) (m0 base : mem) (ms : machine_state) : Prop :=
  forall K : config -> Prop,
    (forall E' base' ms', eagree (s_next ss) E E' -> (s_next ss <= s_next ss')%nat -> CIXA fc E' m0 base' ss' ms' -> aevt K ms') ->
    aevt K ms.

Definition sp_off (ss : sym_state) : option Z :=
  let '(b, k) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 2)) in if expr_eqb b XSP then Some k else None.

Definition kcli (cws : list wrange) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => in_W cws kb kk (kk + Z.of_nat w)
  | KZero (SA kb kk) (ELit len) | KFill (SA kb kk) (ELit len) _ | KUnk (SA kb kk) (ELit len) | KBlob (SA kb kk) (ELit len) _ =>
      (Z.leb 0 len && Z.ltb len two64 && in_W cws kb kk (kk + len))%bool
  | KImg lo' hi' => (Z.leb 0x10000 lo' && Z.leb hi' ROTOP)%bool
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ | KWr _ _ => true
  | _ => false
  end.

Definition igate (PC : Z) (ss : sym_state) : option (Z * Z) :=
  match s_log ss, sr_get (s_regs ss) (Z_to_bv 5 1), sp_off ss with
  | [], ELit ra, Some spoff =>
      if (Z.eqb (s_pc ss) PC && Z.leb 0 ra && Z.ltb ra two64 && Z.eqb (ra mod 4) 0
          && Z.leb SPLO spoff && Z.eqb (spoff mod 16) 0 && Z.leb spoff 0)%bool
      then Some (ra, spoff) else None
  | _, _, _ => None
  end.

Definition dgate (PC : Z) (ss : sym_state) : option (Z * Z * Z * Z) :=
  match igate PC ss, sr_get (s_regs ss) (Z_to_bv 5 12) with
  | Some (ra, spoff), ELit n =>
      let '(db, dk) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 10)) in
      if (expr_eqb db XSP && Z.ltb 0 n && Z.leb n 4096 && Z.leb spoff dk && Z.leb (dk + n) SPTOP && in_W W XSP dk (dk + n))%bool
      then Some (ra, spoff, dk, n) else None
  | _, _ => None
  end.

Definition keepI (spoff : Z) (ss : sym_state) (extra : kentry -> bool) : list kentry :=
  List.filter (fun K => (extra K && kcli ((XSP, spoff, SPTOP) :: CW) K)%bool) (s_know ss) ++ kro.

Definition node_iset (ss : sym_state) : option sym_state :=
  match dgate SETPC ss, sr_get (s_regs ss) (Z_to_bv 5 11) with
  | Some (ra, spoff, dk, n), ELit 0 =>
      let fk := facts_of (s_know ss) in
      Some (SSR (retZ ra) (havoc_regs (s_regs ss) CLOB (s_next ss)) []
               (kzeros XSP dk n ++ keepI spoff ss (kkeep fk XSP dk n)) (s_next ss + 14)%nat None)
  | _, _ => None
  end.

Definition node_icpy (ss : sym_state) : option sym_state :=
  match dgate CPYPC ss with
  | Some (ra, spoff, dk, n) =>
      let fk := facts_of (s_know ss) in
      let '(sb, sk) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 11)) in
      if (expr_eqb sb XSP && Z.eqb (n mod 8) 0 && Z.leb spoff sk && Z.leb (sk + n) SPTOP && (Z.leb (dk + n) sk || Z.leb (sk + n) dk))%bool then
        match read_words asegs ss fk XSP sk (Z.to_nat (n / 8)) with
        | Some vs => Some (SSR (retZ ra) (havoc_regs (s_regs ss) CLOB (s_next ss)) []
                              (kwords8 XSP dk vs ++ keepI spoff ss (kkeep fk XSP dk n)) (s_next ss + 14)%nat None)
        | None => None
        end
      else None
  | None => None
  end.

Definition kn_has_word (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool :=
  existsb (fun K => match K with KWord a' w' v' => (saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v')%bool | _ => false end) kn.
Definition node_itls (ss : sym_state) : option sym_state :=
  match igate TLSPC ss with
  | Some (ra, spoff) =>
      let '(pb, pk) := split_lit (sr_get (s_regs ss) (Z_to_bv 5 10)) in
      if (expr_eqb pb XSP && Z.leb spoff pk && Z.leb (pk + 16) SPTOP && Z.eqb (pk mod 8) 0 && expr_eqb (sr_get (s_regs ss) (Z_to_bv 5 4)) (ELit TPV)
          && kn_has_word (s_know ss) (SA XSP pk) 8 (ELit 1) && kn_has_word (s_know ss) (SA XSP (pk + 8)) 8 (ELit 0))%bool
      then Some (SSR (retZ ra) (havoc_regs (havoc_regs (s_regs ss) CLOB (s_next ss)) [10%nat] (s_next ss + 14)%nat) []
                    (keepI spoff ss (fun _ => true)) (s_next ss + 15)%nat None)
      else None
  | None => None
  end.

Definition node_unw (ss : sym_state) : option sym_state :=
  match s_log ss, sp_off ss with
  | [], Some spoff =>
      if (Z.eqb (s_pc ss) UNWPC && Z.leb SPLO spoff && Z.eqb (spoff mod 16) 0 && Z.leb spoff 0 && expr_eqb (sr_get (s_regs ss) (Z_to_bv 5 4)) (ELit TPV))%bool
      then Some (SSR UNWREAL (havoc_regs (s_regs ss) CLOB (s_next ss)) [] (keepI spoff ss (fun _ => true)) (s_next ss + 14)%nat None)
      else None
  | _, _ => None
  end.

Fixpoint kfpv (b : expr) (k : Z) (nx : nat) (cnt : nat) : list kentry :=
  match cnt with O => [] | S c => KWord (SA b k) 8 (EVar nx) :: kfpv b (k + 8) (S nx) c end.
Definition node_fsdA (ss : sym_state) : option sym_state :=
  let regs := s_regs ss in let fk := facts_of (s_know ss) in
  let '(db, dk) := split_lit (sr_get regs (Z_to_bv 5 10)) in
  match s_log ss with
  | [] => if (Z.eqb (s_pc ss) FSDPC && expr_eqb db XSP && Z.leb SPLO (dk + 256) && Z.leb (dk + 512) SPTOP && in_W W XSP (dk + 256) (dk + 512))%bool
          then Some (SSR (FSDPC + 128) regs [] (kfpv XSP (dk + 256) (s_next ss) 32 ++ List.filter (kkeep fk XSP (dk + 256) 256) (s_know ss)) (s_next ss + 32)%nat None)
          else None
  | _ => None
  end.

Definition node_fldA (ss : sym_state) : option sym_state :=
  let regs := s_regs ss in
  let '(db, dk) := split_lit (sr_get regs (Z_to_bv 5 10)) in
  if (Z.eqb (s_pc ss) FLDPC && expr_eqb db XSP && Z.leb SPLO (dk + 256) && Z.leb (dk + 512) SPTOP)%bool
  then Some (SSR (FLDPC + 128) regs (s_log ss) (s_know ss) (s_next ss) (s_resv ss))
  else None.

Definition STOPSA (ENDPC : Z) : list Z := [SETPC; CPYPC; TLSPC; UNWPC; FSDPC; FLDPC; ENDPC].
Fixpoint xautoA (ENDPC : Z) (fuel : nat) (k : nat) (ss : sym_state) : option sym_state :=
  match k with
  | O => None
  | S k' =>
      match node_run asegs t W fuel (STOPSA ENDPC) ss with
      | None => None
      | Some ss1 =>
          let pc := s_pc ss1 in
          if Z.eqb pc ENDPC then node_flush ss1
          else if Z.eqb pc FLDPC then obind (node_fldA ss1) (xautoA ENDPC fuel k')
          else obind (obind (node_flush ss1) gc_sp) (fun ss3 =>
                 obind (if Z.eqb pc SETPC then node_iset ss3
                        else if Z.eqb pc CPYPC then node_icpy ss3
                        else if Z.eqb pc TLSPC then node_itls ss3
                        else if Z.eqb pc UNWPC then node_unw ss3
                        else if Z.eqb pc FSDPC then node_fsdA ss3
                        else None) (xautoA ENDPC fuel k'))
      end
  end.

Lemma aevt_call : forall K ms (Q : config -> Prop),
  cps asegs (ASTA RT Σ PMc (eq ms)) Q ->
  (forall c, Q c -> exists Pm : machine_state -> Prop, ASTA RT Σ PMc Pm c /\ forall ms', Pm ms' -> aevt K ms') ->
  aevt K ms.
Proof.
  intros K ms Q H HQ T c Hc Hk. apply (H T c Hc). intros c' Hq.
  destruct (HQ c' Hq) as (Pm & HA & HP). destruct (ASTA_unpack RT Σ PMc Pm c' HA) as (ms' & HPm & Hc'). exact (HP ms' HPm T c' Hc' Hk).
Qed.

Lemma aevt_msteps : forall K ms ms', Exec.msteps asegs ms ms' -> aevt K ms' -> aevt K ms.
Proof. intros K ms ms' HM HK. apply (aevt_evt RT AF PMc MST). exists ms'. split; [exact HM| exact HK]. Qed.

Lemma nodeA_ok_bind : forall fc ss ss1 ss' E m0 base ms,
  nodeA_ok fc ss ss1 E m0 base ms ->
  (forall E1 base1 ms1, eagree (s_next ss) E E1 -> CIXA fc E1 m0 base1 ss1 ms1 -> nodeA_ok fc ss1 ss' E1 m0 base1 ms1) ->
  nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss1 ss' E m0 base ms H1 H2 K HK. apply H1. intros E1 base1 ms1 HA1 HL1 HC1.
  apply (H2 E1 base1 ms1 HA1 HC1). intros E' base' ms' HA' HL' HC'. apply (HK E' base' ms'); [| lia| exact HC'].
  eapply eagree_trans; [exact HA1| eapply eagree_le; [exact HA'| exact HL1]].
Qed.

Lemma uE_eagree : forall E E' e, eagree FPB E E' -> evars_lt FPB e = true -> uE E' e = uE E e.
Proof. intros E E' e HA HV. unfold uE. rewrite (edenot_evars_lt FPB E E' e HA HV). reflexivity. Qed.
Lemma XSP_lt : evars_lt FPB XSP = true. Proof. reflexivity. Qed.

Lemma genvA_eagree : forall E E', genvA E -> eagree FPB E E' -> genvA E'.
Proof.
  intros E E' (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW) HA.
  unfold genvA. rewrite !(uE_eagree E E' XSP HA XSP_lt).
  repeat (split; [assumption|]). split.
  - intros x a Hx Hw. apply (GC x a Hx). apply (Wd_eagree E' E); [exact HCW| apply eagree_sym; exact HA| exact Hw].
  - intros x a Hx Hw. apply (GW x a Hx). apply (Wd_eagree E' E); [exact HW| apply eagree_sym; exact HA| exact Hw].
Qed.

Lemma aclient_le : forall s s' a, aclient live frames s a -> s' <= s -> aclient live frames s' a.
Proof. intros s s' a H Hle. eapply Sj_acps.aclient_mono; [exact H| auto| auto| exact Hle]. Qed.

Lemma aclient_up : forall s s' a, aclient live frames s a -> s <= s' -> aclient live frames s' a \/ (s <= a < s').
Proof.
  intros s s' a H Hle. unfold aclient in *.
  destruct H as [H|H]; [| left; right; exact H].
  destruct (Z.lt_ge_cases a s'); [right; lia| left; left; lia].
Qed.

Lemma regs_val : forall E sr R r, regs_ok E sr R -> fullR R -> reg_get R r = edenot E (sr_get sr r).
Proof.
  intros E sr R r HR HF. rewrite <- (HR r). unfold getr.
  destruct (bv_eqb r 0) eqn:Hr; [| reflexivity].
  destruct HF as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                  x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  unfold bv_eqb in Hr. apply Z.eqb_eq in Hr. replace r with (Z_to_bv 5 0) by (apply bv_eq; rewrite Hr; reflexivity). vm_compute. reflexivity.
Qed.

Lemma sp_off_val : forall E ss R spoff,
  sp_off ss = Some spoff -> regs_ok E (s_regs ss) R -> fullR R -> genvA E -> SPLO <= spoff <= 0 ->
  bv_unsigned (reg_get R (Z_to_bv 5 2)) = uE E XSP + spoff.
Proof.
  intros E ss R spoff HS HR HF HG Hsp. unfold sp_off in HS.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 2))) as [b k] eqn:Hsl.
  destruct (expr_eqb b XSP) eqn:Hb; [|discriminate]. apply expr_eqb_eq in Hb. injection HS as <-. subst b.
  rewrite (regs_val E _ R (Z_to_bv 5 2) HR HF). rewrite (split_lit_val E _ XSP k Hsl). unfold uE.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). unfold uE in *.
  apply Z.mod_small. unfold two64. pose proof (u64_range (edenot E XSP)). unfold USTACK_TOP, RT_STACK in *. lia.
Qed.

Lemma xsp_arg_val : forall E e k,
  split_lit e = (XSP, k) -> genvA E -> SPLO <= k -> k <= SPTOP ->
  bv_unsigned (edenot E e) = uE E XSP + k.
Proof.
  intros E e k Hsl HG Hk1 Hk2. rewrite (split_lit_val E e XSP k Hsl). unfold uE.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). unfold uE in *.
  apply Z.mod_small. unfold two64. pose proof (u64_range (edenot E XSP)). unfold USTACK_TOP, RT_STACK in *. lia.
Qed.

Lemma CIA_same_ms : forall E1 E2 m0 base ss ms R F fc,
  ms = MS R F (Z_to_bv 64 (s_pc ss)) fc None (mem_denot E1 base (s_log ss)) rom ->
  CIA fc E2 m0 base ss ms ->
  regs_ok E2 (s_regs ss) R /\ log_flat E2 (s_log ss) /\ know_ok asegs E2 base (s_know ss)
  /\ mem_denot E2 base (s_log ss) = mem_denot E1 base (s_log ss)
  /\ (forall x, aclient live frames (uE E2 XSP + SPLO) (bv_unsigned x) -> ~ Wd E2 W x -> base x = m0 x)
  /\ genvA E2.
Proof.
  intros E1 E2 m0 base ss ms R F fc Hms (R' & F' & Hms' & HR & HLF & HK & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  rewrite Hms in Hms'. apply MS_inj in Hms' as (<- & <- & _ & _ & EM).
  split; [exact HR|]. split; [exact HLF|]. split; [exact HK|]. split; [symmetry; exact EM|]. split; [exact HB| exact HG].
Qed.

Lemma stk_steps : forall (m m' : mem) lo' hi', stk asegs m lo' hi' -> wmono asegs m m' -> ovl_mono m m' -> stk asegs m' lo' hi'.
Proof.
  intros m m' lo' hi' (S1 & S2 & S3) HWM HO. split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hw [b Hb]].
  split; [apply HWM; exact Hw|]. unfold mrd in Hb |- *. destruct (m (wa a)) as [b0|] eqn:E0.
  - destruct (m' (wa a)) as [b1|] eqn:E1; [exists b1; reflexivity|]. exfalso. apply (HO (wa a)); [rewrite E0; discriminate| exact E1].
  - destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity| exists b; exact Hb].
Qed.

Lemma art_run : forall E base log1 log2 (m1 m2 : mem),
  genvA E -> log_flat E log1 -> log_inW W log1 = true -> log_flat E log2 -> log_inW W log2 = true ->
  m1 = mem_denot E base log1 -> m2 = mem_denot E base log2 ->
  ART RT Σ m1 -> wmono asegs m1 m2 -> ART RT Σ m2.
Proof.
  intros E base log1 log2 m1 m2 HG HF1 HL1 HF2 HL2 -> -> HA HWM.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  apply (af_frame RT AF Σ _ _ (uE E XSP + SPLO) HA); [unfold RT_STACK in *; lia| | exact HWM].
  intros a Ha. assert (NW : ~ Wd E W a) by (intros Hw; apply Ha; apply (GW _ a (Z.le_refl _) Hw)).
  rewrite (log_inW_out E W log2 base a HF2 HL2 NW). symmetry. apply (log_inW_out E W log1 base a HF1 HL1 NW).
Qed.

Theorem nodeA_run_sound : forall fc fuel stops ss ss' E m0 base ms,
  node_run asegs t W fuel stops ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc fuel stops ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_run in Hn.
  destruct (log_inW W (s_log (sym_execTX asegs t KCAP fuel true stops ss))) eqn:HL; [|discriminate]. injection Hn as <-.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose (fx := PropExec.mkFP F fc).
  assert (HSTOK : forall E', eagree (s_next ss) E E' -> @st_ok fx asegs E' base rom ss ms).
  { intros E' HAE. destruct (HC E' HAE) as (R' & F' & Hms' & HR' & HLF' & HK' & _).
    exists R'. rewrite Hms in Hms' |- *. injection Hms' as ER EF EM. subst R'.
    split; [unfold mkst; cbn; rewrite <- EM; reflexivity|]. split; [exact HR'|]. split; [exact HLF'| exact HK']. }
  destruct (@sym_execTX_sound fx asegs t KCAP fuel true stops ss E base rom ms Ht HSTOK) as (E1 & ms1 & HA1 & Hle & HMS & HALL).
  pose proof (msteps_lib_of_as _ _ _ HMS) as HMSL.
  apply (aevt_msteps K ms ms1 HMSL). apply (HK E1 base ms1 HA1 Hle).
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. destruct (HALL E'' HA'') as (R1 & Hms1 & HR1 & HLF1 & HK1).
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [exact HA1|]. eapply eagree_le; [exact HA''| exact Hle]. }
  destruct (CIA_same_ms E E'' m0 base ss ms R F fc Hms (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  exists R1, F. split; [exact Hms1|]. split; [exact HR1|]. split; [exact HLF1|]. split; [exact HK1|].
  split. { pose proof (msteps_full asegs _ _ HMSL) as X. rewrite Hms, Hms1 in X. cbn in X. apply X. exact HFR. }
  pose proof (msteps_mem_inv asegs _ _ HMSL HMI) as (HMI1 & HWM1 & HOV1).
  split; [exact HMI1|]. split; [eapply wmono_trans; [exact HWM| exact HWM1]|]. split; [exact HB''|]. split; [exact HL|]. split; [exact HG''|].
  rewrite Hms in HA, HST. rewrite Hms, Hms1 in HWM1, HOV1. rewrite Hms1. unfold MS in HA, HST, HWM1, HOV1 |- *. cbn [ms_mem] in HA, HST, HWM1, HOV1 |- *.
  split.
  - apply (art_run E'' base (s_log ss) _ _ _ HG'' HLF'' HLW HLF1 HL (eq_sym EM) eq_refl HA HWM1).
  - assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
    rewrite (uE_eagree E E'' XSP HAF XSP_lt). exact (stk_steps _ _ _ _ HST HWM1 HOV1).
Qed.

Theorem nodeA_flush_sound : forall fc ss ss' E m0 base ms,
  node_flush ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_flush in Hn.
  destruct (carry (s_log ss) (s_know ss) []) as [[kn' scs] hs] eqn:Hc. destruct scs; [|discriminate]. injection Hn as <-.
  apply (HK E (ms_mem ms) ms (eagree_refl _ _) ltac:(cbn; lia)).
  split; [cbn; exact Hnx|]. intros E' HA. destruct (HC E' HA) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA' & HST).
  exists R, F. cbn [s_pc s_regs s_log s_know s_next].
  assert (EM : ms_mem ms = mem_denot E' base (s_log ss)) by (rewrite Hms; reflexivity).
  split; [cbn [mem_denot]; rewrite Hms at 1; rewrite EM; reflexivity|].
  split; [exact HR|]. split; [exact I|].
  split. { rewrite EM. eapply (carry_sound asegs E' base); [exact Hc| exact HLF| exact HK0| constructor]. }
  split; [exact HFR|]. split; [exact HMI|]. split; [exact HWM|].
  split. { intros x Hx Hw. rewrite EM. rewrite (log_inW_out E' W _ _ x HLF HLW Hw). apply HB; assumption. }
  split; [reflexivity|]. split; [exact HG|]. split; [exact HA'| exact HST].
Qed.

Theorem nodeA_drop_sound : forall fc b lo' hi' ss ss' E m0 base ms,
  node_drop b lo' hi' ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc b lo' hi' ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_drop in Hn.
  destruct (s_log ss) eqn:HL; [|discriminate]. injection Hn as <-.
  apply (HK E base ms (eagree_refl _ _) ltac:(cbn; lia)).
  split; [cbn; exact Hnx|]. intros E' HA. destruct (HC E' HA) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA' & HST).
  exists R, F. cbn [s_pc s_regs s_log s_know s_next]. rewrite HL in Hms, HLF. cbn [mem_denot] in Hms |- *.
  repeat (split; [assumption|]). split.
  { unfold know_ok in *. rewrite Forall_forall in HK0 |- *. intros K0 HIn. apply List.filter_In in HIn as [HIn _]. apply HK0. exact HIn. }
  repeat (split; [assumption|]). split; [reflexivity|]. split; [exact HG|]. split; [exact HA'| exact HST].
Qed.

Lemma know_ok_app2 : forall E (m : mem) k1 k2, know_ok asegs E m k1 -> know_ok asegs E m k2 -> know_ok asegs E m (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. split; assumption. Qed.

Lemma cws_client : forall E spoff (x : word),
  genvA E -> SPLO <= spoff <= 0 -> Wd E ((XSP, spoff, SPTOP) :: CW) x -> aclient live frames (uE E XSP + spoff) (bv_unsigned x).
Proof.
  intros E spoff x HG Hsp (wb & wlo & whi & HIn & Hx). destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  destruct HIn as [HIn|HIn].
  - injection HIn as <- <- <-. left. unfold uE in *. unfold USTACK_TOP in *. lia.
  - apply (GC (uE E XSP + spoff) x ltac:(lia)). exists wb, wlo, whi. split; [exact HIn| exact Hx].
Qed.

Lemma kcli_sound : forall E (M M' : mem) cws K,
  kentry_ok asegs E M K -> kcli cws K = true ->
  (forall x : word, Wd E cws x -> M' x = M x) -> wmono asegs M M' -> mem_inv asegs M' ->
  kentry_ok asegs E M' K.
Proof.
  intros E M M' cws K HK Hc HM HWM HMI.
  assert (PT : forall (kb : expr) (kk len i : Z), in_W cws kb kk (kk + len) = true -> 0 <= i < len ->
            flat E (SA kb kk) len -> M' (Z_to_bv 64 (estart E (SA kb kk) + i)) = M (Z_to_bv 64 (estart E (SA kb kk) + i))).
  { intros kb kk len i HiW Hi Hfl. apply HM. eapply in_W_Wd; [exact HiW|]. pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
    unfold estart in *. cbn [a_base a_off] in *. rewrite u_small; lia. }
  assert (LIT : forall len rest, (Z.leb 0 len && Z.ltb len two64 && rest)%bool = true -> rest = true /\ elenZ E (ELit len) = len).
  { intros len rest H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    split; [exact H3|]. rewrite elenZ_lit. apply Z.mod_small. unfold two64 in H2. lia. }
  destruct K as [[kb kk] w v | [kb kk] len | [kb kk] len j | lo' hi' | e m1 | e lo' hi' | a len | a1 n1 a2 n2 | [kb kk] len c | [kb kk] len];
    cbn [kcli] in Hc; cbn [kentry_ok] in HK |- *.
  -   destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd.
    pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
    apply rdn_ext; [rewrite EU; lia|]. intros x Hx. apply HM. eapply in_W_Wd; [exact Hc|]. rewrite EU in Hx. unfold estart in *. cbn [a_base a_off] in *. lia.
  -   destruct len as [len| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. split; [exact Hfl|].
    destruct (LIT len _ Hc) as [Hc' EL]. rewrite EL in *. intros i Hi. rewrite (PT kb kk _ i Hc' Hi Hfl). apply Hz. exact Hi.
  -   destruct len as [len| | | | | | |]; try discriminate. destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|].
    destruct (LIT len _ Hc) as [Hc' EL]. rewrite EL in *. intros i Hi. rewrite (PT kb kk _ i Hc' Hi Hfl). apply Hz. exact Hi.
  -   destruct HK as (H0 & H1 & Hz). split; [exact H0|]. split; [exact H1|]. apply andb_prop in Hc as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    intros i Hi. destruct (M' (Z_to_bv 64 i)) as [b|] eqn:Eb; [|reflexivity]. exfalso.
    pose proof (Mem.mem_inv_ro asegs M' _ b HMI Eb) as X. unfold wa in ROTOP_ok. rewrite (ROTOP_ok i) in X by lia. discriminate.
  - exact HK.
  - exact HK.
  -   destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m1 Hd Hdm.
    pose proof (flat_u E _ _ Hfl) as EU. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m1 as [|m']; [reflexivity|].
    apply (store_ok_wmono asegs M M'); [rewrite u_small; lia| apply Hs; assumption| exact HWM].
  - exact HK.
  -   destruct len as [len| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. split; [exact Hfl|].
    destruct (LIT len _ Hc) as [Hc' EL]. rewrite EL in *. intros i Hi. rewrite (PT kb kk _ i Hc' Hi Hfl). apply Hz. exact Hi.
  -   destruct len as [len| | | | | | |]; try discriminate. destruct HK as [Hfl Hz]. split; [exact Hfl|].
    destruct (LIT len _ Hc) as [Hc' EL]. rewrite EL in *. intros i Hi. rewrite (PT kb kk _ i Hc' Hi Hfl). apply Hz. exact Hi.
Qed.

Lemma keepI_sound : forall E (M1 M' : mem) spoff ss (extra : kentry -> bool),
  (forall K, In K (s_know ss) -> extra K = true -> kentry_ok asegs E M1 K) ->
  (forall x : word, Wd E ((XSP, spoff, SPTOP) :: CW) x -> M' x = M1 x) -> wmono asegs M1 M' -> mem_inv asegs M' -> ART RT Σ M' ->
  know_ok asegs E M' (keepI spoff ss extra).
Proof.
  intros E M1 M' spoff ss extra HK HM HWM HMI HA. unfold keepI, know_ok. apply Forall_app. split.
  - rewrite Forall_forall. intros K HIn. apply List.filter_In in HIn as [HIn Hb]. apply andb_prop in Hb as [He Hc].
    eapply kcli_sound; [exact (HK K HIn He)| exact Hc| exact HM| exact HWM| exact HMI].
  - apply KRO; assumption.
Qed.

Definition mpatch (M M' : mem) (d n : Z) : mem :=
  fun x => if (Z.leb d (bv_unsigned x) && Z.ltb (bv_unsigned x) (d + n))%bool then M' x else M x.
Lemma mpatch_in : forall M M' d n x, d <= bv_unsigned x < d + n -> mpatch M M' d n x = M' x.
Proof. intros. unfold mpatch. replace (_ && _)%bool with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. Qed.
Lemma mpatch_out : forall M M' d n x, ~ (d <= bv_unsigned x < d + n) -> mpatch M M' d n x = M x.
Proof.
  intros. unfold mpatch. destruct (Z.leb_spec0 d (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (d + n)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma wview_ext1 : forall (M M' : mem) x, M' x = M x -> wview asegs M' x = wview asegs M x.
Proof. intros M M' x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma mpatch_wmono1 : forall M M' d n, wmono asegs M M' -> wmono asegs M (mpatch M M' d n).
Proof.
  intros M M' d n HWM x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) d) as [L|L].
  - rewrite (wview_ext1 M (mpatch M M' d n) x (mpatch_out M M' d n x ltac:(lia))). exact Hx.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (d + n)) as [L2|L2].
    + rewrite (wview_ext1 M' (mpatch M M' d n) x (mpatch_in M M' d n x ltac:(lia))). apply HWM. exact Hx.
    + rewrite (wview_ext1 M (mpatch M M' d n) x (mpatch_out M M' d n x ltac:(lia))). exact Hx.
Qed.
Lemma mpatch_wmono2 : forall M M' d n, wmono asegs M M' -> wmono asegs (mpatch M M' d n) M'.
Proof.
  intros M M' d n HWM x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) d) as [L|L].
  - rewrite (wview_ext1 M (mpatch M M' d n) x (mpatch_out M M' d n x ltac:(lia))) in Hx. apply HWM. exact Hx.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (d + n)) as [L2|L2].
    + rewrite (wview_ext1 M' (mpatch M M' d n) x (mpatch_in M M' d n x ltac:(lia))) in Hx. exact Hx.
    + rewrite (wview_ext1 M (mpatch M M' d n) x (mpatch_out M M' d n x ltac:(lia))) in Hx. apply HWM. exact Hx.
Qed.

Lemma igate_sound : forall PC ss ra spoff,
  igate PC ss = Some (ra, spoff) ->
  s_log ss = [] /\ s_pc ss = PC /\ sr_get (s_regs ss) (Z_to_bv 5 1) = ELit ra /\ sp_off ss = Some spoff
  /\ 0 <= ra < two64 /\ ra mod 4 = 0 /\ SPLO <= spoff <= 0 /\ spoff mod 16 = 0.
Proof.
  intros PC ss ra spoff H. unfold igate in H.
  destruct (s_log ss); [|discriminate].
  destruct (sr_get (s_regs ss) (Z_to_bv 5 1)) as [ra'| | | | | | |]; try discriminate.
  destruct (sp_off ss) as [sp'|]; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end. injection H as <- <-.
  apply andb_prop in Hg as [Hg G7]. apply andb_prop in Hg as [Hg G6]. apply andb_prop in Hg as [Hg G5]. apply andb_prop in Hg as [Hg G4].
  apply andb_prop in Hg as [Hg G3]. apply andb_prop in Hg as [G1 G2].
  apply Z.eqb_eq in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. apply Z.eqb_eq in G4. apply Z.leb_le in G5. apply Z.eqb_eq in G6. apply Z.leb_le in G7.
  repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma dgate_sound : forall PC ss ra spoff dk n,
  dgate PC ss = Some (ra, spoff, dk, n) ->
  (s_log ss = [] /\ s_pc ss = PC /\ sr_get (s_regs ss) (Z_to_bv 5 1) = ELit ra /\ sp_off ss = Some spoff
   /\ 0 <= ra < two64 /\ ra mod 4 = 0 /\ SPLO <= spoff <= 0 /\ spoff mod 16 = 0)
  /\ sr_get (s_regs ss) (Z_to_bv 5 12) = ELit n /\ split_lit (sr_get (s_regs ss) (Z_to_bv 5 10)) = (XSP, dk)
  /\ 0 < n <= 4096 /\ spoff <= dk /\ dk + n <= SPTOP /\ in_W W XSP dk (dk + n) = true.
Proof.
  intros PC ss ra spoff dk n H. unfold dgate in H.
  destruct (igate PC ss) as [[ra' sp']|] eqn:Hi; [|discriminate].
  destruct (sr_get (s_regs ss) (Z_to_bv 5 12)) as [n'| | | | | | |]; try discriminate.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db dk'] eqn:Hsl.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hg; [|discriminate] end. injection H as <- <- <- <-.
  apply andb_prop in Hg as [Hg G6]. apply andb_prop in Hg as [Hg G5]. apply andb_prop in Hg as [Hg G4]. apply andb_prop in Hg as [Hg G3].
  apply andb_prop in Hg as [G1 G2].
  apply expr_eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. apply Z.leb_le in G4. apply Z.leb_le in G5. subst db.
  split; [exact (igate_sound PC ss ra' sp' Hi)|]. repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma stk_wr_at : forall (m : mem) lo' hi' a n, stk asegs m lo' hi' -> lo' <= a -> 0 <= n -> a + n <= hi' -> wr_at asegs m a n.
Proof. intros m lo' hi' a n (H1 & H2 & ST) Ha Hn Hh. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (ST (a + i) ltac:(lia))). Qed.

Lemma stk_pres : forall (m m' : mem) lo' hi',
  stk asegs m lo' hi' -> wmono asegs m m' ->
  (forall a, lo' <= a < hi' -> m' (wa a) = m (wa a) \/ exists b, mrd asegs m' (wa a) = Some b) -> stk asegs m' lo' hi'.
Proof.
  intros m m' lo' hi' (S1 & S2 & ST) HWM HP. split; [exact S1|]. split; [exact S2|]. intros a Ha.
  destruct (ST a Ha) as [Hw [b Hb]]. split; [apply HWM; exact Hw|].
  destruct (HP a Ha) as [E0|[b' E0]]; [| exists b'; exact E0]. unfold mrd in *. rewrite E0. exists b. exact Hb.
Qed.

Lemma bytes_at_some : forall (m : mem) A bs (x : word),
  bytes_at asegs m A bs -> A <= bv_unsigned x < A + Z.of_nat (length bs) -> exists b, mrd asegs m x = Some b.
Proof.
  intros m A bs x (B1 & B2 & B3) Hx.
  specialize (B3 (Z.to_nat (bv_unsigned x - A)) ltac:(lia)). rewrite Z2Nat.id in B3 by lia.
  replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in B3 by lia. unfold wa in B3. rewrite Z_to_bv_bv_unsigned in B3.
  destruct (nth_error bs (Z.to_nat (bv_unsigned x - A))) as [b|] eqn:En; [exists b; exact B3|].
  exfalso. apply nth_error_None in En. lia.
Qed.

Lemma bytes_at_of_rdnG : forall n (m : mem) a bs,
  Common.PropExec.rdn asegs m (wa a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> bytes_at asegs m a bs.
Proof.
  induction n as [|n IH]; intros m a bs Hr Ha Hn.
  - cbn in Hr. injection Hr as <-. apply Mem.bytes_at_nil. lia.
  - rewrite Mem.rdn_unfold in Hr.
    destruct (mrd asegs m (wa a)) as [b|] eqn:Hb; [|discriminate].
    destruct (Common.PropExec.rdn asegs m (wa a + 1)%bv n) as [r|] eqn:Hr'; [|discriminate]. injection Hr as <-.
    change (b :: r) with ([b] ++ r). apply (proj2 (Mem.bytes_at_app asegs m a [b] r)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. exact Hb.
    + cbn [length Z.of_nat Pos.of_succ_nat]. destruct n as [|n'].
      * cbn in Hr'. injection Hr' as <-. apply Mem.bytes_at_nil. lia.
      * apply IH; [| lia| lia]. rewrite <- Hr'. f_equal. unfold wa. apply bv_eq.
        rewrite u_add1 by (rewrite unsigned_lit; lia). rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma stk_after_call : forall E (m m' : mem) spoff d n bs,
  genvA E -> SPLO <= spoff <= 0 ->
  stk asegs m lo (uE E XSP + SPTOP) -> stk asegs m' lo (uE E XSP + spoff) -> wmono asegs m m' ->
  rt_pres_ex live frames (uE E XSP + spoff) d n m m' -> bytes_at asegs m' d bs -> Z.of_nat (length bs) = n ->
  stk asegs m' lo (uE E XSP + SPTOP).
Proof.
  intros E m m' spoff d n bs HG Hsp ST ST' HWM PR BY Hlen.
  destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  destruct (stk_split asegs m lo (uE E XSP + spoff) (uE E XSP + SPTOP) ST ltac:(unfold RT_STACK in *; lia)) as [_ STH].
  apply (stk_merge asegs m' lo (uE E XSP + spoff) (uE E XSP + SPTOP) ST'); [| unfold RT_STACK in *; lia].
  apply (stk_pres m m' _ _ STH HWM). intros a Ha.
  assert (UA : bv_unsigned (wa a) = a) by (unfold wa; apply u_small; unfold USTACK_TOP, RT_STACK in *; lia).
  assert (CL : aclient live frames (uE E XSP + spoff) (bv_unsigned (wa a))) by (rewrite UA; left; unfold USTACK_TOP in *; lia).
  destruct (Z.lt_ge_cases a d) as [L|L]; [left; apply (PR _ CL); rewrite UA; lia|].
  destruct (Z.lt_ge_cases a (d + n)) as [L2|L2]; [| left; apply (PR _ CL); rewrite UA; lia].
  right. exact (bytes_at_some m' d bs (wa a) BY ltac:(rewrite UA; lia)).
Qed.

Lemma mkR_sel : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  reg_get R (Z_to_bv 5 1) = x1 /\ reg_get R (Z_to_bv 5 2) = x2 /\ reg_get R (Z_to_bv 5 4) = x4 /\ reg_get R (Z_to_bv 5 10) = x10
  /\ reg_get R (Z_to_bv 5 11) = x11 /\ reg_get R (Z_to_bv 5 12) = x12.
Proof. intros. vm_compute. repeat split; reflexivity. Qed.

Lemma Some_inj : forall {A} (a b : A), Some a = Some b -> a = b.
Proof. intros A a b H. injection H as H'. exact H'. Qed.

Lemma wz_of_u : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma aclient_anchor : forall E s (x : word),
  genvA E -> uE E XSP + SPLO <= s <= uE E XSP + SPTOP ->
  aclient live frames (uE E XSP + SPLO) (bv_unsigned x) -> ~ Wd E W x -> aclient live frames s (bv_unsigned x).
Proof.
  intros E s x HG Hs Hc Hw. destruct (aclient_up _ s _ Hc ltac:(lia)) as [H|H]; [exact H|].
  exfalso. apply Hw. exists XSP, SPLO, SPTOP. split; [exact HW0|]. unfold uE in *. lia.
Qed.
Lemma dst_in_W : forall E dk n (x : word), in_W W XSP dk (dk + n) = true ->
  uE E XSP + dk <= bv_unsigned x < uE E XSP + dk + n -> Wd E W x.
Proof. intros E dk n x HiW Hx. eapply in_W_Wd; [exact HiW|]. unfold uE in Hx. lia. Qed.

Theorem nodeA_iset_sound : forall fc ss ss' E m0 base ms,
  node_iset ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_iset in Hn.
  destruct (dgate SETPC ss) as [[[[ra spoff] dk] n]|] eqn:Hg; [|discriminate].
  destruct (sr_get (s_regs ss) (Z_to_bv 5 11)) as [cz| | | | | | |] eqn:H11; try discriminate.
  destruct cz as [|p|p]; try discriminate. apply Some_inj in Hn. subst ss'.
  destruct (dgate_sound SETPC ss ra spoff dk n Hg) as ((HL & HPC & H1 & HSO & Hra & Hra4 & Hspo & Hspm) & H12 & Hsl & Hnn & Hdk1 & Hdk2 & HiW).
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HA, HST. unfold MS in HMI, HWM, HA, HST. cbn [ms_mem] in HMI, HWM, HA, HST.

  pose proof (sp_off_val E ss R spoff HSO HR HFR HG ltac:(lia)) as U2.
  pose proof (regs_val E _ R (Z_to_bv 5 10) HR HFR) as V10. rewrite (xsp_arg_val E _ dk Hsl HG ltac:(lia) ltac:(lia)) in V10 || idtac.
  assert (U10 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = uE E XSP + dk).
  { rewrite (regs_val E _ R (Z_to_bv 5 10) HR HFR). apply (xsp_arg_val E _ dk Hsl HG); lia. }
  assert (V12 : reg_get R (Z_to_bv 5 12) = Z_to_bv 64 n).
  { change (reg_get R (Z_to_bv 5 12)) with (getr R (Z_to_bv 5 12)). exact (getr_lit E _ R _ _ HR H12). }
  assert (V11 : reg_get R (Z_to_bv 5 11) = Z_to_bv 64 0).
  { change (reg_get R (Z_to_bv 5 11)) with (getr R (Z_to_bv 5 11)). exact (getr_lit E _ R _ _ HR H11). }
  assert (V1 : reg_get R (Z_to_bv 5 1) = Z_to_bv 64 ra).
  { change (reg_get R (Z_to_bv 5 1)) with (getr R (Z_to_bv 5 1)). exact (getr_lit E _ R _ _ HR H1). }
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  destruct (mkR_sel x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (Q1 & Q2 & Q4 & Q10 & Q11 & Q12).
  rewrite Q1 in V1. rewrite Q2 in U2. rewrite Q10 in U10. rewrite Q11 in V11. rewrite Q12 in V12. subst x1 x11 x12.
  set (d := uE E XSP + dk) in *. set (usp := uE E XSP + spoff) in *.

  assert (CD : checked_dst RT Σ base x2 d n).
  { split; [| split].
    - intros _. split; [apply (af_acc_stack RT AF Σ base d n HA); unfold RT_STACK in *; lia|].
      right; right; left. unfold USTACK_TOP, RT_STACK in *. lia.
    - intros i Hi. left. rewrite U2. unfold USTACK_TOP, RT_STACK in *. lia.
    - apply (stk_wr_at base lo _ d n HST); unfold RT_STACK in *; lia. }
  assert (COK : call_ok RT Σ base x2 lo).
  { split; [| split; [| split; [| split]]]; rewrite ?U2.
    - apply (proj1 (stk_split asegs base lo usp _ HST ltac:(unfold RT_STACK in *; lia))).
    - lia. - unfold RT_STACK in *; lia. - unfold USTACK_TOP in *; lia.
    - subst usp. rewrite Z.add_mod, G8, Hspm by lia. reflexivity. }
  pose proof (Hset Σ PMc (Z_to_bv 64 ra) x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F fc base d n (Z_to_bv 8 0) lo FDO MST (wz_of_u _ _ U10) ltac:(rewrite Z_to_bv_unsigned; reflexivity) eq_refl
                ltac:(unfold USTACK_TOP, RT_STACK in *; lia) ltac:(lia) CD HA HMI COK) as HCPS.
  unfold entry_st in HCPS. rewrite <- HPC in HCPS. rewrite Hms.
  apply (aevt_call K _ _ HCPS). intros c HQ. unfold icpt_postF in HQ. eexists. split; [exact HQ|].
  intros ms' (m' & RS & (HA' & HMI' & HWM' & HST') & PR & BY).
  destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->).
  rewrite U2 in HST', PR. rewrite <- (wz_of_u x10 d U10).
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  apply (HK (eupds E (s_next ss) vals) m'); [apply eupds_agree| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| lia]. }
  assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
  destruct (CIA_same_ms E E'' m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  pose proof (uE_eagree E E'' XSP HAF XSP_lt) as EX.
  assert (OUTB : forall x : word, ~ (d <= bv_unsigned x < d + n) -> mpatch base m' d n x = base x) by (intros; apply mpatch_out; assumption).
  exists (mkR (Z_to_bv 64 ra) x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F'.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split. { pose proof (mod4_mod2 ra Hra4) as M2. rewrite ret_pc_even by (unfold two64 in Hra; lia). unfold retZ.
           replace (ra - ra mod 2) with ra by lia. reflexivity. }
  split. { rewrite <- (regupds_CLOB (Z_to_bv 64 ra) x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 0) (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
           apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
           intros j Hj. pose proof (proj1 HA'' (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj. }
  split; [exact I|].
  split. { apply know_ok_app2.
    - apply kzeros_ok.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. unfold d, RT_STACK in *; lia.
      + lia.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. unfold d, usp, USTACK_TOP, RT_STACK in *; lia.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. exact BY.
    - apply (keepI_sound E'' (mpatch base m' d n) m' spoff ss).
      + intros K0 HIn Hkp. pose proof (proj1 (Forall_forall _ _) HK'' K0 HIn) as HK1.
        eapply (kkeep_sound asegs E'' base (mpatch base m' d n) (facts_of (s_know ss)) XSP dk n K0 (facts_of_ok _ _ _ _ HK'') HK1 Hkp);
          [lia| unfold two64; lia| | apply mpatch_wmono1; exact HWM'].
        intros x Hx. apply mpatch_out. change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP) in Hx. rewrite EX in Hx. exact Hx.
      + intros x Hw. destruct (Z.lt_ge_cases (bv_unsigned x) d) as [L|L]; [| destruct (Z.lt_ge_cases (bv_unsigned x) (d + n)) as [L2|L2]].
        * rewrite mpatch_out by lia. apply PR; [| lia]. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
        * rewrite mpatch_in by lia. reflexivity.
        * rewrite mpatch_out by lia. apply PR; [| lia]. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
      + apply mpatch_wmono2. exact HWM'.
      + exact HMI'.
      + exact HA'. }
  split; [apply fullR_mkR|]. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hcx Hw. rewrite EX in Hcx. rewrite PR.
           - apply HB''; [rewrite EX; exact Hcx| exact Hw].
           - apply (aclient_anchor E usp x HG); [unfold usp; lia| exact Hcx|]. intros Hw'. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF| exact Hw'].
           - intros Hd. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF|]. apply (dst_in_W E dk n x HiW). unfold d in Hd. lia. }
  split; [reflexivity|]. split; [exact HG''|]. split; [exact HA'|].
  rewrite EX. apply (stk_after_call E base m' spoff d n _ HG ltac:(lia) HST HST' HWM' PR BY). rewrite repeat_length. lia.
Qed.

Theorem nodeA_icpy_sound : forall fc ss ss' E m0 base ms,
  node_icpy ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_icpy in Hn.
  destruct (dgate CPYPC ss) as [[[[ra spoff] dk] n]|] eqn:Hg; [|discriminate].
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 11))) as [sb sk] eqn:Hsl1.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hsk2]. apply andb_prop in Hc as [Hc Hsk1]. apply andb_prop in Hc as [Hsb Hm8].
  apply expr_eqb_eq in Hsb. apply Z.eqb_eq in Hm8. apply Z.leb_le in Hsk1. apply Z.leb_le in Hsk2. subst sb.
  assert (HAP : dk + n <= sk \/ sk + n <= dk).
  { apply orb_prop in Hap. destruct Hap as [H|H]; apply Z.leb_le in H; lia. }
  destruct (read_words asegs ss (facts_of (s_know ss)) XSP sk (Z.to_nat (n / 8))) as [vs|] eqn:HRDW; [|discriminate].
  apply Some_inj in Hn. subst ss'.
  destruct (dgate_sound CPYPC ss ra spoff dk n Hg) as ((HL & HPC & H1 & HSO & Hra & Hra4 & Hspo & Hspm) & H12 & Hsl & Hnn & Hdk1 & Hdk2 & HiW).
  pose proof (Z.div_mod n 8 ltac:(lia)) as DM. rewrite Hm8, Z.add_0_r in DM.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).

  assert (SRCW : forall E', eagree (s_next ss) E E' ->
            length vs = Z.to_nat (n / 8) /\ forall j, (j < Z.to_nat (n / 8))%nat -> exists bs,
              rdn asegs base (Z_to_bv 64 (uE E XSP + sk + 8 * Z.of_nat j)) 8 = Some bs /\ length bs = 8%nat /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E' (nth j vs (ELit 0))).
  { intros E' HAE. destruct (CIA_same_ms E E' m0 base ss ms R F fc Hms (HC E' HAE)) as (HR' & HLF' & HK' & _).
    destruct (read_words_sound asegs E' base ss XSP sk _ vs HRDW HLF' HK') as [Hlen Hrd]. split; [exact Hlen|].
    intros j Hj. destruct (Hrd j Hj) as (bs & Hbs & Hbl & Hbv). exists bs. split; [| split; [exact Hbl| exact Hbv]].
    rewrite HL in Hbs. cbn [mem_denot] in Hbs. rewrite <- Hbs. f_equal. f_equal.
    rewrite <- (uE_eagree E E' XSP ltac:(eapply eagree_le; [exact HAE| unfold FPB; lia]) XSP_lt). unfold uE. lia. }
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HA, HST. unfold MS in HMI, HWM, HA, HST. cbn [ms_mem] in HMI, HWM, HA, HST.
  pose proof (sp_off_val E ss R spoff HSO HR HFR HG ltac:(lia)) as U2.
  assert (U10 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = uE E XSP + dk).
  { rewrite (regs_val E _ R (Z_to_bv 5 10) HR HFR). apply (xsp_arg_val E _ dk Hsl HG); lia. }
  assert (U11 : bv_unsigned (reg_get R (Z_to_bv 5 11)) = uE E XSP + sk).
  { rewrite (regs_val E _ R (Z_to_bv 5 11) HR HFR). apply (xsp_arg_val E _ sk Hsl1 HG); lia. }
  assert (V12 : reg_get R (Z_to_bv 5 12) = Z_to_bv 64 n).
  { change (reg_get R (Z_to_bv 5 12)) with (getr R (Z_to_bv 5 12)). exact (getr_lit E _ R _ _ HR H12). }
  assert (V1 : reg_get R (Z_to_bv 5 1) = Z_to_bv 64 ra).
  { change (reg_get R (Z_to_bv 5 1)) with (getr R (Z_to_bv 5 1)). exact (getr_lit E _ R _ _ HR H1). }
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  destruct (mkR_sel x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (Q1 & Q2 & Q4 & Q10 & Q11 & Q12).
  rewrite Q1 in V1. rewrite Q2 in U2. rewrite Q10 in U10. rewrite Q11 in U11. rewrite Q12 in V12. subst x1 x12.
  set (d := uE E XSP + dk) in *. set (sa := uE E XSP + sk) in *. set (usp := uE E XSP + spoff) in *.

  destruct (SRCW E (eagree_refl _ _)) as [Hlen HRDS].
  destruct (readable_bytes asegs base sa (Z.to_nat n) ltac:(unfold sa, RT_STACK in *; lia) ltac:(unfold sa, USTACK_TOP in *; lia)) as (src & Hsl' & Hsb).
  { intros x Hx. set (j := Z.to_nat ((bv_unsigned x - sa) / 8)).
    assert (Hj : (j < Z.to_nat (n / 8))%nat).
    { subst j. apply Z2Nat.inj_lt; [apply Z.div_pos; lia| lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
    destruct (HRDS j Hj) as (bs & Hbs & _ & _).
    apply (rdn_defined_at asegs base _ 8 bs Hbs x). rewrite u_small; [| unfold sa, USTACK_TOP, RT_STACK in *; lia]. subst j. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (bv_unsigned x - sa) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned x - sa) 8 ltac:(lia)). rewrite Z.mod_eq in H0 by lia. lia. }

  assert (CS : checked_src RT Σ base x2 lo sa (Z.of_nat (length src))).
  { rewrite Hsl'. rewrite Z2Nat.id by lia. split.
    - intros _. split; [apply (af_acc_stack RT AF Σ base sa n HA); unfold sa, RT_STACK in *; lia|].
      right; right; left. unfold sa, USTACK_TOP, RT_STACK in *. lia.
    - right. rewrite U2. unfold usp, sa. lia. }
  assert (CD : checked_dst RT Σ base x2 d (Z.of_nat (length src))).
  { rewrite Hsl'. rewrite Z2Nat.id by lia. split; [| split].
    - intros _. split; [apply (af_acc_stack RT AF Σ base d n HA); unfold d, RT_STACK in *; lia|].
      right; right; left. unfold d, USTACK_TOP, RT_STACK in *. lia.
    - intros i Hi. left. rewrite U2. unfold usp, d, USTACK_TOP, RT_STACK in *. lia.
    - apply (stk_wr_at base lo _ d n HST); unfold d, RT_STACK in *; lia. }
  assert (COK : call_ok RT Σ base x2 lo).
  { split; [| split; [| split; [| split]]]; rewrite ?U2.
    - apply (proj1 (stk_split asegs base lo usp _ HST ltac:(unfold usp, RT_STACK in *; lia))).
    - lia. - unfold usp, RT_STACK in *; lia. - unfold usp, USTACK_TOP in *; lia.
    - subst usp. rewrite Z.add_mod, G8, Hspm by lia. reflexivity. }
  pose proof (Hcpy Σ PMc (Z_to_bv 64 ra) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F fc base d sa src lo FDO MST (wz_of_u _ _ U10) (wz_of_u _ _ U11) ltac:(rewrite Hsl', Z2Nat.id by lia; reflexivity)
                ltac:(unfold d, USTACK_TOP, RT_STACK in *; lia) ltac:(unfold sa, USTACK_TOP, RT_STACK in *; lia) ltac:(rewrite Hsl', Z2Nat.id by lia; lia)
                Hsb CS CD ltac:(rewrite Hsl', Z2Nat.id by lia; unfold d, sa; lia) HA HMI COK) as HCPS.
  unfold entry_st in HCPS. rewrite <- HPC in HCPS. rewrite Hms.
  apply (aevt_call K _ _ HCPS). intros c HQ. unfold icpt_postF in HQ. eexists. split; [exact HQ|].
  intros ms' (m' & RS & (HA' & HMI' & HWM' & HST') & PR & BY).
  destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->).
  rewrite U2 in HST', PR. rewrite <- (wz_of_u x10 d U10). rewrite Hsl', Z2Nat.id in PR by lia.
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  apply (HK (eupds E (s_next ss) vals) m'); [apply eupds_agree| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| lia]. }
  assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
  destruct (CIA_same_ms E E'' m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  pose proof (uE_eagree E E'' XSP HAF XSP_lt) as EX.
  destruct (SRCW E'' HAE) as [_ HRDSj].
  exists (mkR (Z_to_bv 64 ra) x2 x3 x4 t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F'.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split. { pose proof (mod4_mod2 ra Hra4) as M2. rewrite ret_pc_even by (unfold two64 in Hra; lia). unfold retZ.
           replace (ra - ra mod 2) with ra by lia. reflexivity. }
  split. { rewrite <- (regupds_CLOB (Z_to_bv 64 ra) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
           apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
           intros j Hj. pose proof (proj1 HA'' (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj. }
  split; [exact I|].
  split. { apply know_ok_app2.
    - apply kwords8_ok.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. unfold d, RT_STACK in *; lia.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX, Hlen, Z2Nat.id by lia. unfold d, usp, USTACK_TOP, RT_STACK in *; lia.
      + intros j Hj. rewrite Hlen in Hj. change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX.

        pose proof (Mem.bytes_at_rdn asegs m' _ src (8 * j) 8 BY ltac:(rewrite Hsl'; lia)) as X. rewrite rdn_common in X. unfold wa in X.
        replace (uE E XSP + dk + 8 * Z.of_nat j) with (d + Z.of_nat (8 * j)) by (unfold d; lia). rewrite X. f_equal.
        pose proof (Mem.bytes_at_rdn asegs base _ src (8 * j) 8 Hsb ltac:(rewrite Hsl'; lia)) as Y. rewrite rdn_common in Y. unfold wa in Y.
        destruct (HRDSj j Hj) as (bs & Hbs & Hbl & Hbv).
        replace (sa + 8 * Z.of_nat j) with (sa + Z.of_nat (8 * j)) in Hbs by lia.
        rewrite Y in Hbs. assert (EQ : firstn 8 (skipn (8 * j) src) = bs) by congruence. rewrite EQ. symmetry. apply le8_of_rdn_val; [exact Hbl| exact Hbv].
    - apply (keepI_sound E'' (mpatch base m' d n) m' spoff ss).
      + intros K0 HIn Hkp. pose proof (proj1 (Forall_forall _ _) HK'' K0 HIn) as HK1.
        eapply (kkeep_sound asegs E'' base (mpatch base m' d n) (facts_of (s_know ss)) XSP dk n K0 (facts_of_ok _ _ _ _ HK'') HK1 Hkp);
          [lia| unfold two64; lia| | apply mpatch_wmono1; exact HWM'].
        intros x Hx. apply mpatch_out. change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP) in Hx. rewrite EX in Hx. exact Hx.
      + intros x Hw. destruct (Z.lt_ge_cases (bv_unsigned x) d) as [L|L]; [| destruct (Z.lt_ge_cases (bv_unsigned x) (d + n)) as [L2|L2]].
        * rewrite mpatch_out by lia. apply PR; [| lia]. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
        * rewrite mpatch_in by lia. reflexivity.
        * rewrite mpatch_out by lia. apply PR; [| lia]. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
      + apply mpatch_wmono2. exact HWM'.
      + exact HMI'.
      + exact HA'. }
  split; [apply fullR_mkR|]. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hcx Hw. rewrite EX in Hcx. rewrite PR.
           - apply HB''; [rewrite EX; exact Hcx| exact Hw].
           - apply (aclient_anchor E usp x HG); [unfold usp; lia| exact Hcx|]. intros Hw'. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF| exact Hw'].
           - intros Hd. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF|]. apply (dst_in_W E dk n x HiW). unfold d in Hd. lia. }
  split; [reflexivity|]. split; [exact HG''|]. split; [exact HA'|].
  rewrite EX. apply (stk_after_call E base m' spoff d n _ HG ltac:(lia) HST HST' HWM' PR BY). rewrite Hsl'. lia.
Qed.

Lemma kn_has_word_sound : forall E (M : mem) kn a w v,
  know_ok asegs E M kn -> kn_has_word kn a w v = true ->
  rdn asegs M (adenot E a) w = Some (word_to_le_bytes w (edenot E v)) /\ flat E a (Z.of_nat w) /\ (w <= 8)%nat.
Proof.
  intros E M kn a w v HK H. unfold kn_has_word in H. apply existsb_exists in H as (K0 & HIn & HK1).
  destruct K0 as [a' w' v'| | | | | | | | |]; try discriminate.
  apply andb_prop in HK1 as [HK1 H3]. apply andb_prop in HK1 as [H1 H2].
  unfold saddr_eqb in H1. destruct a as [b k], a' as [b' k']. cbn [a_base a_off] in H1. apply andb_prop in H1 as [H1a H1b].
  apply expr_eqb_eq in H1a. apply Z.eqb_eq in H1b. apply Nat.eqb_eq in H2. apply expr_eqb_eq in H3. subst b' k' w' v'.
  unfold know_ok in HK. rewrite Forall_forall in HK. specialize (HK _ HIn). cbn [kentry_ok] in HK. destruct HK as (Hw & Hfl & Hrd).
  split; [exact Hrd|]. split; [exact Hfl| exact Hw].
Qed.

Lemma regupd_10 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
  regupds (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) [10%nat] [v]
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma mod8_add : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.
Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. assert (E0 : a = (2 * (a / 16)) * 8) by (pose proof (Z.div_mod a 16 ltac:(lia)); lia).
  rewrite E0 at 1. apply Z.mod_mul. lia.
Qed.

Lemma rw_cells_2x8 : forall (M : mem) p (w1 w2 : word),
  rdn asegs M (Z_to_bv 64 p) 8 = Some (word_to_le_bytes 8 w1) -> rdn asegs M (Z_to_bv 64 (p + 8)) 8 = Some (word_to_le_bytes 8 w2) ->
  0 <= p -> p + 16 <= 2 ^ 64 -> wr_at asegs M p 16 -> rw_cells asegs M p [C8 w1; C8 w2].
Proof.
  intros M p w1 w2 H1 H2 Hp Hh HWR. split; [split; [cbn; tauto|]| exact HWR]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply (proj2 (Mem.bytes_at_app asegs M _ _ _)). split.
  - apply (bytes_at_of_rdnG 8); try lia. rewrite rdn_common. unfold wa. exact H1.
  - rewrite Mem.length_le8. apply (bytes_at_of_rdnG 8); try lia. rewrite rdn_common. unfold wa. replace (p + Z.of_nat 8) with (p + 8) by lia. exact H2.
Qed.

Theorem nodeA_itls_sound : forall fc ss ss' E m0 base ms,
  node_itls ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_itls in Hn.
  destruct (igate TLSPC ss) as [[ra spoff]|] eqn:Hg; [|discriminate].
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [pb pk] eqn:Hsl.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. apply Some_inj in Hn. subst ss'.
  apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc Hpm].
  apply andb_prop in Hc as [Hc Hpk2]. apply andb_prop in Hc as [Hpb Hpk1].
  apply expr_eqb_eq in Hpb. apply Z.leb_le in Hpk1. apply Z.leb_le in Hpk2. apply Z.eqb_eq in Hpm. apply expr_eqb_eq in H4. subst pb.
  destruct (igate_sound TLSPC ss ra spoff Hg) as (HL & HPC & H1 & HSO & Hra & Hra4 & Hspo & Hspm).
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HA, HST. unfold MS in HMI, HWM, HA, HST. cbn [ms_mem] in HMI, HWM, HA, HST.
  pose proof (sp_off_val E ss R spoff HSO HR HFR HG ltac:(lia)) as U2.
  assert (U10 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = uE E XSP + pk).
  { rewrite (regs_val E _ R (Z_to_bv 5 10) HR HFR). apply (xsp_arg_val E _ pk Hsl HG); lia. }
  assert (V4 : reg_get R (Z_to_bv 5 4) = Z_to_bv 64 TPV).
  { change (reg_get R (Z_to_bv 5 4)) with (getr R (Z_to_bv 5 4)). exact (getr_lit E _ R _ _ HR H4). }
  assert (V1 : reg_get R (Z_to_bv 5 1) = Z_to_bv 64 ra).
  { change (reg_get R (Z_to_bv 5 1)) with (getr R (Z_to_bv 5 1)). exact (getr_lit E _ R _ _ HR H1). }

  destruct (kn_has_word_sound E base (s_know ss) _ _ _ HK0 Hk1) as (RD1 & FL1 & _).
  destruct (kn_has_word_sound E base (s_know ss) _ _ _ HK0 Hk2) as (RD2 & FL2 & _).
  rewrite adenot_SA in RD1, RD2. cbn [edenot] in RD1, RD2.
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  destruct (mkR_sel x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (Q1 & Q2 & Q4 & Q10 & Q11 & Q12).
  rewrite Q1 in V1. rewrite Q2 in U2. rewrite Q10 in U10. rewrite Q4 in V4. subst x1 x4.
  set (p := uE E XSP + pk) in *. set (usp := uE E XSP + spoff) in *.
  assert (RWP : rw_cells asegs base p [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)]).
  { apply rw_cells_2x8; [exact RD1| | unfold p, RT_STACK in *; lia| unfold p, USTACK_TOP in *; lia| apply (stk_wr_at base lo _ p 16 HST); unfold p, RT_STACK in *; lia].
    replace (p + 8) with (bv_unsigned (edenot E XSP) + (pk + 8)) by (unfold p, uE; lia). exact RD2. }
  assert (COK : call_ok RT Σ base x2 lo).
  { split; [| split; [| split; [| split]]]; rewrite ?U2.
    - apply (proj1 (stk_split asegs base lo usp _ HST ltac:(unfold usp, RT_STACK in *; lia))).
    - lia. - unfold usp, RT_STACK in *; lia. - unfold usp, USTACK_TOP in *; lia.
    - subst usp. rewrite Z.add_mod, G8, Hspm by lia. reflexivity. }
  pose proof (Htls Σ PMc (Z_to_bv 64 ra) x2 x3 (Z_to_bv 64 TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F fc base p lo FDO MST (wz_of_u _ _ U10) eq_refl ltac:(unfold p, RT_STACK in *; lia)
                ltac:(unfold p; apply mod8_add; [apply mod16_mod8; exact G8| exact Hpm])
                ltac:(rewrite U2; unfold usp, p; lia) ltac:(unfold p, USTACK_TOP in *; lia) RWP HA HMI COK) as HCPS.
  unfold entry_st in HCPS. rewrite <- HPC in HCPS. rewrite Hms.
  apply (aevt_call K _ _ HCPS). intros c [v HQ]. unfold icpt_postF in HQ. eexists. split; [exact HQ|].
  intros ms' (m' & RS & (HA' & HMI' & HWM' & HST') & PR & _).
  destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & ->).
  rewrite U2 in HST', PR.
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  apply (HK (eupds (eupds E (s_next ss) vals) (s_next ss + 14)%nat [v]) m');
    [eapply eagree_trans; [apply eupds_agree| eapply eagree_le; [apply eupds_agree| lia]]| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE14 : eagree (s_next ss + 14)%nat (eupds E (s_next ss) vals) E'').
  { eapply eagree_trans; [apply (eupds_agree [v])|]. eapply eagree_le; [exact HA''| lia]. }
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HAE14| lia]. }
  assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
  destruct (CIA_same_ms E E'' m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  pose proof (uE_eagree E E'' XSP HAF XSP_lt) as EX.
  exists (mkR (Z_to_bv 64 ra) x2 x3 (Z_to_bv 64 TPV) t0' t1' t2' x8 x9 v a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F'.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split. { pose proof (mod4_mod2 ra Hra4) as M2. rewrite ret_pc_even by (unfold two64 in Hra; lia). unfold retZ.
           replace (ra - ra mod 2) with ra by lia. reflexivity. }
  split. { rewrite <- (regupd_10 (Z_to_bv 64 ra) x2 x3 (Z_to_bv 64 TPV) t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' v).
           rewrite <- (regupds_CLOB (Z_to_bv 64 ra) x2 x3 (Z_to_bv 64 TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
           apply havoc_regs_ok; [| reflexivity| intros r [<-|[]]; lia|].
           - apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
             intros j Hj. pose proof (proj1 HAE14 (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj.
           - intros j Hj. cbn in Hj. destruct j; [| lia]. rewrite Nat.add_0_r.
             pose proof (proj1 HA'' (s_next ss + 14)%nat ltac:(lia)) as X. rewrite <- X.
             pose proof (eupds_at [v] (eupds E (s_next ss) vals) (s_next ss + 14)%nat 0%nat ltac:(cbn; lia)) as Y. rewrite Nat.add_0_r in Y. exact Y. }
  split; [exact I|].
  split. { apply (keepI_sound E'' base m' spoff ss).
    - intros K0 HIn _. exact (proj1 (Forall_forall _ _) HK'' K0 HIn).
    - intros x Hw. apply PR; [| lia]. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
    - exact HWM'.
    - exact HMI'.
    - exact HA'. }
  split; [apply fullR_mkR|]. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hcx Hw. rewrite EX in Hcx. rewrite PR.
           - apply HB''; [rewrite EX; exact Hcx| exact Hw].
           - apply (aclient_anchor E usp x HG); [unfold usp; lia| exact Hcx|]. intros Hw'. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF| exact Hw'].
           - lia. }
  split; [reflexivity|]. split; [exact HG''|]. split; [exact HA'|].
  rewrite EX. apply (stk_after_call E base m' spoff 0 0 [] HG ltac:(lia) HST HST' HWM' PR); [| reflexivity].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Theorem nodeA_unw_sound : forall fc ss ss' E m0 base ms,
  node_unw ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_unw in Hn.
  destruct (s_log ss) eqn:HL; [|discriminate]. destruct (sp_off ss) as [spoff|] eqn:HSO; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. apply Some_inj in Hn. subst ss'.
  apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc Hspo2]. apply andb_prop in Hc as [Hc Hspm]. apply andb_prop in Hc as [HPC Hspo1].
  apply Z.eqb_eq in HPC. apply Z.leb_le in Hspo1. apply Z.eqb_eq in Hspm. apply Z.leb_le in Hspo2. apply expr_eqb_eq in H4.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HA, HST. unfold MS in HMI, HWM, HA, HST. cbn [ms_mem] in HMI, HWM, HA, HST.
  pose proof (sp_off_val E ss R spoff HSO HR HFR HG ltac:(lia)) as U2.
  assert (V4 : reg_get R (Z_to_bv 5 4) = Z_to_bv 64 TPV).
  { change (reg_get R (Z_to_bv 5 4)) with (getr R (Z_to_bv 5 4)). exact (getr_lit E _ R _ _ HR H4). }
  destruct HFR as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                   x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ER). subst R.
  destruct (mkR_sel x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as (Q1 & Q2 & Q4 & Q10 & Q11 & Q12).
  rewrite Q2 in U2. rewrite Q4 in V4. subst x4.
  set (usp := uE E XSP + spoff) in *.
  assert (COK : call_ok RT Σ base x2 lo).
  { split; [| split; [| split; [| split]]]; rewrite ?U2.
    - apply (proj1 (stk_split asegs base lo usp _ HST ltac:(unfold usp, RT_STACK in *; lia))).
    - lia. - unfold usp, RT_STACK in *; lia. - unfold usp, USTACK_TOP in *; lia.
    - subst usp. rewrite Z.add_mod, G8, Hspm by lia. reflexivity. }
  pose proof (Hunw Σ PMc x1 x2 x3 (Z_to_bv 64 TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                F fc base lo FDO MST eq_refl HA HMI COK ltac:(rewrite U2; unfold usp in *; lia) ltac:(rewrite U2; unfold usp in *; lia)) as HCPS.
  unfold entry_st in HCPS. rewrite <- HPC in HCPS. rewrite Hms.
  apply (aevt_call K _ _ HCPS). intros c HQ. eexists. split; [exact HQ|].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HA' & HMI' & HWM' & HST' & PR).
  rewrite U2 in HST', PR.
  set (vals := [t0'; t1'; t2'; a1'; a2'; a3'; a4'; a5'; a6'; a7'; t3'; t4'; t5'; t6']).
  apply (HK (eupds E (s_next ss) vals) m'); [apply eupds_agree| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| lia]. }
  assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
  destruct (CIA_same_ms E E'' m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  pose proof (uE_eagree E E'' XSP HAF XSP_lt) as EX.
  exists (mkR x1 x2 x3 (Z_to_bv 64 TPV) t0' t1' t2' x8 x9 x10 a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6'), F.
  cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split; [reflexivity|].
  split. { rewrite <- (regupds_CLOB x1 x2 x3 (Z_to_bv 64 TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
           apply havoc_regs_ok; [exact HR''| reflexivity| apply CLOB_range|].
           intros j Hj. pose proof (proj1 HA'' (s_next ss + j)%nat ltac:(cbn in Hj; lia)) as X. rewrite <- X. apply eupds_at. exact Hj. }
  split; [exact I|].
  split. { apply (keepI_sound E'' base m' spoff ss).
    - intros K0 HIn _. exact (proj1 (Forall_forall _ _) HK'' K0 HIn).
    - intros x Hw. apply PR. unfold usp. rewrite <- EX. apply (cws_client E'' spoff x HG'' ltac:(lia) Hw).
    - exact HWM'.
    - exact HMI'.
    - exact HA'. }
  split; [apply fullR_mkR|]. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hcx Hw. rewrite EX in Hcx. rewrite PR.
           - apply HB''; [rewrite EX; exact Hcx| exact Hw].
           - apply (aclient_anchor E usp x HG); [unfold usp; lia| exact Hcx|]. intros Hw'. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF| exact Hw']. }
  split; [reflexivity|]. split; [exact HG''|]. split; [exact HA'|].
  rewrite EX. apply (stk_after_call E base m' spoff 0 0 [] HG ltac:(lia) HST HST' HWM'); [| | reflexivity].
  - intros a Ha _. apply PR. exact Ha.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Lemma kfpv_ok : forall E (M : mem) b k nx cnt (ws : list word),
  length ws = cnt ->
  0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + 8 * Z.of_nat cnt <= 2 ^ 64 ->
  (forall j, (j < cnt)%nat -> ev E (nx + j)%nat = nth j ws (Z_to_bv 64 0)) ->
  (forall j, (j < cnt)%nat -> rdn asegs M (Z_to_bv 64 (bv_unsigned (edenot E b) + k + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (nth j ws (Z_to_bv 64 0)))) ->
  know_ok asegs E M (kfpv b k nx cnt).
Proof.
  intros E M b k nx cnt. revert k nx. induction cnt as [|c IH]; intros k nx ws Hlen Hlo Hhi Hev Hrd; [constructor|].
  cbn [kfpv]. constructor.
  - cbn [kentry_ok]. split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    rewrite adenot_SA. specialize (Hrd 0%nat ltac:(lia)). rewrite Z.mul_0_r, Z.add_0_r in Hrd. rewrite Hrd.
    f_equal. cbn [edenot]. rewrite <- (Hev 0%nat ltac:(lia)). rewrite Nat.add_0_r. reflexivity.
  - destruct ws as [|w ws']; [cbn in Hlen; lia|].
    apply (IH (k + 8) (S nx) ws'); [cbn in Hlen; lia| lia| lia| |].
    + intros j Hj. replace (S nx + j)%nat with (nx + S j)%nat by lia. rewrite (Hev (S j)) by lia. reflexivity.
    + intros j Hj. replace (bv_unsigned (edenot E b) + (k + 8) + 8 * Z.of_nat j) with (bv_unsigned (edenot E b) + k + 8 * Z.of_nat (S j)) by lia.
      rewrite (Hrd (S j)) by lia. reflexivity.
Qed.

Theorem nodeA_fsd_sound : forall fc ss ss' E m0 base ms,
  node_fsdA ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_fsdA in Hn.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db dk] eqn:Hsl.
  destruct (s_log ss) eqn:HL; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. apply Some_inj in Hn. subst ss'.
  apply andb_prop in Hc as [Hc HiW]. apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply andb_prop in Hc as [HPC Hdb].
  apply Z.eqb_eq in HPC. apply expr_eqb_eq in Hdb. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. subst db.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  rewrite HL in Hms. cbn [mem_denot] in Hms. rewrite Hms in HMI, HWM, HA, HST. unfold MS in HMI, HWM, HA, HST. cbn [ms_mem] in HMI, HWM, HA, HST.
  assert (U10 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = uE E XSP + dk).
  { rewrite (regs_val E _ R (Z_to_bv 5 10) HR HFR). rewrite (split_lit_val E _ XSP dk Hsl). unfold uE.
    apply Z.mod_small. unfold two64. pose proof (u64_range (edenot E XSP)). unfold uE, USTACK_TOP, RT_STACK in *. lia. }
  set (d := uE E XSP + dk) in *.
  destruct (stk_carve asegs base lo (d + 512) 256 ltac:(apply (proj1 (stk_split asegs base lo (d + 512) _ HST ltac:(unfold d, RT_STACK in *; lia))))
              ltac:(unfold d, RT_STACK in *; lia)) as [_ [junk RWC]].
  replace (d + 512 - Z.of_nat 256) with (bv_unsigned (reg_get R (Z_to_bv 5 10)) + 256) in RWC by lia.
  pose proof (Hfsd R F fc base junk HFR RWC ltac:(unfold d, USTACK_TOP in *; lia) HMI) as EV.
  destruct EV as (ms1 & HMS & m' & -> & MU & HWM' & HMI' & HRD).
  rewrite U10 in MU, HRD. rewrite Hms, HPC. apply (aevt_msteps K _ _ HMS).
  set (vals := map (fun i => reg_get F (Z_to_bv 5 (Z.of_nat i))) (seq 0 32)).
  apply (HK (eupds E (s_next ss) vals) m'); [apply eupds_agree| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  assert (HAE : eagree (s_next ss) E E'').
  { eapply eagree_trans; [apply (eupds_agree vals)|]. eapply eagree_le; [exact HA''| cbn; lia]. }
  assert (HAF : eagree FPB E E'') by (eapply eagree_le; [exact HAE| unfold FPB; lia]).
  destruct (CIA_same_ms E E'' m0 base ss ms _ F fc ltac:(rewrite HL; exact Hms) (HC E'' HAE)) as (HR'' & HLF'' & HK'' & EM & HB'' & HG'').
  pose proof (uE_eagree E E'' XSP HAF XSP_lt) as EX.
  assert (OUT : forall x : word, ~ (d + 256 <= bv_unsigned x < d + 256 + 256) -> m' x = base x).
  { intros x Hx. apply MU. cbn [outside]. split; [| exact I]. lia. }
  exists R, F. cbn [s_pc s_regs s_log s_know s_next mem_denot].
  split; [reflexivity|]. split; [exact HR''|]. split; [exact I|].
  split. { apply know_ok_app2.
    - apply (kfpv_ok E'' m' XSP (dk + 256) (s_next ss) 32 vals); [reflexivity| | | |].
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. unfold d, RT_STACK in *; lia.
      + change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX. unfold d, USTACK_TOP in *; lia.
      + intros j Hj. rewrite <- (proj1 HA'' (s_next ss + j)%nat ltac:(lia)). apply eupds_at. cbn. exact Hj.
      + intros j Hj. change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP). rewrite EX.
        replace (uE E XSP + (dk + 256) + 8 * Z.of_nat j) with (d + 256 + 8 * Z.of_nat j) by (unfold d; lia). rewrite (HRD j Hj).
        f_equal. unfold fle8, vals. f_equal. symmetry.
        rewrite (nth_indep _ (Z_to_bv 64 0) ((fun i => reg_get F (Z_to_bv 5 (Z.of_nat i))) 0%nat)) by (rewrite length_map, length_seq; exact Hj).
        rewrite (map_nth (fun i => reg_get F (Z_to_bv 5 (Z.of_nat i)))). rewrite seq_nth by exact Hj. reflexivity.
    - eapply kkeep_filter_sound; [exact HK''| lia| unfold two64; lia| | exact HWM'].
      intros x Hx. apply OUT. change (bv_unsigned (edenot E'' XSP)) with (uE E'' XSP) in Hx. rewrite EX in Hx. unfold d. lia. }
  split; [exact HFR|]. unfold MS. cbn [ms_mem].
  split; [exact HMI'|]. split; [eapply wmono_trans; [exact HWM| exact HWM']|].
  split. { intros x Hcx Hw. rewrite OUT; [apply HB''; assumption|]. intros Hd. apply Hw. apply (Wd_eagree E E''); [exact HW| exact HAF|].
           eapply in_W_Wd; [exact HiW|]. unfold d, uE in *. lia. }
  split; [reflexivity|]. split; [exact HG''|].
  split. { apply (af_frame RT AF Σ _ _ (uE E XSP + SPLO) HA); [unfold RT_STACK in *; lia| | exact HWM'].
           intros a Ha. apply OUT. intros Hd. apply Ha. apply (GW _ a (Z.le_refl _)). eapply in_W_Wd; [exact HiW|]. unfold d, uE in *. lia. }
  rewrite EX. apply (stk_pres base m' _ _ HST HWM'). intros a Ha.
  destruct (Z.lt_ge_cases a (d + 256)) as [L|L]; [| destruct (Z.lt_ge_cases a (d + 512)) as [L2|L2]].
  - left. apply OUT. unfold wa. rewrite u_small by (unfold USTACK_TOP, RT_STACK in *; lia). lia.
  - right. set (j := Z.to_nat ((a - (d + 256)) / 8)).
    assert (Hj : (j < 32)%nat) by (subst j; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia).
    apply (rdn_defined_at asegs m' _ 8 _ (HRD j Hj) (wa a)). unfold wa. rewrite !u_small by (unfold USTACK_TOP, RT_STACK in *; lia).
    subst j. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.mul_div_le (a - (d + 256)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a - (d + 256)) 8 ltac:(lia)). rewrite Z.mod_eq in H0 by lia. lia.
  - left. apply OUT. unfold wa. rewrite u_small by (unfold USTACK_TOP, RT_STACK in *; lia). lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with ((bytes_le_to_Z bs) mod 2^64)%Z.
  rewrite (Z_to_le_bytes_mod 8 _ 64) by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma words_of_bytes : forall (m : mem) A k, 0 <= A -> A + 8 * Z.of_nat k <= 2 ^ 64 ->
  (forall a, A <= a < A + 8 * Z.of_nat k -> exists b, mrd asegs m (wa a) = Some b) ->
  exists ws : list word, length ws = k /\ cells_at asegs m A (map (fun w => C8 w) ws).
Proof.
  intros m A k. revert A. induction k as [|k IH]; intros A HA Hh Hrd.
  - exists []. split; [reflexivity|]. split; [exact I|]. cbn. apply Mem.bytes_at_nil. lia.
  - destruct (readable_bytes asegs m A 8 HA ltac:(lia)) as (bs & Hl & Hb).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). apply Hrd. lia. }
    destruct (IH (A + 8) ltac:(lia) ltac:(lia)) as (ws & Hlen & [Hwf Hcs]); [intros a Ha; apply Hrd; lia|].
    exists (le_bytes_to_word bs :: ws). split; [cbn; lia|]. split; [split; [exact I| exact Hwf]|].
    cbn [map cells_bytes cbytes]. apply (proj2 (Mem.bytes_at_app asegs m _ _ _)). split.
    + rewrite le8_le_bytes_to_word by exact Hl. exact Hb.
    + rewrite Mem.length_le8. replace (A + Z.of_nat 8) with (A + 8) by lia. exact Hcs.
Qed.

Theorem nodeA_fld_sound : forall fc ss ss' E m0 base ms,
  node_fldA ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ss ss' E m0 base ms Hn [Hnx HC] K HK. unfold node_fldA in Hn.
  destruct (split_lit (sr_get (s_regs ss) (Z_to_bv 5 10))) as [db dk] eqn:Hsl.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. apply Some_inj in Hn. subst ss'.
  apply andb_prop in Hc as [Hc Hk2]. apply andb_prop in Hc as [Hc Hk1]. apply andb_prop in Hc as [HPC Hdb].
  apply Z.eqb_eq in HPC. apply expr_eqb_eq in Hdb. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. subst db.
  destruct (HC E (eagree_refl _ _)) as (R & F & Hms & HR & HLF & HK0 & HFR & HMI & HWM & HB & HLW & HG & HA & HST).
  pose proof HG as HG0. destruct HG0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GW).
  assert (U10 : bv_unsigned (reg_get R (Z_to_bv 5 10)) = uE E XSP + dk).
  { rewrite (regs_val E _ R (Z_to_bv 5 10) HR HFR). rewrite (split_lit_val E _ XSP dk Hsl). unfold uE.
    apply Z.mod_small. unfold two64. pose proof (u64_range (edenot E XSP)). unfold uE, USTACK_TOP, RT_STACK in *. lia. }
  set (d := uE E XSP + dk) in *. set (M := ms_mem ms) in *.
  assert (HSTM : stk asegs M lo (uE E XSP + SPTOP)) by exact HST.
  destruct (words_of_bytes M (d + 256) 32 ltac:(unfold d, RT_STACK in *; lia) ltac:(unfold d, USTACK_TOP in *; lia)) as (ws & Hlen & CS).
  { intros a Ha. destruct HSTM as (_ & _ & ST3). apply (proj2 (ST3 a ltac:(unfold d, RT_STACK in *; lia))). }
  rewrite <- U10 in CS.
  pose proof (Hfld R F fc M ws HFR Hlen ltac:(unfold d, USTACK_TOP in *; lia) CS) as EV.
  assert (EMS : ms = MS R F (Z_to_bv 64 FLDPC) fc None M rom) by (rewrite Hms at 1; rewrite HPC; unfold M; rewrite Hms; reflexivity).
  rewrite EMS. destruct EV as (ms1 & HMS & F' & ->). apply (aevt_msteps K _ _ HMS).
  apply (HK E base); [apply eagree_refl| cbn [s_next]; lia|].
  split; [cbn [s_next] in *; lia|]. intros E'' HA''. cbn [s_next] in HA''.
  destruct (HC E'' HA'') as (R2 & F2 & Hms2 & HR'' & HLF'' & HK'' & HFR'' & HMI'' & HWM'' & HB'' & HLW'' & HG'' & HART'' & HST'').
  rewrite Hms in Hms2. apply MS_inj in Hms2 as (<- & <- & _ & _ & EM).
  exists R, F'. cbn [s_pc s_regs s_log s_know s_next s_resv].
  rewrite Hms in HMI'', HWM'', HART'', HST''. unfold MS in HMI'', HWM'', HART'', HST''. cbn [ms_mem] in HMI'', HWM'', HART'', HST''.
  split; [unfold M; rewrite Hms; unfold MS; cbn [ms_mem]; rewrite EM; reflexivity|].
  split; [exact HR''|]. split; [exact HLF''|]. split; [exact HK''|]. split; [exact HFR|].
  unfold M. rewrite Hms. unfold MS. cbn [ms_mem].
  split; [exact HMI''|]. split; [exact HWM''|]. split; [exact HB''|]. split; [exact HLW''|]. split; [exact HG''|]. split; [exact HART''| exact HST''].
Qed.

Lemma obind_some' : forall x f y, obind x f = Some y -> exists z, x = Some z /\ f z = Some y.
Proof. intros [z|] f y H; cbn in H; [exists z; auto| discriminate]. Qed.

Theorem xautoA_sound : forall fc ENDPC fuel k ss ss' E m0 base ms,
  xautoA ENDPC fuel k ss = Some ss' -> CIXA fc E m0 base ss ms -> nodeA_ok fc ss ss' E m0 base ms.
Proof.
  intros fc ENDPC fuel k. induction k as [|k IH]; intros ss ss' E m0 base ms Hx HC; [discriminate|].
  cbn [xautoA] in Hx.
  destruct (node_run asegs t W fuel (STOPSA ENDPC) ss) as [ss1|] eqn:Hr; [|discriminate].
  eapply nodeA_ok_bind; [eapply nodeA_run_sound; eauto|]. intros E1 base1 ms1 _ HC1.
  destruct (Z.eqb (s_pc ss1) ENDPC).
  { eapply nodeA_flush_sound; eauto. }
  destruct (Z.eqb (s_pc ss1) FLDPC).
  { apply obind_some' in Hx as (ss2 & H2 & Hx). eapply nodeA_ok_bind; [eapply nodeA_fld_sound; eauto|].
    intros E2 base2 ms2 _ HC2. eapply IH; eauto. }
  apply obind_some' in Hx as (ss3 & H3 & Hx). apply obind_some' in H3 as (ss2 & H2 & H3).
  eapply nodeA_ok_bind; [eapply nodeA_flush_sound; eauto|]. intros E2 base2 ms2 _ HC2.
  eapply nodeA_ok_bind.
  { unfold gc_sp in H3. destruct (split_lit (sr_get (s_regs ss2) (Z_to_bv 5 2))) as [b kk]. eapply nodeA_drop_sound; eauto. }
  intros E3 base3 ms3 _ HC3.
  apply obind_some' in Hx as (ss4 & H4 & Hx).
  eapply nodeA_ok_bind; [| intros E4 base4 ms4 _ HC4; eapply IH; eauto].
  destruct (Z.eqb (s_pc ss1) SETPC); [eapply nodeA_iset_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) CPYPC); [eapply nodeA_icpy_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) TLSPC); [eapply nodeA_itls_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) UNWPC); [eapply nodeA_unw_sound; eauto|].
  destruct (Z.eqb (s_pc ss1) FSDPC); [eapply nodeA_fsd_sound; eauto| discriminate].
Qed.

End CoreA.
