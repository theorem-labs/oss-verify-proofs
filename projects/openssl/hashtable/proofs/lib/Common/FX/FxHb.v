(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg MiscCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxRun FxRn FxSys FxMisc FxDrive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tree_all (p : fstate -> stop -> bool) (t : dtree) : bool :=
  match t with
  | DLeaf F _ _ r => p F r
  | DFork t1 t2 => tree_all p t1 && tree_all p t2
  end.

Lemma tree_all_leaf p t F L n r :
  tree_all p t = true -> leaf_in (F, L, n, r) t -> p F r = true.
Proof.
  induction t as [F0 L0 n0 r0 | t1 IH1 t2 IH2]; cbn [tree_all leaf_in]; intros H Hin.
  - injection Hin as -> -> -> ->. exact H.
  - apply andb_true_iff in H as [H1 H2]. destruct Hin as [Hin|Hin]; [apply IH1 | apply IH2]; assumption.
Qed.

Definition leaf_openat_err (IM : fimage) (F : fstate) (r : stop) : bool :=
  match r with
  | SEcall =>
      match FxState.rget F 17%uint63, FxState.rget F 10%uint63, FxState.rget F 12%uint63,
            FxState.rget F 11%uint63 with
      | FV t7 w7, FV t0 w0', FV t2 w2, FV t (W64 top off) =>
          (t7 =? 0)%uint63 && w_eqb w7 (w_of_int 56)
          && (t0 =? 0)%uint63 && w_eqb (w_zext32 w0') (w_of_int 4294967196)
          && (t2 =? 0)%uint63 && modeled_open_flags (wbv w2)
          && (top =? 0)%uint63
          && match fx_cstring IM (f_mem F) t off with
             | Some l => path_has_slash (bytes_of l)
                         && negb (path_eqb (bytes_of l) localtime_path)
                         && negb (path_eqb (bytes_of l) devnull_path)
                         && negb (path_eqb (bytes_of l) urandom_path)   (* [comment removed for export] *)
                         && match tmp_name (bytes_of l) with None => true | Some _ => false end
             | None => false
             end
      end
  | _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rom.
Variable segs : list Segment.

Lemma decode_exec_rom st w st' :
  drop_access_report (decode_exec_accesses segs st w) = MachineOk st' -> ms_rom st' = ms_rom st.
Proof.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - cbn [drop_access_report]. intros H. injection H as <-. reflexivity.
  - destruct (decode_any w) as [[i isz]|].
    + destruct (interp_eff_accesses _ _ _) as [[[c m'] acc]| |]; cbn [drop_access_report]; try discriminate.
      cbn. intros H. injection H as <-. reflexivity.
    + destruct (is_defined_illegal w); discriminate.
Qed.

Lemma step_rom st st' : RiscvSemantics.step segs st = MachineOk st' -> ms_rom st' = ms_rom st.
Proof.
  unfold RiscvSemantics.step, step_accesses.
  destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_rom|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_rom|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_rom|].
  unfold fetch_failure.
  destruct (negb _); [discriminate|]. cbv zeta. destruct (_ || _ || _)%bool; discriminate.
Qed.

Lemma rsteps_rom : forall n ms ms', rsteps segs n ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  induction n as [|n IH]; intros ms ms' H; cbn [rsteps] in H.
  - injection H as <-. reflexivity.
  - destruct (ms_svc_pending ms); [injection H as <-; reflexivity|].
    destruct (RiscvSemantics.step segs ms) as [ms1| |] eqn:E; try discriminate.
    rewrite (IH _ _ H). exact (step_rom _ _ E).
Qed.

Variable cfg : SpuriousCfg.

Lemma apply_effect_rom ms eff : ms_rom (advance_past_svc (apply_effect ms eff)) = ms_rom ms.
Proof. reflexivity. Qed.

Lemma sstep_cfg_rom c e c' :
  sstep_cfg segs cfg c e (SNext c') -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  intros H. inversion H; subst; cbn [cfg_ms]; try reflexivity.
  - match goal with Hs : mi_account_step _ _ _ = MachineOk _ |- _ =>
      apply mi_account_step_projects in Hs; exact (step_rom _ _ Hs) end.
Qed.

Lemma star_cfg_rom c tr c' :
  star_cfg segs cfg c tr c' -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  induction 1 as [c | c1 evs c2 tr c3 Hs _ IH]; [reflexivity|].
  rewrite IH. exact (sstep_cfg_rom _ _ _ Hs).
Qed.
End Rom.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Hb.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable rl : role.
Variable keep : list int.
Variable mem0 : word -> option byte.
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Variable xsys : fstate -> fledger -> int -> option dres.
Hypothesis xsys_sound : forall n rho F L ms m res,
  xsys F L n = Some res -> DInv cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_ok cfg segs IM R0 Lim rl keep mem0 XI xtags res ms m.

Local Abbreviation DI := (DInv cfg segs IM R0 Lim rl keep mem0 XI xtags).
(* [comment removed for export] *)
Variable xask : fstate -> option (int * int).
Local Abbreviation drv := (drive IM code Rb Rc Lim rl keep xsys xask).

(* [comment removed for export] *)
Theorem drive_existential_leaf : forall p bp k, (k <= 61)%nat -> forall fuel n rho F L ms m,
  DI n rho F L ms m ->
  tree_all p (drv bp k fuel F L n) = true ->
  exists F' L' n' r rho' ms' m',
    p F' r = true
    /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')
    /\ DI n' rho' F' L' ms' m'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms'))
    /\ ms_rom ms' = ms_rom ms.
Proof.
  intros p bp k Hk fuel n rho F L ms m HD Hall.
  destruct (drive_existential cfg segs IM code Hcode Halloc R0 Rb Rc Lim HRb HRc rl keep mem0 XI xtags
              XI_rho XI_vm xsys xsys_sound xask bp k Hk fuel n rho F L ms m HD)
    as (F' & L' & n' & r & rho' & ms' & m' & Hleaf & Hstar & HD' & Hec).
  exists F', L', n', r, rho', ms', m'.
  split; [exact (tree_all_leaf p _ F' L' n' r Hall Hleaf)|].
  split; [exact Hstar|]. split; [exact HD'|]. split; [exact Hec|].
  exact (star_cfg_rom segs cfg _ _ _ Hstar).
Qed.

(* [comment removed for export] *)
Lemma openat_err_leaf_reaches : forall n rho F L r ms m,
  leaf_openat_err IM F r = true ->
  DI n rho F L ms m ->
  (r = SEcall -> RiscvSemantics.step segs ms = MachineOk (ms_pend ms)) ->
  ms_rom ms = seg_rom segs ->
  reaches_error_cfg segs cfg (mkCfg ms m).
Proof.
  intros n' rho' F' L' r ms' m' Hp HD' Hec Hrom.
  destruct HD' as (HRn & H0 & Hh & Hnl & _).
  unfold leaf_openat_err in Hp. destruct r; try discriminate.
  destruct (FxState.rget F' 17%uint63) as [t7 w7] eqn:E17.
  destruct (FxState.rget F' 10%uint63) as [t0 w0'] eqn:E10.
  destruct (FxState.rget F' 12%uint63) as [t2 w2] eqn:E12.
  destruct (FxState.rget F' 11%uint63) as [t [top off]] eqn:E11.
  repeat match type of Hp with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hp as [Hp H] end.
  destruct (fx_cstring IM (f_mem F') t off) as [l|] eqn:Estr; [|discriminate].
  apply andb_true_iff in Hc as [Hc Htmp]. apply andb_true_iff in Hc as [Hc Hur].
  apply andb_true_iff in Hc as [Hc Hdn]. apply andb_true_iff in Hc as [Hsl Hlt].
  apply negb_true_iff in Hlt, Hdn, Hur.
  assert (Htmp' : tmp_name (bytes_of l) = None) by (destruct (tmp_name (bytes_of l)); [discriminate Htmp | reflexivity]).
  apply Uint63.eqb_spec in Hp, Hc4, Hc2, Hc0. subst t7 t0 t2 top.
  apply w_eqb_true_iff in Hc5, Hc3. rewrite wZ_w_of_int in Hc5, Hc3. rewrite wZ_w_zext32 in Hc3.
  pose proof (R_svc _ _ _ _ _ (HRn rho' (agree_refl n' rho' H0))) as Hsvc.
  apply (reaches_error_cfg_star cfg segs _ [] (mkCfg (ms_pend ms') m')).
  { apply (rsteps_star_cfg cfg segs 1 ms' m' (ms_pend ms') Hh (proj1 Hnl)).
    cbn [rsteps]. rewrite Hsvc, (Hec eq_refl). reflexivity. }
  apply (fx_openat_sep_error_Rn segs IM cfg n' rho' F' ms' m' w7 w0' w2 t off l HRn H0); assumption.
Qed.

(* [comment removed for export] *)
Theorem drive_reaches_openat_error : forall bp k, (k <= 61)%nat -> forall fuel n rho F L ms m,
  DI n rho F L ms m ->
  ms_rom ms = seg_rom segs ->
  tree_all (leaf_openat_err IM) (drv bp k fuel F L n) = true ->
  reaches_error_cfg segs cfg (mkCfg ms m).
Proof.
  intros bp k Hk fuel n rho F L ms m HD Hrom Hall.
  destruct (drive_existential_leaf (leaf_openat_err IM) bp k Hk fuel n rho F L ms m HD Hall)
    as (F' & L' & n' & r & rho' & ms' & m' & Hp & Hstar & HD' & Hec & Hrom').
  apply (reaches_error_cfg_star cfg segs _ [] (mkCfg ms' m') Hstar).
  apply (openat_err_leaf_reaches n' rho' F' L' r ms' m' Hp HD' Hec). rewrite Hrom'. exact Hrom.
Qed.

(* [comment removed for export] *)
Theorem drive_universal_leaves : forall p bp k, (k <= 61)%nat -> forall fuel n rho F L ms m T,
  DI n rho F L ms m ->
  tree_all p (drv bp k fuel F L n) = true ->
  (forall F' L' n' r rho' ms' m',
     p F' r = true -> DI n' rho' F' L' ms' m' ->
     (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
     realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros p bp k Hk fuel n rho F L ms m T HD Hall Hk0.
  apply (drive_universal cfg segs IM code Hcode Halloc R0 Rb Rc Lim HRb HRc rl keep mem0 XI xtags
           XI_rho XI_vm xsys xsys_sound xask bp k Hk fuel n rho F L ms m T HD).
  intros F' L' n' r Hleaf rho' ms' m' HD' Hec.
  exact (Hk0 F' L' n' r rho' ms' m' (tree_all_leaf p _ F' L' n' r Hall Hleaf) HD' Hec).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis xsys_soundX : forall n rho F L ms m res,
  xsys F L n = Some res -> DInv cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_okX cfg segs IM R0 Lim rl keep mem0 XI xtags n rho F L res ms m.
Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.
Local Abbreviation DIX := (DInvX cfg segs IM R0 Lim rl keep mem0 XI xtags fr0 fc0 rom0 hi).

Theorem drive_existential_leafX : forall p bp k, (k <= 61)%nat -> forall fuel n rho F L ms m,
  DIX n rho F L ms m ->
  tree_all p (drv bp k fuel F L n) = true ->
  exists F' L' n' r rho' ms' m',
    p F' r = true
    /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')
    /\ DIX n' rho' F' L' ms' m'
    /\ dext n rho m n' rho' m'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')).
Proof.
  intros p bp k Hk fuel n rho F L ms m HD Hall.
  destruct (drive_existentialX cfg segs IM code Hcode Halloc R0 Rb Rc Lim HRb HRc rl keep mem0 XI xtags
              XI_rho XI_vm xsys xask xsys_soundX fr0 fc0 rom0 hi bp k Hk fuel n rho F L ms m HD)
    as (F' & L' & n' & r & rho' & ms' & m' & Hleaf & Hstar & HD' & Hext & Hec).
  exists F', L', n', r, rho', ms', m'.
  split; [exact (tree_all_leaf p _ F' L' n' r Hall Hleaf)|].
  split; [exact Hstar|]. split; [exact HD'|]. split; [exact Hext | exact Hec].
Qed.

Theorem drive_universal_leavesX : forall p bp k, (k <= 61)%nat -> forall fuel n rho F L ms m T,
  DIX n rho F L ms m ->
  tree_all p (drv bp k fuel F L n) = true ->
  (forall F' L' n' r rho' ms' m',
     p F' r = true -> DIX n' rho' F' L' ms' m' -> dext n rho m n' rho' m' ->
     (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
     realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros p bp k Hk fuel n rho F L ms m T HD Hall Hk0.
  apply (drive_universalX cfg segs IM code Hcode Halloc R0 Rb Rc Lim HRb HRc rl keep mem0 XI xtags
           XI_rho XI_vm xsys xask xsys_soundX fr0 fc0 rom0 hi bp k Hk fuel n rho F L ms m T HD).
  intros F' L' n' r Hleaf rho' ms' m' HD' Hext Hec.
  exact (Hk0 F' L' n' r rho' ms' m' (tree_all_leaf p _ F' L' n' r Hall Hleaf) HD' Hext Hec).
Qed.
End Hb.
