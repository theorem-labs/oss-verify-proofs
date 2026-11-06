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
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeCfg NodesCfg AllocCfg MiscCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxRn FxSys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fx_ret_fresh (F : fstate) (n : int) : fstate := fx_sysret F (FV n w_zero) (f_mem F).

(* [comment removed for export] *)
Definition reg_step (ms ms' : machine_state) (rd : reg) (w : word) (npc : int) : Prop :=
  ms_pc_val ms' = Z_to_bv 64 (to_Z npc)
  /\ (forall r, Sem.rget (core_of ms') r =
                if is_x0 r then w0 else if bv_eqb r rd then w else Sem.rget (core_of ms) r)
  /\ ms_svc_pending ms' = None
  /\ ms_resv ms' = ms_resv ms
  /\ ms_mem ms' = ms_mem ms.

(* [comment removed for export] *)
Definition seg_rom (segs : list Segment) : word -> option byte :=
  fun addr => match memory_read segs addr 1 with
              | Some (b :: _) => Some b
              | _ => None
              end.

Lemma init_cfg_rom : forall img lim en inp,
  ms_rom (cfg_ms (init_cfg img lim en inp)) = seg_rom (img_segments img).
Proof. intros [segs pc ph] lim [sp brk0 mb rnd] inp. reflexivity. Qed.

Lemma read_byte_rview : forall segs ms a,
  ms_rom ms = seg_rom segs -> ms_read_byte ms a = rview segs (ms_mem ms) a.
Proof. intros segs ms a H. unfold ms_read_byte, rview. rewrite H. reflexivity. Qed.

Lemma ms_rom_pend : forall ms, ms_rom (ms_pend ms) = ms_rom ms.
Proof. reflexivity. Qed.

Lemma ms_read_byte_pend : forall ms a, ms_read_byte (ms_pend ms) a = ms_read_byte ms a.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section CString.
Variable IM : fimage.

Definition fx_byte (M : itrie region) (t off : int) : option w64 :=
  match fm_load IM M (FV t (W64 0 off)) SZ1 false with
  | Some v => if (vtag v =? 0)%uint63 then Some (vw v) else None   (* [comment removed for export] *)
  | None => None
  end.

Fixpoint fx_cstring_aux (M : itrie region) (t off : int) (fuel : nat) : option (list w64) :=
  match fuel with
  | O => None
  | S fuel' =>
      match fx_byte M t off with
      | None => None
      | Some w =>
          if w_eqb w w_zero then Some []
          else match fx_cstring_aux M t (off + 1)%uint63 fuel' with
               | Some r => Some (w :: r)
               | None => None
               end
      end
  end.

Definition fx_cstring (M : itrie region) (t off : int) : option (list w64) :=
  if (off <? 4611686018427387904)%uint63 then fx_cstring_aux M t off path_max else None.
End CString.

(* [comment removed for export] *)
Definition bytes_of (l : list w64) : list byte := map (fun w => Z_to_bv 8 (wZ w)) l.

Lemma length_bytes_of : forall l, length (bytes_of l) = length l.
Proof. intros l. unfold bytes_of. apply length_map. Qed.

(* [comment removed for export] *)
Lemma load_slots_sz1_tag0 : forall sgn bi s v, load_slots SZ1 sgn bi s = Some v -> vtag v = 0%uint63.
Proof.
  intros sgn bi s v H. unfold load_slots in H. cbv zeta in H.
  destruct (all_sk bi (msz_int SZ1) s); [inversion H; reflexivity |].
  destruct sgn; discriminate H.
Qed.

(* [comment removed for export] *)

Section Sound.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.

Lemma fx_byte_sound : forall M m t off w,
  mem_ok segs IM rho M m ->
  fx_byte IM M t off = Some w ->
  rview segs m (dv rho (FV t (W64 0 off))) = Some (Z_to_bv 8 (wZ w)) /\ wZ w < 256.
Proof.
  intros M m t off w Hmem H. unfold fx_byte in H.
  destruct (fm_load IM M (FV t (W64 0 off)) SZ1 false) as [v |] eqn:Hl; [| discriminate H].
  destruct (vtag v =? 0)%uint63 eqn:Htag0; [| discriminate H].
  inversion H; subst w. clear H.
  assert (Htag : vtag v = 0%uint63) by (apply Uint63.eqb_spec; exact Htag0).
  destruct (fm_load_sound segs IM rho Hrho0 M m _ SZ1 false v Hmem Hl) as (bs & Hrd & Hres).
  cbn [msz_nat ov_read_bytes] in Hrd.
  change (match m (dv rho (FV t (W64 0 off))) with
          | Some b => Some b
          | None => match memory_read segs (dv rho (FV t (W64 0 off))) 1 with
                    | Some (b :: _) => Some b
                    | _ => None
                    end
          end) with (rview segs m (dv rho (FV t (W64 0 off)))) in Hrd.
  destruct (rview segs m (dv rho (FV t (W64 0 off)))) as [b |]; [| discriminate Hrd].
  inversion Hrd; subst bs. clear Hrd.
  assert (Hb : bv_unsigned b = wZ (vw v)).
  { rewrite (dv_tag0' rho Hrho0 v) in Hres by (rewrite Htag; reflexivity).
    apply (f_equal bv_unsigned) in Hres. rewrite wbv_unsigned in Hres. rewrite <- Hres.
    unfold load_result. cbv zeta. unfold zext. rewrite bv_zero_extend_unsigned by lia.
    rewrite bv_extract_unsigned. unfold le_bytes_to_word. cbn [bytes_le_to_Z].
    pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 8) with 256 in Hr.
    rewrite Z.shiftl_0_l, Z.lor_0_r, Z.shiftr_0_r.
    rewrite Z_to_bv_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
    symmetry. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia. }
  pose proof (bv_unsigned_in_range _ b) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  split; [| lia]. f_equal. apply bv_eq. rewrite Hb.
  rewrite Z_to_bv_small; [reflexivity | unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia].
Qed.

(* [comment removed for export] *)
Lemma fm_load_plain : forall M m a sz sgn v,
  mem_ok segs IM rho M m -> fm_load IM M a sz sgn = Some v -> to_Z (vtag a) < 2 ^ 60.
Proof.
  intros M m [t [top off]] sz sgn v Hmem H. unfold fm_load in H. cbv zeta in H.
  destruct (negb ((top land 1) =? 0)%uint63); [discriminate H |].
  destruct (negb ((off land 7) + msz_int sz <=? 8)%uint63); [discriminate H |].
  destruct (iget t M) as [rg |] eqn:Hg; [| discriminate H].
  exact (region_plain segs IM rho M m t rg Hmem Hg).
Qed.

(* [comment removed for export] *)
Lemma dv_off_succ : forall t off,
  to_Z t < 2 ^ 60 ->
  to_Z off + 1 < 2 ^ 63 ->
  dv rho (FV t (W64 0 (off + 1)%uint63)) = aoff (dv rho (FV t (W64 0 off))) 1.
Proof.
  intros t off Hpl H. pose proof (to_Z_bounded off) as Hb.
  rewrite !(fk_dv_plain rho (FV t _)) by exact Hpl.
  unfold aoff. cbn [vtag vw]. rewrite !fxs_wbv_W64_0.
  rewrite Uint63.add_spec. change (to_Z 1) with 1. rewrite Z.mod_small by (rewrite fxs_wB; lia).
  apply bv_eq. rewrite !bv_add_unsigned.
  rewrite !fxs_u64_lit by lia. change (Z.of_nat 1) with 1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma aoff_aoff : forall a i j, aoff (aoff a i) j = aoff a (i + j).
Proof.
  intros a i j. unfold aoff. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. set (M := bv_modulus 64). rewrite Nat2Z.inj_add.
  set (A := bv_unsigned a). set (I := Z.of_nat i). set (J := Z.of_nat j).
  rewrite Zplus_mod_idemp_l.                       (* [comment removed for export] *)
  rewrite Zplus_mod_idemp_r.                       (* [comment removed for export] *)
  replace (A + I mod M + J) with (A + J + I mod M) by lia.
  rewrite Zplus_mod_idemp_r.                       (* [comment removed for export] *)
  rewrite (Zplus_mod_idemp_r (I + J) A).           (* [comment removed for export] *)
  f_equal. lia.
Qed.

Lemma fx_cstring_aux_sound : forall fuel M m t off l,
  mem_ok segs IM rho M m ->
  to_Z off + Z.of_nat fuel < 2 ^ 63 ->
  fx_cstring_aux IM M t off fuel = Some l ->
  (length l < fuel)%nat
  /\ no_nul (bytes_of l) = true
  /\ (forall i, (i < length l)%nat ->
        rview segs m (aoff (dv rho (FV t (W64 0 off))) i) = nth_error (bytes_of l) i)
  /\ rview segs m (aoff (dv rho (FV t (W64 0 off))) (length l)) = Some nul_byte.
Proof.
  induction fuel as [|fuel IH]; intros M m t off l Hmem Hb H; [discriminate H |].
  cbn [fx_cstring_aux] in H.
  destruct (fx_byte IM M t off) as [w |] eqn:Hbyte; [| discriminate H].
  destruct (fx_byte_sound M m t off w Hmem Hbyte) as [Hrv Hw256].
  pose proof (wZ_range w) as Hwr.
  destruct (w_eqb w w_zero) eqn:Ez.
  - inversion H; subst l. clear H.
    apply w_eqb_true_iff in Ez. rewrite wZ_w_zero in Ez.
    cbn [length bytes_of map]. rewrite aoff_0.
    split; [lia |]. split; [reflexivity |]. split; [intros i Hi; lia |].
    rewrite Hrv, Ez. reflexivity.
  - destruct (fx_cstring_aux IM M t (off + 1)%uint63 fuel) as [r |] eqn:Hrec; [| discriminate H].
    inversion H; subst l. clear H.
    apply w_eqb_false_iff in Ez. rewrite wZ_w_zero in Ez.
    pose proof (to_Z_bounded off) as Hob.
    assert (Hs : to_Z (off + 1)%uint63 = to_Z off + 1).
    { rewrite Uint63.add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite fxs_wB. lia. }
    destruct (IH M m t (off + 1)%uint63 r Hmem ltac:(rewrite Hs; lia) Hrec)
      as (Hlen & Hnn & Hbytes & Hnul).
    assert (Hpl : to_Z t < 2 ^ 60).
    { unfold fx_byte in Hbyte.
      destruct (fm_load IM M (FV t (W64 0 off)) SZ1 false) as [v0 |] eqn:Hl0; [| discriminate Hbyte].
      exact (fm_load_plain M m _ _ _ _ Hmem Hl0). }
    rewrite (dv_off_succ t off Hpl ltac:(lia)) in Hbytes, Hnul.
    cbn [length bytes_of map]. fold (bytes_of r).
    split; [lia |]. split; [| split].
    + cbn [no_nul forallb]. fold (no_nul (bytes_of r)). rewrite Hnn, andb_true_r.
      apply negb_true_iff. unfold bv_eqb, nul_byte.
      rewrite Z_to_bv_small by (unfold bv_modulus; change (2 ^ Z.of_N 8) with 256; lia).
      change (bv_unsigned (Z_to_bv 8 0)) with 0. apply Z.eqb_neq. exact Ez.
    + intros [|i] Hi.
      * rewrite aoff_0. cbn [nth_error]. exact Hrv.
      * cbn [nth_error]. rewrite <- (Hbytes i ltac:(lia)). rewrite aoff_aoff. reflexivity.
    + rewrite <- Hnul. rewrite aoff_aoff. reflexivity.
Qed.

Theorem fx_cstring_sound : forall M m t off l,
  mem_ok segs IM rho M m ->
  fx_cstring IM M t off = Some l ->
  (length (bytes_of l) < path_max)%nat
  /\ no_nul (bytes_of l) = true
  /\ (forall i, (i < length (bytes_of l))%nat ->
        rview segs m (aoff (dv rho (FV t (W64 0 off))) i) = nth_error (bytes_of l) i)
  /\ rview segs m (aoff (dv rho (FV t (W64 0 off))) (length (bytes_of l))) = Some nul_byte.
Proof.
  intros M m t off l Hmem H. unfold fx_cstring in H.
  destruct (off <? 4611686018427387904)%uint63 eqn:E; [| discriminate H].
  apply Uint63.ltb_spec in E. change (to_Z 4611686018427387904) with (2 ^ 62) in E.
  rewrite length_bytes_of.
  apply (fx_cstring_aux_sound path_max M m t off l Hmem); [| exact H].
  unfold path_max. change (Z.of_nat 4096) with 4096. lia.
Qed.

(* [comment removed for export] *)
Lemma R_gpr : forall F ms (i : nat) (r : reg) (ri : int),
  R segs IM rho F ms ->
  Z_to_bv 5 (10 + Z.of_nat i) = r -> is_x0 r = false -> ireg r = ri ->
  ms_gpr (ms_pend ms) i = dv rho (FxState.rget F ri).
Proof.
  intros F ms i r ri HR Hr Hx0 Hri. subst ri.
  rewrite <- (R_regs _ _ _ _ _ HR r). unfold Sem.rget. rewrite Hx0.
  unfold ms_gpr. cbn [ms_pend ms_regs core_of c_regs]. rewrite Hr. reflexivity.
Qed.

Lemma R_reg17 : forall F ms,
  R segs IM rho F ms -> ms_reg ms (17%bv : bv 5) = dv rho (FxState.rget F 17%uint63).
Proof.
  intros F ms HR. change 17%uint63 with (ireg (17%bv : bv 5)).
  rewrite <- (R_regs _ _ _ _ _ HR (17%bv : bv 5)). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem fx_openat_sep_error : forall cfg F ms m w7 w0' w2 t off l,
  R segs IM rho F ms ->
  ms_rom ms = seg_rom segs ->
  m_halted m = None ->
  FxState.rget F 17%uint63 = FV 0 w7 -> wZ w7 = 56 ->                       (* [comment removed for export] *)
  FxState.rget F 10%uint63 = FV 0 w0' -> wZ w0' mod 2 ^ 32 = 2 ^ 32 - 100 ->  (* [comment removed for export] *)
  FxState.rget F 12%uint63 = FV 0 w2 -> modeled_open_flags (wbv w2) = true ->  (* [comment removed for export] *)
  FxState.rget F 11%uint63 = FV t (W64 0 off) ->                            (* [comment removed for export] *)
  fx_cstring IM (f_mem F) t off = Some l ->
  path_has_slash (bytes_of l) = true ->
  path_eqb (bytes_of l) localtime_path = false ->
  path_eqb (bytes_of l) devnull_path = false ->
  path_eqb (bytes_of l) urandom_path = false ->   (* [comment removed for export] *)
  tmp_name (bytes_of l) = None ->
  reaches_error_cfg segs cfg (mkCfg (ms_pend ms) m).
Proof.
  intros cfg F ms m w7 w0' w2 t off l HR Hrom Hh H17 Hw7 H10 Hw0 H12 Hfl H11 Hstr Hslash Hlt Hdn Hur Htmp.
  destruct (fx_cstring_sound (f_mem F) (ms_mem ms) t off l (R_mem _ _ _ _ _ HR) Hstr)
    as (Hlen & Hnn & Hbytes & Hnul).
  assert (Ha0 : ms_gpr (ms_pend ms) 0 = wbv w0').
  { rewrite (R_gpr F ms 0 (10%bv : bv 5) 10%uint63 HR); [| apply gpr0_reg_eq | reflexivity | reflexivity].
    rewrite H10. apply dv_tag0. exact Hrho0. }
  assert (Ha1 : ms_gpr (ms_pend ms) 1 = dv rho (FV t (W64 0 off))).
  { rewrite (R_gpr F ms 1 (Z_to_bv 5 (10 + Z.of_nat 1)) 11%uint63 HR); [| reflexivity ..].
    rewrite H11. reflexivity. }
  assert (Ha2 : ms_gpr (ms_pend ms) 2 = wbv w2).
  { rewrite (R_gpr F ms 2 (Z_to_bv 5 (10 + Z.of_nat 2)) 12%uint63 HR); [| reflexivity ..].
    rewrite H12. apply dv_tag0. exact Hrho0. }
  apply (openat_sep_reaches_error cfg segs (ms_pend ms) (ms_reg ms (17%bv : bv 5)) m (bytes_of l)).
  - exact Hh.
  - reflexivity.
  - rewrite (R_reg17 F ms HR), H17, (dv_tag0 rho Hrho0), wbv_unsigned. exact Hw7.
  - rewrite Ha0. apply fd32_at_fdcwd. rewrite wbv_unsigned. exact Hw0.
  - rewrite Ha2. exact Hfl.
  - exact Hlen.
  - exact Hnn.
  - intros i Hi. rewrite Ha1, ms_read_byte_pend, (read_byte_rview segs ms _ Hrom).
    exact (Hbytes i Hi).
  - rewrite Ha1, ms_read_byte_pend, (read_byte_rview segs ms _ Hrom). exact Hnul.
  - exact Hslash.
  - exact Hlt.
  - exact Hdn.
  - exact Hur.
  - exact Htmp.
Qed.

End Sound.

(* [comment removed for export] *)
Section WithRn.
Variable segs : list Segment.
Variable IM : fimage.
Local Abbreviation Rn := (FxRn.Rn segs IM).

Theorem fx_openat_sep_error_Rn : forall cfg n rho F ms m w7 w0' w2 t off l,
  Rn n rho F ms ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  ms_rom ms = seg_rom segs ->
  m_halted m = None ->
  FxState.rget F 17%uint63 = FV 0 w7 -> wZ w7 = 56 ->
  FxState.rget F 10%uint63 = FV 0 w0' -> wZ w0' mod 2 ^ 32 = 2 ^ 32 - 100 ->
  FxState.rget F 12%uint63 = FV 0 w2 -> modeled_open_flags (wbv w2) = true ->
  FxState.rget F 11%uint63 = FV t (W64 0 off) ->
  fx_cstring IM (f_mem F) t off = Some l ->
  path_has_slash (bytes_of l) = true ->
  path_eqb (bytes_of l) localtime_path = false ->
  path_eqb (bytes_of l) devnull_path = false ->
  path_eqb (bytes_of l) urandom_path = false ->   (* [comment removed for export] *)
  tmp_name (bytes_of l) = None ->
  reaches_error_cfg segs cfg (mkCfg (ms_pend ms) m).
Proof.
  intros cfg n rho F ms m w7 w0' w2 t off l HRn H0.
  apply (fx_openat_sep_error segs IM rho H0 cfg F ms m w7 w0' w2 t off l).
  apply HRn. apply agree_refl. exact H0.
Qed.

(* [comment removed for export] *)
Theorem fx_ret_fresh_sound : forall n rho F ms w,
  Rn n rho F ms -> at_ecall F ->
  to_Z n < 2 ^ 60 ->
  Rn (n + 1)%uint63 (rho_upd rho n w) (fx_ret_fresh F n) (sysret (ms_pend ms) w (ms_mem ms)).
Proof.
  intros n rho F ms w HRn Hpc Hnb rho'' Hag''.
  destruct (agree_upd n rho w rho'' ltac:(lia) Hag'') as [Hag Hnw].
  pose proof (HRn rho'' Hag) as HR.
  unfold fx_ret_fresh. apply fxs_R_sysret; [exact HR | exact Hpc | | exact (R_mem _ _ _ _ _ HR)].
  rewrite (fk_dv_plain rho'' (FV n w_zero)) by (cbn [vtag]; lia).
  cbn [vtag vw]. rewrite Hnw, wbv_w_zero. unfold w0. apply fxs_bv_add_0.
Qed.

(* [comment removed for export] *)
Lemma fxm_R_reg_step : forall rho F ms ms' rd w v npc,
  R segs IM rho F ms ->
  reg_step ms ms' rd w npc ->
  dv rho v = w ->
  R segs IM rho (FxState.rset F (ireg rd) v npc) ms'.
Proof.
  intros rho F ms ms' rd w v npc HR (Hpc & Hregs & Hsvc & Hresv & Hmem) Hv. constructor.
  - exact Hpc.
  - intros r. rewrite Hregs. pose proof (R_regs _ _ _ _ _ HR r) as Hr.
    unfold FxState.rget, FxState.rset in *. cbn [f_regs].
    rewrite fxs_ireg_is0 in *. unfold Sem.rget in Hr.
    destruct (is_x0 r) eqn:Ex0; [exact Hr |].
    assert (Heq : (ireg r =? ireg rd)%uint63 = bv_eqb r rd).
    { unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned r) (bv_unsigned rd)) as [E | E].
      - apply Uint63.eqb_spec. apply Uint63.to_Z_inj. rewrite !fxs_ireg_to_Z. exact E.
      - apply fxs_eqb_false. rewrite !fxs_ireg_to_Z. exact E. }
    destruct (ireg rd =? 0)%uint63 eqn:Erd.
    + (* [comment removed for export] *)
      rewrite fxs_ireg_is0 in Erd.
      destruct (bv_eqb r rd) eqn:E.
      * unfold bv_eqb in E. apply Z.eqb_eq in E. unfold is_x0 in Ex0, Erd. rewrite E in Ex0. congruence.
      * unfold Sem.rget. rewrite Ex0. exact Hr.
    + rewrite iget_iset, Heq. destruct (bv_eqb r rd); [symmetry; exact Hv |].
      unfold Sem.rget. rewrite Ex0. exact Hr.
  - exact Hsvc.
  - rewrite Hresv. cbn [FxState.rset f_resv]. exact (R_resv _ _ _ _ _ HR).
  - rewrite Hmem. cbn [FxState.rset f_mem]. exact (R_mem _ _ _ _ _ HR).
Qed.

(* [comment removed for export] *)
Theorem fx_rd_known_sound : forall n rho F ms ms' rd w v npc,
  Rn n rho F ms ->
  reg_step ms ms' rd w npc ->
  (forall rho', agree n rho rho' -> dv rho' v = w) ->
  Rn n rho (FxState.rset F (ireg rd) v npc) ms'.
Proof.
  intros n rho F ms ms' rd w v npc HRn Hstep Hv rho' Hag.
  exact (fxm_R_reg_step rho' F ms ms' rd w v npc (HRn rho' Hag) Hstep (Hv rho' Hag)).
Qed.

(* [comment removed for export] *)
Theorem fx_rd_fresh_sound : forall n rho F ms ms' rd w npc,
  Rn n rho F ms ->
  reg_step ms ms' rd w npc ->
  to_Z n < 2 ^ 60 ->
  Rn (n + 1)%uint63 (rho_upd rho n w) (FxState.rset F (ireg rd) (FV n w_zero) npc) ms'.
Proof.
  intros n rho F ms ms' rd w npc HRn Hstep Hnb rho'' Hag''.
  destruct (agree_upd n rho w rho'' ltac:(lia) Hag'') as [Hag Hnw].
  apply (fxm_R_reg_step rho'' F ms ms' rd w (FV n w_zero) npc (HRn rho'' Hag) Hstep).
  rewrite (fk_dv_plain rho'' (FV n w_zero)) by (cbn [vtag]; lia).
  cbn [vtag vw]. rewrite Hnw, wbv_w_zero. unfold w0. apply fxs_bv_add_0.
Qed.

End WithRn.
