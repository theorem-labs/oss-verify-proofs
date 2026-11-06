(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cfg.
Module RzNodes.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma node_outcomes : forall ms mo x8 (I : Type) (effs : I -> resp) (mos : I -> Model) (evs : I -> list event),
  m_halted mo = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists i, o = Ok (effs i) (mos i) (evs i)) ->
  (forall i, m_halted (mos i) = None) -> (forall i, m_vm_lazy (mos i) = []) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) mo (effs i)) ->
  node_ok segs (mkCfg ms mo) I evs (fun i => mkCfg (nret ms (effs i)) (mos i)).
Proof.
  intros ms mo x8 I effs mos evs Hh Hsvc Hiff Hh' Hl' Hns. split.
  - intros i. apply (sstep_cfg_syscall segs ACFG ms mo x8 (effs i) (mos i) (mos i) (evs i) Hh Hsvc);
      [apply Hiff; exists i; reflexivity | apply Hns | apply Hh' | apply materialize_model_accesses_no_lazy; apply Hl'].
  - intros e st Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_svc_inv segs ms mo x8 e st Hsvc Hss)
      as [(eff & mo1 & mo2 & Hspec & Hh1 & Hmat & ->)
         |[(eff & mo1 & evs0 & Hspec & Hh1 & Hmat & -> & ->)
         |[(eff & mo1 & evs0 & code & Hspec & Hcode & -> & ->)
         | (Hspec & -> & ->)]]].
    + apply Hiff in Hspec as (i & E). injection E as -> -> ->.
      rewrite (materialize_model_accesses_no_lazy _ _ (Hl' i)) in Hmat. injection Hmat as <-.
      exists i. split; reflexivity.
    + exfalso. apply Hiff in Hspec as (i & E). injection E as -> -> ->.
      rewrite (materialize_model_accesses_no_lazy _ _ (Hl' i)) in Hmat. discriminate Hmat.
    + exfalso. apply Hiff in Hspec as (i & E). injection E as -> -> ->.
      rewrite (Hh' i) in Hcode. discriminate Hcode.
    + exfalso. apply Hiff in Hspec as (i & E). discriminate E.
Qed.

(* [comment removed for export] *)
Lemma rz_outcomes : forall ms mo x8 (I : Type) (effs : I -> resp) (mos : I -> Model) (evs : I -> list event)
                           (T : I -> TSet) (i0 : I),
  m_halted mo = None -> ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists i, o = Ok (effs i) (mos i) (evs i)) ->
  (forall i, m_halted (mos i) = None) -> (forall i, m_vm_lazy (mos i) = []) ->
  (forall i, realizes segs (mkCfg (nret ms (effs i)) (mos i)) (T i)) ->
  realizes segs (mkCfg ms mo) (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros ms mo x8 I effs mos evs T i0 Hh Hsvc Hb Hiff Hh' Hl' HK.
  apply (rz_node segs (mkCfg ms mo) I evs (fun i => mkCfg (nret ms (effs i)) (mos i)) T i0).
  - apply (node_outcomes ms mo x8 I effs mos evs Hh Hsvc Hiff Hh' Hl').
    intros i. exact (nsp_no segs ms x8 _ mo (effs i) eq_refl Hb).
  - exact HK.
Qed.

(* [comment removed for export] *)
Lemma rz_outcomes_silent : forall ms mo x8 (I : Type) (effs : I -> resp) (mos : I -> Model) (K : TSet) (i0 : I),
  m_halted mo = None -> ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> exists i, o = Ok (effs i) (mos i) []) ->
  (forall i, m_halted (mos i) = None) -> (forall i, m_vm_lazy (mos i) = []) ->
  (forall i, realizes segs (mkCfg (nret ms (effs i)) (mos i)) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo x8 I effs mos K i0 Hh Hsvc Hb Hiff Hh' Hl' HK.
  apply (rz_conseq segs _ (t_alt (fun _ : I => t_emit [] K))).
  - apply (rz_outcomes ms mo x8 I effs mos (fun _ => []) (fun _ => K) i0 Hh Hsvc Hb Hiff Hh' Hl' HK).
  - assert (HT : K []) by (eapply realizes_nonempty; apply (HK i0)).
    intros tr. split.
    + intros [_ Ht]. exact (proj1 (t_emit_nil_eq K HT tr) Ht).
    + intros Ht. exists i0. exact (proj2 (t_emit_nil_eq K HT tr) Ht).
Qed.

(* [comment removed for export] *)
Lemma rz_det_silent : forall ms mo x8 eff mo' K,
  m_halted mo = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok eff mo' []) ->
  m_halted mo' = None -> m_vm_lazy mo' = [] ->
  realizes segs (mkCfg (nret ms eff) mo') K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo x8 eff mo' K Hh Hsvc Hiff Hh' Hl' HK.
  eapply rz_silent1; [|exact HK].
  apply (node_outcomes ms mo x8 unit (fun _ => eff) (fun _ => mo') (fun _ => []) Hh Hsvc);
    [| intros _; exact Hh' | intros _; exact Hl' |].
  - intros o. rewrite Hiff. split; [intros ->; exists tt; reflexivity | intros [[] ->]; reflexivity].
  - intros _. apply nsp_det. intros eff' m' evs' Hs. apply Hiff in Hs. injection Hs as -> _ _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_err_or_one : forall ms mo x8 (errs : list Z) (e0 : Z) (erf : Z -> resp) eff1 mo1 KA KB,
  m_halted mo = None -> m_vm_lazy mo = [] -> ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  In e0 errs ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     (exists e, In e errs /\ o = Ok (erf e) mo []) \/ o = Ok eff1 mo1 []) ->
  m_halted mo1 = None -> m_vm_lazy mo1 = [] ->
  (forall e, In e errs -> realizes segs (mkCfg (nret ms (erf e)) mo) KA) ->
  realizes segs (mkCfg (nret ms eff1) mo1) KB ->
  realizes segs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros ms mo x8 errs e0 erf eff1 mo1 KA KB Hh Hl Hsvc Hb He0 Hiff Hh1 Hl1 HA HB.
  pose (I := ({e : Z | In e errs} + unit)%type).
  pose (effs := fun i : I => match i with inl (exist _ e _) => erf e | inr _ => eff1 end).
  pose (mos := fun i : I => match i with inl _ => mo | inr _ => mo1 end).
  apply (rz_alt2 segs (mkCfg ms mo) {e : Z | In e errs} unit
           (fun i => mkCfg (nret ms (effs i)) (mos i)) KA KB (exist _ e0 He0) tt).
  - apply (node_outcomes ms mo x8 I effs mos (fun _ => []) Hh Hsvc).
    + intros o. rewrite Hiff. split.
      * intros [(e & He & ->) | ->]; [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity.
      * intros [[[e He] | []] ->]; [left; exists e; auto | right; reflexivity].
    + intros [[e He] | []]; assumption.
    + intros [[e He] | []]; assumption.
    + intros i. exact (nsp_no segs ms x8 _ mo (effs i) eq_refl Hb).
  - intros [e He]. apply HA. exact He.
  - intros []. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma svc_pending : forall R F pc x8 fc rv m, ms_svc_pending (MSsvc R F pc x8 fc rv m (seg_rom segs)) = Some x8.
Proof. reflexivity. Qed.
Lemma svc_sysno : forall R F pc x8 fc rv m x, in_sysno (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) = x.
Proof. reflexivity. Qed.
Lemma svc_a0 : forall R F pc x8 fc rv m x, in_arg (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) 0 = reg_get R 10.
Proof. reflexivity. Qed.
Lemma svc_a1 : forall R F pc x8 fc rv m x, in_arg (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) 1 = reg_get R 11.
Proof. reflexivity. Qed.
Lemma svc_a2 : forall R F pc x8 fc rv m x, in_arg (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) 2 = reg_get R 12.
Proof. reflexivity. Qed.
Lemma svc_mem : forall R F pc x8 fc rv m x, in_mem (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) = mrd segs m.
Proof. reflexivity. Qed.
Lemma svc_wmem : forall R F pc x8 fc rv m x, in_wmem (sys_input segs (MSsvc R F pc x8 fc rv m (seg_rom segs)) x) = wview segs m.
Proof. reflexivity. Qed.
Lemma svc_gpr0 : forall R F pc x8 fc rv m, ms_gpr (MSsvc R F pc x8 fc rv m (seg_rom segs)) 0 = reg_get R 10.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nret_svc : forall R F pc x8 fc rv m r ws zs us cis,
  nret (MSsvc R F pc x8 fc rv m (seg_rom segs)) (mkEffectU r ws zs us [] cis)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) (seg_rom segs).
Proof. reflexivity. Qed.

Lemma nret_svc_ret : forall R F pc x8 fc rv m r cis,
  nret (MSsvc R F pc x8 fc rv m (seg_rom segs)) (eff0c r cis)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv m (seg_rom segs).
Proof. reflexivity. Qed.

Lemma u64_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply unsigned_lit. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close : forall R F pc fc rv m mo (fd : word) e K,
  MOK mo ->
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some e ->
  realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 0)))
                       (with_fds (fd_remove (m_fds mo) fd) mo)) K ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 57) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo fd e K [Hh Hl] H10 Hfd Hlk HK.
  eapply rz_det_silent; [exact Hh | reflexivity | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_57 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
  rewrite svc_a0, H10, (fd32_id fd Hfd). exact (close_outcome fd _ mo e o Hlk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_ioctl_tty : forall R F pc fc rv m mo (fd : word) e K,
  MOK mo ->
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some e ->
  e <> FdUrandom ->
  reg_get R 11 = TIOCGWINSZ ->
  realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) (efferr ENOTTY)) mo) K ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 29) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo fd e K [Hh Hl] H10 Hfd Hlk Hnd H11 HK.
  eapply rz_det_silent; [exact Hh | reflexivity | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_29 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
  rewrite svc_a0, svc_a1, H10, H11, (fd32_id fd Hfd).
  apply (ioctl_tty_outcome fd _ _ mo e o Hlk Hnd). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_exit_no_93 : is_exit_no (Z_to_bv 64 93). Proof. left. reflexivity. Qed.
Lemma is_exit_no_94 : is_exit_no (Z_to_bv 64 94). Proof. right. reflexivity. Qed.

Lemma rz_exit_svc : forall R F pc x8 fc rv m mo,
  m_halted mo = None -> is_exit_no x8 ->
  realizes segs (mkCfg (MSsvc R F pc x8 fc rv m (seg_rom segs)) mo)
           (t_exit (bv_and (reg_get R 10) (Z_to_bv 64 255)) (m_fs mo)).
Proof.
  intros R F pc x8 fc rv m mo Hh Hx8. rewrite <- svc_gpr0 with (F := F) (pc := pc) (x8 := x8) (fc := fc) (rv := rv) (m := m).
  eapply ShapeAlg.rz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.

Lemma bv_and_255_small : forall code, 0 <= code < 256 ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
  intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma rz_exit_group_lit : forall R F pc fc rv m mo (code : Z),
  m_halted mo = None -> reg_get R 10 = Z_to_bv 64 code -> 0 <= code < 256 ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 94) fc rv m (seg_rom segs)) mo)
           (t_exit (Z_to_bv 64 code) (m_fs mo)).
Proof.
  intros R F pc fc rv m mo code Hh H10 Hc.
  rewrite <- (bv_and_255_small code Hc), <- H10. apply rz_exit_svc; [exact Hh | apply is_exit_no_94].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_bytes_map_wr_at : forall m (buf cnt : Z),
  wr_at segs m buf cnt -> 0 <= cnt < 2^64 ->
  exists w, read_bytes_map (wview segs m) (Z_to_bv 64 buf) (Z_to_bv 64 cnt) = Some w.
Proof.
  intros m buf cnt Hw Hc. rewrite read_bytes_map_eq.
  pose proof (read_bytes_aux_wr_at segs m buf cnt (word_to_nat (Z_to_bv 64 cnt)) Hw
                ltac:(unfold word_to_nat; rewrite u64_lit by lia; lia)) as H.
  change (Z_to_bv 64 buf) with (wa buf).
  destruct (read_bytes_aux (wview segs m) (wa buf) (word_to_nat (Z_to_bv 64 cnt))) as [w|]; [exists w; reflexivity | congruence].
Qed.

Lemma length_file_read : forall data off count,
  length (file_read data off count) = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof. intros. rewrite file_read_unguarded, length_firstn, length_skipn. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_file_outcome_i : forall i mo (fd buf cnt : word) p off data w,
  bv_unsigned (in_sysno i) = 63 -> in_arg i 0 = fd -> bv_unsigned fd < 2^32 ->
  in_arg i 1 = buf -> in_arg i 2 = cnt ->
  fd_lookup (m_fds mo) fd = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  read_bytes_map (in_wmem i) buf cnt = Some w ->
  bv_unsigned cnt <= rw_bytes_max -> bv_unsigned buf + bv_unsigned cnt <= TASK_SIZE ->
  let bs := file_read data off cnt in
  forall o, syscall_spec i mo o <->
    o = Ok (mkEffect (len_word bs) (delivered_writes buf bs) [])
           (with_fds (fd_insert (m_fds mo) fd (FdFile p (off + len_word bs)%bv)) mo) [].
Proof.
  intros i mo fd buf cnt p off data w Hno H0 Hfd H1 H2 Hlk Hfs Hw Hcnt Htask bs o.
  assert (HL : bv_unsigned (len_word (file_read data off cnt)) <= bv_unsigned cnt).
  { unfold len_word. rewrite unsigned_lit_wrap.
    pose proof (bv_unsigned_in_range 64 cnt) as Hc. unfold bv_modulus in Hc.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; [lia|]. change (2 ^ Z.of_N 64) with (2^64) in Hc. lia. }
  rewrite (syscall_spec_63 i mo o Hno), H0, H1, H2, (fd32_id fd Hfd).
  assert (Hcl : Z_to_bv 64 (rw_count_clamp cnt) = cnt).
  { rewrite (rw_count_clamp_of_rw _ Hcnt). apply Z_to_bv_bv_unsigned. }
  rewrite (read_file_outcome fd buf cnt i mo o p off data (firstn (word_to_nat (len_word bs)) w) Hlk).
  - rewrite Hcl. reflexivity.
  - apply access_okb_intro. exact Htask.
  - exact Hfs.
  - rewrite Hcl. exact (read_bytes_map_prefix _ _ _ _ _ HL Hw).
Qed.

Lemma length_file_read_le : forall data off (cnt : Z), 0 <= cnt < 2^64 ->
  Z.of_nat (length (file_read data off (Z_to_bv 64 cnt))) <= cnt.
Proof.
  intros data off cnt Hc. rewrite length_file_read. unfold word_to_nat. rewrite u64_lit by lia. lia.
Qed.

Lemma len_word_of : forall (bs : list byte), Z.of_nat (length bs) < 2^64 ->
  len_word bs = Z_to_bv 64 (Z.of_nat (length bs)).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_bytes_max_val : rw_bytes_max = 131072.
Proof. reflexivity. Qed.
Lemma TASK_SIZE_val : TASK_SIZE = 0x800000000000.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rz_read_file : forall R F pc fc rv m mo (fd : word) p off data (buf cnt : Z) K,
  MOK mo ->
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  reg_get R 11 = Z_to_bv 64 buf -> reg_get R 12 = Z_to_bv 64 cnt ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->
  wr_at segs m buf cnt ->
  let bs := file_read data off (Z_to_bv 64 cnt) in
  realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs))
                             (mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []))
                       (with_fds (fd_insert (m_fds mo) fd (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo)) K ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo fd p off data buf cnt K [Hh Hl] H10 Hfd Hlk Hfs H11 H12 Hcnt Hnw Hwr bs HK.
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  destruct (read_bytes_map_wr_at m buf cnt Hwr ltac:(lia)) as [w Hw].
  eapply rz_det_silent; [exact Hh | reflexivity | | | | exact HK]; [| exact Hh | exact Hl].
  subst bs. rewrite <- len_word_of by (pose proof (length_file_read_le data off cnt ltac:(lia)); lia).
  apply (read_file_outcome_i _ mo fd (Z_to_bv 64 buf) (Z_to_bv 64 cnt) p off data w);
    rewrite ?svc_sysno, ?svc_a0, ?svc_a1, ?svc_a2, ?svc_wmem; try assumption.
  - apply u64_lit; lia.
  - rewrite u64_lit by lia. rewrite rw_bytes_max_val. lia.
  - rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
Qed.

(* [comment removed for export] *)
Lemma rz_read_dir : forall R F pc fc rv m mo (fd : word) (buf cnt : Z) K,
  MOK mo ->
  reg_get R 10 = fd -> bv_unsigned fd < 2^32 ->
  fd_lookup (m_fds mo) fd = Some FdDir ->
  reg_get R 11 = Z_to_bv 64 buf -> reg_get R 12 = Z_to_bv 64 cnt ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->
  wr_at segs m buf cnt ->
  realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) (efferr EISDIR)) mo) K ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 63) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo fd buf cnt K [Hh Hl] H10 Hfd Hlk H11 H12 Hcnt Hnw Hwr HK.
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  eapply rz_det_silent; [exact Hh | reflexivity | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_63 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
  rewrite svc_a0, svc_a1, svc_a2, H10, H11, H12, (fd32_id fd Hfd).
  apply (read_dir_outcome fd _ _ _ mo o Hlk).
  apply access_okb_intro. rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_bytes_in : forall m a bs, bytes_at segs m a bs -> bytes_in (mrd segs m) a bs.
Proof. intros m a bs H. exact H. Qed.

Section Openat.
  Variables (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m : word -> option byte) (mo : Model).
  Hypothesis HM : MOK mo.
  Hypothesis H10 : reg_get R 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (reg_get R 12)) open_ignored_flags = 0.

  Let svc := MSsvc R F pc (Z_to_bv 64 56) fc rv m (seg_rom segs).
  Let pathp := reg_get R 11.
  Let fds := m_fds mo.

  (* [comment removed for export] *)
  Lemma openat_head : forall o,
    syscall_spec (sys_input segs svc (Z_to_bv 64 56)) mo o <->
    openat_spec AT_FDCWD32 pathp (reg_get R 12) (sys_input segs svc (Z_to_bv 64 56)) mo o.
  Proof.
    intros o. unfold svc, pathp. rewrite (syscall_spec_56 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite svc_a0, svc_a1, svc_a2, H10. reflexivity.
  Qed.

  Lemma open_flags_modeled : modeled_open_flags (reg_get R 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p /\ bytes_at segs m (bv_unsigned pathp) (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (in_mem (sys_input segs svc (Z_to_bv 64 56))) pathp = CstrOk p.
  Proof.
    intros p (H1 & H2 & H3). unfold svc, pathp in *. rewrite svc_mem. unfold read_cstr.
    rewrite <- (wa_unsigned_id (reg_get R 11)). apply read_cstr_aux_bytes_in; [unfold path_max; lia | exact H2 | exact H3].
  Qed.

  (* [comment removed for export] *)
  Lemma nret_copyins : forall ms r reads, nret ms (with_copyins reads (mkEffect r [] [])) = nret ms (eff0 r).
  Proof. reflexivity. Qed.

  Lemma rz_openat_det : forall r K,
    (forall o, syscall_spec (sys_input segs svc (Z_to_bv 64 56)) mo o <->
               o = Ok (with_copyins (open_reads (sys_input segs svc (Z_to_bv 64 56)) pathp) (mkEffect r [] [])) mo []) ->
    realizes segs (mkCfg (nret svc (eff0 r)) mo) K ->
    realizes segs (mkCfg svc mo) K.
  Proof.
    intros r K Hiff HK. destruct HM as [Hh Hl].
    eapply rz_det_silent; [exact Hh | reflexivity | exact Hiff | exact Hh | exact Hl |].
    rewrite nret_copyins. exact HK.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs -> bytes_at segs m (bv_unsigned pathp) bs ->
    realizes segs (mkCfg (nret svc (efferr ENAMETOOLONG)) mo) K ->
    realizes segs (mkCfg svc mo) K.
  Proof.
    intros bs K Hlen Hnz Hb HK. apply rz_openat_det with (r := errno_ret ENAMETOOLONG); [|exact HK].
    intros o. rewrite openat_head. apply (openat_toolong_outcome _ _ _ _ mo open_flags_modeled).
    unfold svc, pathp in *. rewrite svc_mem. unfold read_cstr. rewrite <- (wa_unsigned_id (reg_get R 11)).
    apply (read_cstr_aux_toolong_bytes_in path_max bs); [unfold path_max; lia | exact Hnz | exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    realizes segs (mkCfg (nret svc (efferr ENOENT)) mo) K ->
    realizes segs (mkCfg svc mo) K.
  Proof.
    intros K Hp HK. apply rz_openat_det with (r := errno_ret ENOENT); [|exact HK].
    intros o. rewrite openat_head. apply (openat_empty_outcome _ _ _ _ mo open_flags_modeled). exact (path_at_cstr [] Hp).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->
    fs_lookup (m_fs mo) p = None ->
    realizes segs (mkCfg (nret svc (efferr ENOENT)) mo) K ->
    realizes segs (mkCfg svc mo) K.
  Proof.
    intros p K Hp Hne Hnd Hndd Hsl Hfs HK. apply rz_openat_det with (r := errno_ret ENOENT); [|exact HK].
    intros o. rewrite openat_head.
    apply (openat_absent_outcome _ _ _ _ mo open_flags_modeled eq_refl Hfl p);
      [exact (path_at_cstr p Hp) | exact Hne | exact Hnd | exact Hndd | exact Hsl | exact Hfs].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
  Proof. left. reflexivity. Qed.

  Lemma rz_openat_open : forall (mk : word -> Model) KA KB,
    (forall o, syscall_spec (sys_input segs svc (Z_to_bv 64 56)) mo o <->
               open_out (open_reads (sys_input segs svc (Z_to_bv 64 56)) pathp) mo mk o) ->
    (forall fd, m_halted (mk fd) = m_halted mo) -> (forall fd, m_vm_lazy (mk fd) = m_vm_lazy mo) ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret svc (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret svc (eff0 (alloc_fd fds))) (mk (alloc_fd fds))) KB ->
    realizes segs (mkCfg svc mo) (t_alt2 KA KB).
  Proof.
    intros mk KA KB Hiff Hmkh Hmkl HA HB. destruct HM as [Hh Hl].
    set (rd := open_reads (sys_input segs svc (Z_to_bv 64 56)) pathp) in *.
    apply (rz_err_or_one svc mo (Z_to_bv 64 56) openat_errnos ENOMEM
             (fun e => with_copyins rd (efferr e)) (with_copyins rd (eff0 (alloc_fd fds))) (mk (alloc_fd fds)) KA KB
             Hh Hl eq_refl eq_refl ENOMEM_in_openat_errnos).
    - intros o. rewrite Hiff. unfold open_out, fds. split.
      + intros [(e & He & ->) | (_ & ->)]; [left; exists e; auto | right; reflexivity].
      + intros [(e & He & ->) | ->]; [left; exists e; auto | right; auto].
    - rewrite Hmkh. exact Hh.
    - rewrite Hmkl. exact Hl.
    - intros e He. change (nret svc (with_copyins rd (efferr e))) with (nret svc (efferr e)). apply HA. exact He.
    - exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret svc (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret svc (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo)) KB ->
    realizes segs (mkCfg svc mo) (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB.
    apply (rz_openat_open (fun fd => with_fds (fd_insert fds fd FdDir) mo)); [| reflexivity | reflexivity | exact HA | exact HB].
    intros o. rewrite openat_head. apply (openat_dot_outcome _ _ _ _ mo open_flags_modeled eq_refl Hfl). exact (path_at_cstr _ Hp).
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->
    fs_lookup (m_fs mo) p = Some d ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret svc (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret svc (eff0 (alloc_fd fds)))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) mo)) KB ->
    realizes segs (mkCfg svc mo) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hnd Hndd Hsl Hfs HA HB.
    apply (rz_openat_open (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) mo));
      [| reflexivity | reflexivity | exact HA | exact HB].
    intros o. rewrite openat_head.
    apply (openat_file_outcome _ _ _ _ mo open_flags_modeled eq_refl Hfl p d);
      [exact (path_at_cstr p Hp) | exact Hne | exact Hnd | exact Hndd | exact Hsl | exact Hfs].
  Qed.
End Openat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma copy_iovecs_aux_bytes_in : forall iovs mp a,
  bytes_in mp a (iovec_bytes iovs) ->
  Forall (fun iv => bv_unsigned (snd iv) < 2^63) iovs ->
  copy_iovecs_aux mp (wa a) (length iovs) = ImpOk iovs.
Proof.
  induction iovs as [|[b l] iovs IH]; intros mp a H Hl; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in H. rewrite <- app_assoc in H.
  apply bytes_in_app in H as [H1 H]. apply bytes_in_app in H as [H2 H3].
  rewrite !length_le8 in H2. rewrite !length_le8 in H3.
  cbn [copy_iovecs_aux length]. unfold read_iovec_entry.
  rewrite (read_u64_bytes_in _ _ _ H1). rewrite !wa_add.
  change (bv_unsigned (8%bv : word)) with 8. change (bv_unsigned (16%bv : word)) with 16.
  replace (a + Z.of_nat 8) with (a + 8) in H2 by lia. rewrite (read_u64_bytes_in _ _ _ H2).
  inversion Hl as [|x r Hx Hr]; subst. cbn [fst snd] in Hx.
  rewrite (proj2 (Z.leb_gt _ _) Hx).
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) in H3 by lia.
  unfold iovec_bytes in IH. rewrite (IH _ _ H3 Hr). reflexivity.
Qed.

Lemma Forall2_iov_ok_lens : forall mp iovs bss,
  Forall2 (iov_ok mp) iovs bss ->
  Forall (fun iv => bv_unsigned (snd iv) <= Z.of_nat (length (concat bss))) iovs.
Proof.
  intros mp iovs bss H. induction H as [|[b l] bs iovs bss (Hl & Hlen & Hb) _ IH]; [constructor|].
  constructor.
  - cbn [snd concat]. cbn [fst snd] in Hl. subst l. rewrite u64_lit by lia. rewrite length_app. lia.
  - eapply Forall_impl; [|exact IH]. intros [b' l'] H'. cbn [snd concat] in *. rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
Lemma writev_outcome_i : forall i mo (fd : Z) (iovp : word) iovs bss,
  bv_unsigned (in_sysno i) = 66 -> in_arg i 0 = Z_to_bv 64 fd -> 0 < fd < 2^31 ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  in_arg i 1 = iovp -> in_arg i 2 = Z_to_bv 64 (Z.of_nat (length iovs)) -> (1 <= length iovs <= 1024)%nat ->
  bytes_in (in_mem i) (bv_unsigned iovp) (iovec_bytes iovs) ->
  Forall2 (iov_ok (in_mem i)) iovs bss ->
  bv_unsigned iovp + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs ->
  let bs := concat bss in
  1 <= Z.of_nat (length bs) -> Z.of_nat (length bs) <= 67108864 ->
  let CA := copy_iovecs_accesses (in_mem i) iovp (length iovs) in
  forall o, syscall_spec i mo o <->
    exists k, (1 <= k <= length bs)%nat /\
      o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
             mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs)).
Proof.
  intros i mo fd iovp iovs bss Hno H0 Hfd Hlk H1 H2 Hcnt Harr Hbufs Htask Hbtask bs Hb1 Hbmax CA o.
  pose proof (gather_iovecs_ok _ _ _ Hbufs) as Hg. fold bs in Hg.
  pose proof (iovs_total_ok _ _ _ Hbufs) as Htot. fold bs in Htot.
  rewrite (syscall_spec_66 i mo o Hno), H0, H1, H2.
  rewrite fd32_id by (rewrite u64_lit; lia).
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  subst CA.
  replace (copy_iovecs_accesses (in_mem i) iovp (length iovs))
    with (copy_iovecs_accesses (in_mem i) iovp (word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))))) by (rewrite Hwn; reflexivity).
  apply (writev_chan_outcome _ _ _ _ mo o (Z_to_bv 64 fd) iovs bs Hlk).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold IOV_MAX. rewrite u64_lit; lia.
  - rewrite Hwn. rewrite <- (wa_unsigned_id iovp). apply copy_iovecs_aux_bytes_in; [exact Harr|].
    eapply Forall_impl; [|exact (Forall2_iov_ok_lens _ _ _ Hbufs)]. intros [b l] Hl. cbn [snd] in *. fold bs in Hl. lia.
  - apply access_okb_intro_Z; rewrite u64_lit by lia; lia.
  - unfold iovs_access_okb. apply forallb_forall. intros [b l] Hin.
    rewrite Forall_forall in Hbtask. specialize (Hbtask _ Hin). cbn [fst snd] in *.
    apply access_okb_intro. exact Hbtask.
  - rewrite Htot. exact Hbmax.
  - exact Hg.
  - exact Hb1.
Qed.

(* [comment removed for export] *)
Lemma rz_writev : forall R F pc fc rv m mo (fd : Z) iovs bss (T : nat -> TSet),
  MOK mo -> 0 < fd < 2^31 ->
  reg_get R 10 = Z_to_bv 64 fd ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) -> (1 <= length iovs <= 1024)%nat ->
  bytes_at segs m (bv_unsigned (reg_get R 11)) (iovec_bytes iovs) ->
  Forall2 (iov_ok (mrd segs m)) iovs bss ->
  bv_unsigned (reg_get R 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs ->
  let bs := concat bss in
  1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
  (forall k, (1 <= k <= length bs)%nat ->
     realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo)
              (T k)) ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) mo)
    (t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
  intros R F pc fc rv m mo fd iovs bss T [Hh Hl] Hfd H10 Hlk H12 Hcnt Harr Hbufs Htask Hbtask bs [Hb1 Hbmax] HK.
  set (svc := MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) in *.
  pose proof (writev_outcome_i (sys_input segs svc (Z_to_bv 64 66)) mo fd (reg_get R 11) iovs bss
                eq_refl H10 Hfd Hlk eq_refl H12 Hcnt Harr Hbufs Htask Hbtask Hb1 Hbmax) as Hiff.
  cbv zeta in Hiff. fold bs in Hiff.
  set (CA := copy_iovecs_accesses _ _ _) in Hiff.
  assert (Hnb : (1 <= length bs)%nat) by lia.
  apply (rz_outcomes svc mo (Z_to_bv 64 66) (wr_index bs)
           (fun i => mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i)))
           (fun _ => mo)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => T (proj1_sig i)) (wr_full bs Hnb) Hh eq_refl eq_refl).
  - intros o. rewrite Hiff. split.
    + intros (k & Hk & ->). exists (exist _ k Hk). reflexivity.
    + intros [[k Hk] ->]. exists k. split; [exact Hk | reflexivity].
  - intros _; exact Hh.
  - intros _; exact Hl.
  - intros [k Hk]. cbn [proj1_sig]. apply (HK k Hk).
Qed.

(* [comment removed for export] *)
Lemma rz_writev_wall : forall R F pc fc rv m mo (fd : Z) iovs bss (K : TSet),
  MOK mo -> 0 < fd < 2^31 ->
  reg_get R 10 = Z_to_bv 64 fd ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) -> (1 <= length iovs <= 1024)%nat ->
  bytes_at segs m (bv_unsigned (reg_get R 11)) (iovec_bytes iovs) ->
  Forall2 (iov_ok (mrd segs m)) iovs bss ->
  bv_unsigned (reg_get R 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs ->
  let bs := concat bss in
  1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
  K [] ->
  (forall k, (1 <= k <= length bs)%nat ->
     realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo)
              (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)) ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) mo)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs) K).
Proof.
  intros R F pc fc rv m mo fd iovs bss K HM Hfd H10 Hlk H12 Hcnt Harr Hbufs Htask Hbtask bs Hb HK0 HK.
  eapply rz_conseq.
  - apply (rz_writev R F pc fc rv m mo fd iovs bss (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)
             HM Hfd H10 Hlk H12 Hcnt Harr Hbufs Htask Hbtask Hb HK).
  - apply t_alt_wall; [exact HK0 | lia].
Qed.

(* [comment removed for export] *)
Lemma rz_writev_zero : forall R F pc fc rv m mo (fd : Z) iovs bss K,
  MOK mo -> 0 < fd < 2^31 ->
  reg_get R 10 = Z_to_bv 64 fd ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) -> (1 <= length iovs <= 1024)%nat ->
  bytes_at segs m (bv_unsigned (reg_get R 11)) (iovec_bytes iovs) ->
  Forall2 (iov_ok (mrd segs m)) iovs bss ->
  bv_unsigned (reg_get R 11) + 16 * Z.of_nat (length iovs) <= TASK_SIZE ->
  Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs ->
  concat bss = [] ->
  realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) (eff0 (Z_to_bv 64 0))) mo) K ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo fd iovs bss K [Hh Hl] Hfd H10 Hlk H12 Hcnt Harr Hbufs Htask Hbtask Hnil HK.
  set (svc := MSsvc R F pc (Z_to_bv 64 66) fc rv m (seg_rom segs)) in *.
  pose proof (iovs_total_ok _ _ _ Hbufs) as Htot. rewrite Hnil in Htot. cbn in Htot.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  apply (rz_det_silent svc mo (Z_to_bv 64 66)
           (with_copyins (copy_iovecs_accesses (in_mem (sys_input segs svc (Z_to_bv 64 66))) (reg_get R 11)
                            (word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs)))))
                         (mkEffect (Z_to_bv 64 0) [] [])) mo); [exact Hh | reflexivity | | exact Hh | exact Hl | exact HK].
  intros o. unfold svc. rewrite (syscall_spec_66 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
  rewrite svc_a0, svc_a1, svc_a2, H10, H12, fd32_id by (rewrite u64_lit; lia).
  apply (writev_chan_zero_outcome _ _ _ _ mo o (Z_to_bv 64 fd) iovs Hlk).
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
  - apply w_is0_pos. rewrite u64_lit; lia.
  - unfold IOV_MAX. rewrite u64_lit; lia.
  - rewrite Hwn, svc_mem. rewrite <- (wa_unsigned_id (reg_get R 11)). apply copy_iovecs_aux_bytes_in; [exact Harr|].
    eapply Forall_impl; [|exact (Forall2_iov_ok_lens _ _ _ Hbufs)]. intros [b l] Hb. cbn [snd] in *. rewrite Hnil in Hb. cbn in Hb. lia.
  - apply access_okb_intro_Z; rewrite u64_lit by lia; lia.
  - unfold iovs_access_okb. apply forallb_forall. intros [b l] Hin.
    rewrite Forall_forall in Hbtask. specialize (Hbtask _ Hin). cbn [fst snd] in *.
    apply access_okb_intro. exact Hbtask.
  - exact Htot.
  - vm_compute. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_set_tid : forall R F pc fc rv m mo K,
  MOK mo -> m_tid mo = None ->
  (forall t, 0 < bv_unsigned t < PID_MAX_ENVELOPE ->
     realizes segs (mkCfg (nret (MSsvc R F pc (Z_to_bv 64 96) fc rv m (seg_rom segs)) (eff0 t)) (with_tid t mo)) K) ->
  realizes segs (mkCfg (MSsvc R F pc (Z_to_bv 64 96) fc rv m (seg_rom segs)) mo) K.
Proof.
  intros R F pc fc rv m mo K [Hh Hl] Htid HK.
  pose (I := {t : word | 0 < bv_unsigned t < PID_MAX_ENVELOPE}).
  assert (i0 : I). { exists (Z_to_bv 64 1). unfold PID_MAX_ENVELOPE. rewrite u64_lit; lia. }
  apply (rz_outcomes_silent (MSsvc R F pc (Z_to_bv 64 96) fc rv m (seg_rom segs)) mo (Z_to_bv 64 96) I
           (fun i => eff0 (proj1_sig i)) (fun i => with_tid (proj1_sig i) mo) K i0 Hh eq_refl eq_refl).
  - intros o. rewrite (syscall_spec_96 _ mo o) by (rewrite svc_sysno; apply u64_lit; lia).
    rewrite (set_tid_fresh_outcome _ mo o Htid). split.
    + intros (t & Ht & ->). exists (exist _ t Ht). reflexivity.
    + intros [[t Ht] ->]. exists t. auto.
  - intros i; exact Hh.
  - intros i; exact Hl.
  - intros [t Ht]. apply HK. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma alloc_fd_012 : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.

Lemma fd_lookup_012_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mkR_set_a0' : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
  bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.

Lemma apply_mem_none' : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof. reflexivity. Qed.
Lemma apply_mem_delivered' : forall m a bs,
  apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof. intros m a [|b bs]; reflexivity. Qed.

(* [comment removed for export] *)
Ltac rz_nret :=
  unfold eff0, efferr, eff0c;
  rewrite ?nret_svc; rewrite ?mkR_set_a0';
  first [ rewrite apply_mem_delivered' | rewrite apply_mem_none' | idtac ];
  repeat match goal with
  | |- context [ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv ] =>
      let p' := eval vm_compute in (p + 4)%Z in
      replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
  end.

End RzNodes.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
Import RzNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_impl_enode : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo K,
  MOK mo ->
  impl segs (at_node segs) (enode n dec) (epost Q) ms ->
  (forall ms1, at_node segs n ms1 ->
     (forall rsp' a mo' K', dec rsp' = Some a -> MOK mo' ->
        (forall ms2, Q a ms2 -> realizes segs (mkCfg ms2 mo') K') ->
        realizes segs (mkCfg (nret ms1 rsp') mo') K') ->
     realizes segs (mkCfg ms1 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros A n dec Q ms mo K HM Himpl Hnode.
  cbn in Himpl. eapply rz_evt; [exact HM | exact Himpl |].
  intros ms1 [Hat Hk]. apply (Hnode ms1 Hat).
  intros rsp' a mo' K' Hdec HM' HK. specialize (Hk rsp'). rewrite Hdec in Hk. cbn in Hk.
  eapply rz_evt; [exact HM' | exact Hk |]. intros ms2 HQ. apply HK. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma in_sysno_pending : forall ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_at_read_file : forall ms mo (fd buf cnt : Z) p off data K,
  at_node segs (NRead fd buf cnt) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  let bs := file_read data off (Z_to_bv 64 cnt) in
  realizes segs (mkCfg (nret ms (mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []))
                       (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo)) K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo fd buf cnt p off data K Hat [Hh Hl] Hlk Hfs Hcnt Hnw bs HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10 & H11 & H12 & _ & Hwr).
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  destruct (read_bytes_map_wr_at segs (ms_mem ms) buf cnt Hwr ltac:(lia)) as [w Hw].
  eapply rz_det_silent; [exact Hh | exact Hsvc | | | | exact HK]; [| exact Hh | exact Hl].
  subst bs. rewrite <- len_word_of by (pose proof (length_file_read_le data off cnt ltac:(lia)); lia).
  apply (read_file_outcome_i _ mo (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 cnt) p off data w);
    rewrite ?in_sysno_pending, ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_wmem_si; try assumption.
  - reflexivity.
  - rewrite u64_lit; lia.
  - rewrite u64_lit by lia. rewrite rw_bytes_max_val. lia.
  - rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
Qed.

Lemma rz_at_read_dir : forall ms mo (fd buf cnt : Z) K,
  at_node segs (NRead fd buf cnt) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  realizes segs (mkCfg (nret ms (efferr EISDIR)) mo) K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo fd buf cnt K Hat [Hh Hl] Hlk Hcnt Hnw HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10 & H11 & H12 & _ & Hwr).
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  eapply rz_det_silent; [exact Hh | exact Hsvc | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_63 _ mo o) by (rewrite in_sysno_pending; reflexivity).
  rewrite in_a0_si, in_a1_si, in_a2_si, H10, H11, H12, fd32_id by (rewrite u64_lit; lia).
  apply (read_dir_outcome _ _ _ _ mo o Hlk).
  apply access_okb_intro. rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
Qed.

Lemma dec_read_file_ok : forall (buf cnt : Z) bs,
  0 <= cnt < 2^62 -> Z.of_nat (length bs) <= cnt ->
  dec_read buf cnt (mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []) = Some (RdData bs).
Proof.
  intros buf cnt bs Hc Hlen. destruct bs as [|b bs'].
  - cbn [delivered_writes length Z.of_nat]. unfold dec_read. rewrite errno_of_lit by lia. reflexivity.
  - cbn [delivered_writes]. unfold dec_read. rewrite bv_eqb_refl, u64_lit by lia.
    rewrite (proj2 (Z.leb_le 1 _)) by (cbn [length]; lia). rewrite (proj2 (Z.leb_le _ cnt) Hlen), Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_impl_read_file : forall (Q : read_ans -> machine_state -> Prop) ms mo (fd buf cnt : Z) p off data K,
  MOK mo ->
  impl segs (at_node segs) (enode (NRead fd buf cnt) (dec_read buf cnt)) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  let bs := file_read data off (Z_to_bv 64 cnt) in
  (forall ms2, Q (RdData bs) ms2 ->
     realizes segs (mkCfg ms2 (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo)) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo fd buf cnt p off data K HM Himpl Hlk Hfs Hcnt Hnw bs HK.
  assert (Hwk : rw_bytes_max < 2^62) by (vm_compute; reflexivity).
  apply (rz_impl_enode (NRead fd buf cnt) (dec_read buf cnt) Q ms mo K HM Himpl).
  intros ms1 Hat Hcont.
  apply (rz_at_read_file ms1 mo fd buf cnt p off data K Hat HM Hlk Hfs Hcnt Hnw).
  apply (Hcont _ (RdData bs) _ K).
  - apply dec_read_file_ok; [lia|]. apply length_file_read_le. lia.
  - destruct HM as [Hh Hl]. split; [exact Hh | exact Hl].
  - exact HK.
Qed.

Lemma rz_impl_read_dir : forall (Q : read_ans -> machine_state -> Prop) ms mo (fd buf cnt : Z) K,
  MOK mo ->
  impl segs (at_node segs) (enode (NRead fd buf cnt) (dec_read buf cnt)) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  (forall ms2, Q (RdErr EISDIR) ms2 -> realizes segs (mkCfg ms2 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo fd buf cnt K HM Himpl Hlk Hcnt Hnw HK.
  apply (rz_impl_enode (NRead fd buf cnt) (dec_read buf cnt) Q ms mo K HM Himpl).
  intros ms1 Hat Hcont.
  apply (rz_at_read_dir ms1 mo fd buf cnt K Hat HM Hlk Hcnt Hnw).
  apply (Hcont _ (RdErr EISDIR) _ K); [| exact HM | exact HK].
  unfold dec_read, efferr, eff0. rewrite errno_of_errno_ret by (unfold EISDIR; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_at_close : forall ms mo (fd : Z) e K,
  at_node segs (NClose fd) ms -> MOK mo ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  realizes segs (mkCfg (nret ms (eff0 (Z_to_bv 64 0))) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo)) K ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros ms mo fd e K Hat [Hh Hl] Hlk HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10).
  eapply rz_det_silent; [exact Hh | exact Hsvc | | | | exact HK]; [| exact Hh | exact Hl].
  intros o. rewrite (syscall_spec_57 _ mo o) by (rewrite in_sysno_pending; reflexivity).
  rewrite in_a0_si, H10, fd32_id by (rewrite u64_lit; lia). exact (close_outcome _ _ mo e o Hlk).
Qed.

Lemma rz_impl_close : forall (Q : sret -> machine_state -> Prop) ms mo (fd : Z) e K,
  MOK mo ->
  impl segs (at_node segs) (enode (NClose fd) dec_close) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  (forall ms2, Q (SVal 0) ms2 -> realizes segs (mkCfg ms2 (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo)) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo fd e K HM Himpl Hlk HK.
  apply (rz_impl_enode (NClose fd) dec_close Q ms mo K HM Himpl).
  intros ms1 Hat Hcont. apply (rz_at_close ms1 mo fd e K Hat HM Hlk).
  apply (Hcont _ (SVal 0) _ K); [| | exact HK].
  - unfold dec_close. apply dec_plain_val; [lia | reflexivity].
  - destruct HM as [Hh Hl]. split; [exact Hh | exact Hl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma open_flags_at_node : forall fl : word,
  Z.ldiff (bv_unsigned fl) (O_CLOEXEC + O_LARGEFILE) = 0 ->
  Z.ldiff (bv_unsigned fl) open_ignored_flags = 0.
Proof.
  intros fl H. unfold open_ignored_flags.
  replace (O_CLOEXEC + O_LARGEFILE + O_NONBLOCK) with (Z.lor (O_CLOEXEC + O_LARGEFILE) O_NONBLOCK) by reflexivity.
  rewrite <- Z.ldiff_ldiff_l, H. reflexivity.
Qed.

Section Openat.
  Variables (ms : machine_state) (mo : Model) (path : list byte).
  Hypothesis Hat : at_node segs (NOpen path) ms.
  Hypothesis HM : MOK mo.

  Let x8 := Z_to_bv 64 56.
  Let i := sys_input segs ms x8.
  Let fds := m_fds mo.

  Lemma open_at_facts :
    ms_svc_pending ms = Some x8 /\ areg ms 10 = AT_FDCWD /\
    Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\ ~ In (Z_to_bv 8 0) path /\
    bytes_in (in_mem i) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]).
  Proof.
    cbn [at_node] in Hat. destruct Hat as (Hsvc & H10 & Hfl & Hnz & Hrom & Hb).
    refine (conj Hsvc (conj H10 (conj _ (conj Hnz _)))).
    - apply open_flags_at_node. exact Hfl.
    - unfold i. rewrite in_mem_si. apply (bytes_at_in segs); assumption.
  Qed.

  Lemma openat_head_at : forall o,
    syscall_spec i mo o <-> openat_spec AT_FDCWD32 (areg ms 11) (areg ms 12) i mo o.
  Proof.
    intros o. destruct open_at_facts as (Hsvc & H10 & _).
    unfold i. rewrite (syscall_spec_56 _ mo o) by (rewrite in_sysno_pending; reflexivity).
    rewrite in_a0_si, in_a1_si, in_a2_si, H10. reflexivity.
  Qed.

  Lemma open_flags_modeled_at : modeled_open_flags (areg ms 12) = true.
  Proof. destruct open_at_facts as (_ & _ & Hfl & _). exact (modeled_open_flags_rd _ Hfl). Qed.

  Lemma path_cstr_at : (length path <= 4095)%nat -> read_cstr (in_mem i) (areg ms 11) = CstrOk path.
  Proof.
    intros Hlen. destruct open_at_facts as (_ & _ & _ & Hnz & Hb). unfold read_cstr.
    rewrite <- (wa_unsigned_id (areg ms 11)). apply read_cstr_aux_bytes_in; [unfold path_max; lia | exact Hnz | exact Hb].
  Qed.

  Lemma path_toolong_at : (4096 <= length path)%nat -> read_cstr (in_mem i) (areg ms 11) = CstrTooLong.
  Proof.
    intros Hlen. destruct open_at_facts as (_ & _ & _ & Hnz & Hb). unfold read_cstr.
    rewrite <- (wa_unsigned_id (areg ms 11)). apply bytes_in_app in Hb as [Hb _].
    apply (read_cstr_aux_toolong_bytes_in path_max path); [unfold path_max; lia | exact Hnz | exact Hb].
  Qed.

  Lemma rz_at_openat_det : forall r K,
    (forall o, syscall_spec i mo o <-> o = Ok (with_copyins (open_reads i (areg ms 11)) (mkEffect r [] [])) mo []) ->
    realizes segs (mkCfg (nret ms (eff0 r)) mo) K ->
    realizes segs (mkCfg ms mo) K.
  Proof.
    intros r K Hiff HK. destruct HM as [Hh Hl]. destruct open_at_facts as (Hsvc & _).
    eapply rz_det_silent; [exact Hh | exact Hsvc | exact Hiff | exact Hh | exact Hl | exact HK].
  Qed.

  Lemma rz_at_openat_toolong : forall K, (4096 <= length path)%nat ->
    realizes segs (mkCfg (nret ms (efferr ENAMETOOLONG)) mo) K -> realizes segs (mkCfg ms mo) K.
  Proof.
    intros K Hlen HK. apply rz_at_openat_det with (r := errno_ret ENAMETOOLONG); [|exact HK].
    intros o. rewrite openat_head_at. apply (openat_toolong_outcome _ _ _ _ mo open_flags_modeled_at). exact (path_toolong_at Hlen).
  Qed.

  Lemma rz_at_openat_empty : forall K, path = [] ->
    realizes segs (mkCfg (nret ms (efferr ENOENT)) mo) K -> realizes segs (mkCfg ms mo) K.
  Proof.
    intros K Hp HK. apply rz_at_openat_det with (r := errno_ret ENOENT); [|exact HK].
    intros o. rewrite openat_head_at. apply (openat_empty_outcome _ _ _ _ mo open_flags_modeled_at).
    rewrite <- Hp. apply path_cstr_at. rewrite Hp. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_at_openat_absent : forall K, (length path <= 4095)%nat -> path <> [] -> path <> dot_path ->
    path <> dotdot_path -> path_has_slash path = false ->
    fs_lookup (m_fs mo) path = None ->
    realizes segs (mkCfg (nret ms (efferr ENOENT)) mo) K -> realizes segs (mkCfg ms mo) K.
  Proof.
    intros K Hlen Hne Hnd Hndd Hsl Hfs HK. apply rz_at_openat_det with (r := errno_ret ENOENT); [|exact HK].
    destruct open_at_facts as (_ & _ & Hfl & _).
    intros o. rewrite openat_head_at.
    apply (openat_absent_outcome _ _ _ _ mo open_flags_modeled_at eq_refl Hfl path);
      [exact (path_cstr_at Hlen) | exact Hne | exact Hnd | exact Hndd | exact Hsl | exact Hfs].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma rz_at_openat_open : forall (mk : word -> Model) KA KB,
    (forall o, syscall_spec i mo o <-> open_out (open_reads i (areg ms 11)) mo mk o) ->
    (forall fd, m_halted (mk fd) = m_halted mo) -> (forall fd, m_vm_lazy (mk fd) = m_vm_lazy mo) ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret ms (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret ms (eff0 (alloc_fd fds))) (mk (alloc_fd fds))) KB ->
    realizes segs (mkCfg ms mo) (t_alt2 KA KB).
  Proof.
    intros mk KA KB Hiff Hmkh Hmkl HA HB. destruct HM as [Hh Hl]. destruct open_at_facts as (Hsvc & _).
    set (rd := open_reads i (areg ms 11)) in *.
    apply (rz_err_or_one segs ms mo x8 openat_errnos ENOMEM
             (fun e => with_copyins rd (efferr e)) (with_copyins rd (eff0 (alloc_fd fds))) (mk (alloc_fd fds)) KA KB
             Hh Hl Hsvc eq_refl (ENOMEM_in_openat_errnos)).
    - intros o. unfold i in Hiff. rewrite Hiff. unfold open_out, fds. split.
      + intros [(e & He & ->) | (_ & ->)]; [left; exists e; auto | right; reflexivity].
      + intros [(e & He & ->) | ->]; [left; exists e; auto | right; auto].
    - rewrite Hmkh. exact Hh.
    - rewrite Hmkl. exact Hl.
    - intros e He. change (nret ms (with_copyins rd (efferr e))) with (nret ms (efferr e)). apply HA. exact He.
    - exact HB.
  Qed.

  Lemma rz_at_openat_dot : forall KA KB, path = dot_path ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret ms (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret ms (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo)) KB ->
    realizes segs (mkCfg ms mo) (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB. destruct open_at_facts as (_ & _ & Hfl & _).
    apply (rz_at_openat_open (fun fd => with_fds (fd_insert fds fd FdDir) mo)); [| reflexivity | reflexivity | exact HA | exact HB].
    intros o. rewrite openat_head_at. apply (openat_dot_outcome _ _ _ _ mo open_flags_modeled_at eq_refl Hfl).
    rewrite <- Hp. apply path_cstr_at. rewrite Hp. cbn. lia.
  Qed.

  Lemma rz_at_openat_file : forall d KA KB, (length path <= 4095)%nat -> path <> [] -> path <> dot_path ->
    path <> dotdot_path -> path_has_slash path = false ->
    fs_lookup (m_fs mo) path = Some d ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (nret ms (efferr e)) mo) KA) ->
    realizes segs (mkCfg (nret ms (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) (FdFile path (Z_to_bv 64 0))) mo)) KB ->
    realizes segs (mkCfg ms mo) (t_alt2 KA KB).
  Proof.
    intros d KA KB Hlen Hne Hnd Hndd Hsl Hfs HA HB. destruct open_at_facts as (_ & _ & Hfl & _).
    apply (rz_at_openat_open (fun fd => with_fds (fd_insert fds fd (FdFile path (Z_to_bv 64 0))) mo));
      [| reflexivity | reflexivity | exact HA | exact HB].
    intros o. rewrite openat_head_at.
    apply (openat_file_outcome _ _ _ _ mo open_flags_modeled_at eq_refl Hfl path d);
      [exact (path_cstr_at Hlen) | exact Hne | exact Hnd | exact Hndd | exact Hsl | exact Hfs].
  Qed.
End Openat.

(* [comment removed for export] *)
Lemma openat_errnos_range : forall e, In e openat_errnos -> 1 <= e <= 4095.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

Lemma rz_impl_openat_err : forall (Q : sret -> machine_state -> Prop) ms mo path (e : Z) K,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  1 <= e <= 4095 ->
  (forall ms1 K', at_node segs (NOpen path) ms1 ->
     realizes segs (mkCfg (nret ms1 (efferr e)) mo) K' -> realizes segs (mkCfg ms1 mo) K') ->
  (forall ms2, Q (SErr e) ms2 -> realizes segs (mkCfg ms2 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo path e K HM Himpl He Hnode HK.
  apply (rz_impl_enode (NOpen path) dec_open Q ms mo K HM Himpl).
  intros ms1 Hat Hcont. apply (Hnode ms1 K Hat).
  apply (Hcont _ (SErr e) _ K); [| exact HM | exact HK].
  unfold dec_open. apply dec_plain_err. exact He.
Qed.

(* [comment removed for export] *)
Lemma rz_impl_openat_absent : forall (Q : sret -> machine_state -> Prop) ms mo path K,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (length path <= 4095)%nat -> path <> [] -> path <> dot_path ->
  path <> dotdot_path -> path_has_slash path = false -> fs_lookup (m_fs mo) path = None ->
  (forall ms2, Q (SErr ENOENT) ms2 -> realizes segs (mkCfg ms2 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo path K HM Himpl Hlen Hne Hnd Hndd Hsl Hfs HK.
  apply (rz_impl_openat_err Q ms mo path ENOENT K HM Himpl ltac:(unfold ENOENT; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (rz_at_openat_absent ms1 mo path Hat HM K' Hlen Hne Hnd Hndd Hsl Hfs HK').
Qed.

Lemma rz_impl_openat_empty : forall (Q : sret -> machine_state -> Prop) ms mo K,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen []) dec_open) (epost Q) ms ->
  (forall ms2, Q (SErr ENOENT) ms2 -> realizes segs (mkCfg ms2 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo K HM Himpl HK.
  apply (rz_impl_openat_err Q ms mo [] ENOENT K HM Himpl ltac:(unfold ENOENT; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (rz_at_openat_empty ms1 mo [] Hat HM K' eq_refl HK').
Qed.

Lemma rz_impl_openat_toolong : forall (Q : sret -> machine_state -> Prop) ms mo path K,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (4096 <= length path)%nat ->
  (forall ms2, Q (SErr ENAMETOOLONG) ms2 -> realizes segs (mkCfg ms2 mo) K) ->
  realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo path K HM Himpl Hlen HK.
  apply (rz_impl_openat_err Q ms mo path ENAMETOOLONG K HM Himpl ltac:(unfold ENAMETOOLONG; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (rz_at_openat_toolong ms1 mo path Hat HM K' Hlen HK').
Qed.

(* [comment removed for export] *)
Lemma rz_impl_openat_file : forall (Q : sret -> machine_state -> Prop) ms mo path d KA KB,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (length path <= 4095)%nat -> path <> [] -> path <> dot_path ->
  path <> dotdot_path -> path_has_slash path = false -> fs_lookup (m_fs mo) path = Some d ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  (forall e ms2, In e openat_errnos -> Q (SErr e) ms2 -> realizes segs (mkCfg ms2 mo) KA) ->
  (forall ms2, Q (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
     realizes segs (mkCfg ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (FdFile path (Z_to_bv 64 0))) mo)) KB) ->
  realizes segs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros Q ms mo path d KA KB HM Himpl Hlen Hne Hnd Hndd Hsl Hfs Hfree Hfd HA HB.
  apply (rz_impl_enode (NOpen path) dec_open Q ms mo (t_alt2 KA KB) HM Himpl).
  intros ms1 Hat Hcont.
  apply (rz_at_openat_file ms1 mo path Hat HM Hfree d KA KB Hlen Hne Hnd Hndd Hsl Hfs).
  - intros e He. pose proof (openat_errnos_range e He) as Her.
    apply (Hcont _ (SErr e) _ KA); [unfold dec_open; apply dec_plain_err; exact Her | exact HM |].
    intros ms2 HQ. exact (HA e ms2 He HQ).
  - rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
    apply (Hcont _ (SVal (bv_unsigned (alloc_fd (m_fds mo)))) _ KB); [| | exact HB].
    + unfold dec_open. apply dec_plain_val; [|rewrite (proj2 (Z.leb_le 3 _)), (proj2 (Z.leb_le _ 4096)) by lia; reflexivity].
      pose proof (bv_unsigned_in_range 64 (alloc_fd (m_fds mo))). lia.
    + destruct HM as [Hh Hl]. split; [exact Hh | exact Hl].
Qed.

Lemma rz_impl_openat_dot : forall (Q : sret -> machine_state -> Prop) ms mo KA KB,
  MOK mo ->
  impl segs (at_node segs) (enode (NOpen dot_path) dec_open) (epost Q) ms ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  (forall e ms2, In e openat_errnos -> Q (SErr e) ms2 -> realizes segs (mkCfg ms2 mo) KA) ->
  (forall ms2, Q (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
     realizes segs (mkCfg ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) FdDir) mo)) KB) ->
  realizes segs (mkCfg ms mo) (t_alt2 KA KB).
Proof.
  intros Q ms mo KA KB HM Himpl Hfree Hfd HA HB.
  apply (rz_impl_enode (NOpen dot_path) dec_open Q ms mo (t_alt2 KA KB) HM Himpl).
  intros ms1 Hat Hcont.
  apply (rz_at_openat_dot ms1 mo dot_path Hat HM Hfree KA KB eq_refl).
  - intros e He. pose proof (openat_errnos_range e He) as Her.
    apply (Hcont _ (SErr e) _ KA); [unfold dec_open; apply dec_plain_err; exact Her | exact HM |].
    intros ms2 HQ. exact (HA e ms2 He HQ).
  - rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
    apply (Hcont _ (SVal (bv_unsigned (alloc_fd (m_fds mo)))) _ KB); [| | exact HB].
    + unfold dec_open. apply dec_plain_val; [|rewrite (proj2 (Z.leb_le 3 _)), (proj2 (Z.leb_le _ 4096)) by lia; reflexivity].
      pose proof (bv_unsigned_in_range 64 (alloc_fd (m_fds mo))). lia.
    + destruct HM as [Hh Hl]. split; [exact Hh | exact Hl].
Qed.

End WithSegs.
