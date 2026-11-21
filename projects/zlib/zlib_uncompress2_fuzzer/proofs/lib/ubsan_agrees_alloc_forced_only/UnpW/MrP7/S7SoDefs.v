(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive
  RefMemcpyLib AgentLib SpecConsts SymDriveX ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Spec.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7ExitBase S7StdioDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition so_dom (i : Z) : Prop := 0x22d78 <= i < 0x22e60 \/ 0x93688 <= i < 0x93a90.

Definition so_pristine (mem : word -> option byte) : Prop :=
  forall i, so_dom i -> mem (Z_to_bv 64 i) = None.

Record so_wmode {RCa1 : RunCtx}  (mem : word -> option byte) (k : nat) : Prop := SO_WMODE {
  som_k     : (Z.of_nat k <= 512)%Z;
  som_flags : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d78) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  som_rpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  som_rend  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  som_wend  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93a90));
  som_wpos  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22da0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x93690 + 2 * Z.of_nat k)));
  som_wbase : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22db0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93690));
  som_write : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22dc0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1b5d4));
  som_buf   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22dd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93690));
  som_bsz   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22dd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  som_fd    : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22df0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  som_mode  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e00) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  som_lock  : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e04) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  som_lbf   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e08) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  som_bytes : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93690) (length (Spec.zero_lines k)) = Some (Spec.zero_lines k)
}.
Arguments SO_WMODE {RCa1}.  (* a worker (A1) tool *)

(* [comment removed for export] *)
Definition so_agree (mem mem' : word -> option byte) : Prop :=
  forall i, so_dom i -> mem' (Z_to_bv 64 i) = mem (Z_to_bv 64 i).

Lemma zero_lines_length : forall k, length (Spec.zero_lines k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [Spec.zero_lines length]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma so_agree_refl : forall mem, so_agree mem mem.
Proof. intros mem i _. reflexivity. Qed.

Lemma so_agree_trans : forall m1 m2 m3, so_agree m1 m2 -> so_agree m2 m3 -> so_agree m1 m3.
Proof. intros m1 m2 m3 A B i Hi. rewrite (B i Hi). apply A, Hi. Qed.

(* [comment removed for export] *)
Lemma so_agree_of_frame : forall mem mem' rs,
  frame_mod mem mem' rs ->
  (forall i, so_dom i -> outside (Z_to_bv 64 i) rs) ->
  so_agree mem mem'.
Proof. intros mem mem' rs [He _] Ho i Hi. apply He, Ho, Hi. Qed.

Lemma so_pristine_frame : forall mem mem', so_pristine mem -> so_agree mem mem' -> so_pristine mem'.
Proof. intros mem mem' P A i Hi. rewrite (A i Hi). apply P, Hi. Qed.

Lemma so_rdn_agree {RCa1 : RunCtx}  : forall mem mem' a n,
  so_agree mem mem' -> (0 <= a)%Z -> (forall i, a <= i < a + Z.of_nat n -> so_dom i) -> (a + Z.of_nat n <= 0x94000)%Z ->
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 a) n = rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 a) n.
Proof.
  intros mem mem' a n A Ha Hd Hhi.
  apply rdn_ext; [rewrite u64_lit by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply A, Hd. lia.
Qed.

Lemma so_wmode_frame {RCa1 : RunCtx}  : forall mem mem' k, so_wmode mem k -> so_agree mem mem' -> so_wmode mem' k.
Proof.
  intros mem mem' k [Hk F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 FB] A.
  constructor; try exact Hk;
    try (rewrite (so_rdn_agree mem mem' _ _ A); [eassumption | lia | unfold so_dom; cbn; lia | cbn; lia]).
  rewrite (so_rdn_agree mem mem' _ _ A); [exact FB | lia | | ].
  - rewrite zero_lines_length. unfold so_dom. lia.
  - rewrite zero_lines_length. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma so_wmode_pending {RCa1 : RunCtx}  : forall mem k can,
  so_wmode mem k -> (1 <= k)%nat -> ssp_cells mem can ->
  stdout_pending mem 0x93690 (0x93690 + 2 * Z.of_nat k) (Z_to_bv 64 0x93690) (Z_to_bv 64 1024) (Z_to_bv 64 0) can
                 (Spec.zero_lines k).
Proof.
  intros mem k can [Hk F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 FB] K1 SSP.
  pose proof rw_bytes_max_ge17 as RW.
  constructor; try assumption; try (rewrite zero_lines_length; lia); lia.
Qed.

(* [comment removed for export] *)
Lemma so_wmode_clean {RCa1 : RunCtx}  : forall mem, so_wmode mem 0 -> exists wp rp, file_clean mem 0x22d78 wp rp.
Proof.
  intros mem [Hk F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 FB].
  exists (Z_to_bv 64 0x93690), (Z_to_bv 64 0). unfold file_clean. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma so_pristine_clean {RCa1 : RunCtx}  : forall mem, so_pristine mem -> exists wp rp, file_clean mem 0x22d78 wp rp.
Proof.
  intros mem P. exists (Z_to_bv 64 0), (Z_to_bv 64 0). unfold file_clean.
  assert (RD : forall a n, 0x22d78 <= a -> a + Z.of_nat n <= 0x22e60 ->
                 rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 a) n = rdn (run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 a) n).
  { intros a n Ha Hn. apply SymDriveX.rdn_untouched; [lia | lia |]. intros i Hi. apply P. left. lia. }
  repeat split; (rewrite RD by (cbn; lia)); vm_compute; apply f_equal;
    repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PF1_FR : Z := 1200.

(* [comment removed for export] *)
Record pf_pre {RCa1 : RunCtx}  (mem : word -> option byte) (sp : word) (can : Z) : Prop := PF_PRE {
  pp_sp16  : bv_unsigned sp mod 16 = 0;
  pp_splo  : 4294967296 + PF1_FR <= bv_unsigned sp;
  pp_sphi  : bv_unsigned sp <= 0x7fffffffffff;
  pp_stk   : stk_ok (run_segments RSEGS rc_inp rc_sp rc_mb) mem sp PF1_FR;
  pp_img   : forall i, 0x10000 <= i < 0x21c48 \/ 0x21c50 <= i < 0x22000 -> mem (Z_to_bv 64 i) = None;
  pp_got   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93228));
  pp_can   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93228) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  pp_can64 : 0 <= can < 2 ^ 64 }.
Arguments PF_PRE {RCa1}.  (* a worker (A1) tool *)

(* [comment removed for export] *)
Definition so_regions (sp : word) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp - PF1_FR), PF1_FR); (Z_to_bv 64 0x22d78, 232); (Z_to_bv 64 0x93688, 1032)].

(* [comment removed for export] *)
Lemma pf_pre_frame {RCa1 : RunCtx}  : forall mem mem' sp can,
  pf_pre mem sp can -> frame_mod mem mem' (so_regions sp) -> pf_pre mem' sp can.
Proof.
  intros mem mem' sp can [P1 P2 P3 P4 P5 P6 P7 P8] FM. pose proof FM as [He Hg].
  assert (OUT : forall i, 0x10000 <= i < 0x22d78 \/ 0x22e60 <= i < 0x93688 -> outside (Z_to_bv 64 i) (so_regions sp)).
  { intros i Hi. unfold so_regions, PF1_FR in *. cbn [outside]. unfold in_rng.
    rewrite !u64_lit by lia. lia. }
  constructor; try assumption.
  - intros a n H1 H2. eapply store_ok_mono; [exact Hg | apply P4; assumption].
  - intros i Hi. rewrite He; [apply P5; exact Hi | apply OUT; lia].
  - rewrite (rdn_ext (run_segments RSEGS rc_inp rc_sp rc_mb) 8 mem' mem); [exact P6 | rewrite u64_lit by lia; cbn; lia |].
    intros x Hx. rewrite u64_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply He, OUT. cbn in Hx. lia.
  - rewrite (rdn_ext (run_segments RSEGS rc_inp rc_sp rc_mb) 8 mem' mem); [exact P7 | rewrite u64_lit by lia; cbn; lia |].
    intros x Hx. rewrite u64_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply He, OUT. cbn in Hx. lia.
Qed.

(* [comment removed for export] *)
Definition printf0_first_stmt {RCa1 : RunCtx}  : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (sp : word) (can : Z) (K : TSet),
    pf_pre mem sp can -> so_pristine mem ->
    getr regs 1 = Z_to_bv 64 0x14c78 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    m_channel_reader model = true ->   (* a worker port727: LibWritev's premise *)
    m_halted model = None -> m_vm_lazy model = [] ->
    K [] ->
    (forall regs' mem',
       keeps_cs regs regs' -> frame_mod mem mem' (so_regions sp) -> so_wmode mem' 0 ->
       realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs' (Z_to_bv 64 0x14c78) mem' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) K) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x14d24) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
             (t_emit (Spec.W 1 [Z_to_bv 8 0x30; Z_to_bv 8 0x0a]) K).

(* [comment removed for export] *)
Definition printf0_next_stmt {RCa1 : RunCtx}  : Prop :=
  forall (regs : bvmap 5 word) (mem rom : word -> option byte) (sp : word) (can : Z) (k : nat),
    pf_pre mem sp can -> so_wmode mem k -> (k < 512)%nat ->
    getr regs 1 = Z_to_bv 64 0x14c78 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs' mem',
      msteps (run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 0x14d24) mem rom) (mkst regs' (Z_to_bv 64 0x14c78) mem' rom)
      /\ keeps_cs regs regs' /\ frame_mod mem mem' (so_regions sp) /\ so_wmode mem' (S k).

(* [comment removed for export] *)
Definition printf0_next_rz_stmt {RCa1 : RunCtx}  : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (sp : word) (can : Z) (k : nat) (T : TSet),
    pf_pre mem sp can -> so_wmode mem k -> (k < 512)%nat ->
    getr regs 1 = Z_to_bv 64 0x14c78 -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 0 ->
    m_halted model = None -> m_vm_lazy model = [] ->
    (forall regs' mem',
       keeps_cs regs regs' -> frame_mod mem mem' (so_regions sp) -> so_wmode mem' (S k) ->
       realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs' (Z_to_bv 64 0x14c78) mem' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) T) ->
    realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x14d24) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) T.

Lemma printf0_next_rz_of {RCa1 : RunCtx}  : printf0_next_stmt -> printf0_next_rz_stmt.
Proof.
  intros H regs mem model sp can k T PP SO Hk R1 R2 R11 Hh Hl HK.
  destruct (H regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp can k PP SO Hk R1 R2 R11) as (regs' & mem' & Hms & Hcs & Hfm & Hso).
  eapply rz_msteps; [exact Hh | exact Hl | exact Hms |]. apply HK; assumption.
Qed.
