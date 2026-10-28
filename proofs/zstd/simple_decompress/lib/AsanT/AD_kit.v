(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree Keeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree Stdio Driver AsanCtrl AsanEmbed AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto AMalloc_iface AProg_kit AHarness_iface
     F_syscalls StdioFiles Stdio_kit ADriver_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition dcli (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  aclient_addr CI LB SP a \/ (shad ATOP <= a < shad SP).

Lemma magree_of_dpost : forall CI LB SP m m',
  aheap_pres CI LB SP m m' -> astk_shadow_pres SP m m' -> magree bsegs (dcli CI LB SP) m m'.
Proof.
  intros CI LB SP m m' HP HS a Ha [Hc | Hs].
  - apply HP; assumption.
  - pose proof (HS a Hs) as E. split; [exact E|]. unfold wview, mrd. rewrite E. auto.
Qed.

Lemma dcli_weaken : forall CI LB LB' SP SP' a,
  dcli CI LB' SP' a -> SP <= SP' -> SP' <= 2^47 -> SP mod 8 = 0 -> (forall b, In b LB' -> In b LB) -> dcli CI LB SP a.
Proof.
  intros CI LB LB' SP SP' a H HS HS' H8 HL. destruct H as [H | H].
  - left. revert H. unfold aclient_addr, in_block, in_fake. intros [X|[X|[(b & Hb & R)|(a' & X & E)]]].
    + left; lia. + right; left; exact X.
    + right; right; left. exists b. split; [apply HL; exact Hb| exact R].
    + right; right; right. exists a'. split; [| exact E].
      destruct X as [X|[X|(c & A & n & Hin & R)]]; [left; lia| right; left; exact X| right; right].
      exists c, A, n. split; [apply HL; exact Hin| exact R].
  - (* [comment removed for export] *)
    left. right; right; right. exists (8 * (a - ASHOFF)). split.
    + left. rewrite !shad_div in *. unfold ASHOFF in *. atop_facts. pose proof ATOP_al16. Z.div_mod_to_equations. lia.
    + rewrite shad_div. unfold ASHOFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
  Variable P : Z -> Prop.
  Variables (m m' : amem).
  Hypothesis AG : magree bsegs P m m'.

  Lemma stdout_file_magree : forall so, (forall a, (RSTDOUT <= a < RSTDOUT + 232) \/ (RSTDOUT_BUF <= a < RSTDOUT_BUF + 1024) -> P a) ->
    stdout_file m so -> stdout_file m' so.
  Proof.
    intros so HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
    exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
    - eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
    - eapply rw_cells_magree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
  Qed.

  Lemma stderr_file_magree : (forall a, RSTDERR <= a < RSTDERR + 232 -> P a) -> stderr_file m -> stderr_file m'.
  Proof.
    intros HP (flags & mode & e & wend & tail & F1). exists flags, mode, e, wend, tail.
    eapply rw_cells_magree; [exact AG| exact F1|]. intros a Ha. apply HP. cbn in Ha. lia.
  Qed.

  Lemma shadow_bytes_magree : forall s1 s2 f, (forall a, s1 <= a < s2 -> P a) -> shadow_bytes m s1 s2 f -> shadow_bytes m' s1 s2 f.
  Proof.
    intros s1 s2 f HP SB. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
    intros s Hs. destruct (AG s ltac:(lia) ltac:(apply HP; lia)) as [E _]. exact E.
  Qed.

  Lemma unpoisoned_magree : forall lo hi, (forall a, shad lo <= a <= shad (hi - 1) -> P a) -> 0 <= lo -> hi <= KEND ->
    unpoisoned m lo hi -> unpoisoned m' lo hi.
  Proof.
    intros lo hi HP H0 H1 U. eapply unpoisoned_agree; [exact U|].
    intros s Hs. destruct (AG s ltac:(rewrite !shad_div in Hs; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia) ltac:(apply HP; lia)) as [E _]. exact E.
  Qed.

  Lemma rclean_magree : forall r, (forall a, shad (r_rlo r) <= a < shad (r_rhi r) -> P a) -> rclean m r -> rclean m' r.
  Proof.
    intros r HP [(U & HL & W & AB) LT]. pose proof HL as (H1 & H2 & H3 & H4 & H5 & H6). split; [| exact LT].
    split; [| split; [exact HL| split; [| exact AB]]].
    - eapply unpoisoned_magree; [| lia | unfold KEND in *; lia | exact U].
      intros a Ha. apply HP. pose proof (shad_mono (r_rlo r) (r_lo r) H1). pose proof (shad_mono (r_hi r - 1) (r_rhi r - 1) ltac:(lia)).
      assert (shad (r_rhi r - 1) < shad (r_rhi r)) by (rewrite !shad_div; Z.div_mod_to_equations; lia). lia.
    - eapply wr_at_magree; [exact AG| exact W|]. intros a Ha. apply HP. lia.
  Qed.

  Lemma rodata_sh0_magree : (forall a, shad 0x10000 <= a < shad 0x210c0 -> P a) -> rodata_sh0 m -> rodata_sh0 m'.
  Proof.
    intros HP [SB W]. split; [eapply shadow_bytes_magree; [exact HP| exact SB]|].
    eapply wr_at_magree; [exact AG| exact W|]. intros a Ha. apply HP. lia.
  Qed.

  (* [comment removed for export] *)
End Transport.

(* [comment removed for export] *)
Lemma RSTDOUT_eq : RSTDOUT = 0xcb9f8. Proof. reflexivity. Qed.
Lemma RSTDOUT_BUF_eq : RSTDOUT_BUF = 0x6233c0. Proof. reflexivity. Qed.
Lemma RSTDERR_eq : RSTDERR = 0xcb908. Proof. reflexivity. Qed.
Lemma shad_lit : forall a, shad a = 0x7fff8000 + a / 8. Proof. intros; apply shad_div. Qed.

(* [comment removed for export] *)
Lemma aatexit_cells_agree : forall (P : Z -> Prop) reg m m', magree bsegs P m m' ->
  (forall a, (0x622d00 <= a < 0x622d30) \/ (0x622e20 <= a < 0x622e30) -> P a) -> aatexit_cells reg m -> aatexit_cells reg m'.
Proof.
  intros P reg m m' AG HP AC. unfold aatexit_cells, AATEXIT in *.
  decompose [and] AC. repeat match goal with |- _ /\ _ => split end.
  all: eapply rw_cells_magree; [exact AG | eassumption | intros a Ha; apply HP; cbn in Ha; lia].
Qed.
Lemma aincb0_agree : forall (P : Z -> Prop) m m', magree bsegs P m m' -> (forall a, 0x602354 <= a < 0x602355 -> P a) -> aincb0 m -> aincb0 m'.
Proof.
  intros P m m' AG HP AC. unfold aincb0, AAEF_INCB in *. eapply rw_cells_magree; [exact AG | exact AC | intros a Ha; apply HP; cbn in Ha; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Relro.
  Variable AI : AMallocIface.

  Lemma relro_C8 : forall L RNG st LB m A v,
    AHEAP AI L RNG st LB m -> ARELRO_LO <= A -> A + 8 <= ARELRO_HI ->
    rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
    rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
  Proof.
    intros L RNG st LB m A v AH HLO HHI HB. pose proof (AI_relro AI L RNG st LB m AH) as R.
    eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
      | exact HB | unfold ARELRO_LO in *; lia | rewrite length_le8; unfold ARELRO_HI in *; lia ]
      | cbn; split; exact I | reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma drv_got_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    rw_cells bsegs m AGOT_STDERRP [C8 (Z_to_bv 64 ASTDERRP)]
    /\ rw_cells bsegs m ASTDERRP [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs m AGOT_FUZZ_INIT [C8 (Z_to_bv 64 AFUZZ_INIT)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold AGOT_STDERRP, ASTDERRP, AGOT_FUZZ_INIT, AFUZZ_INIT, got_ssp, ssp_guard.
    repeat match goal with |- _ /\ _ => split end;
      (eapply relro_C8; [exact AH | unfold ARELRO_LO; lia | unfold ARELRO_HI; lia | vm_compute; reflexivity]).
  Qed.
End Relro.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Lemma land3_range : forall c, 0 <= c -> 0 <= Z.land c 3 <= 3.
Proof.
  intros c Hc. split; [apply Z.land_nonneg; lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c 4 ltac:(lia)). change (2^2) with 4. lia.
Qed.

Lemma snez_norm : forall rv, -2^63 < rv < 2^63 -> Z.b2z (0 <? Z.land rv 18446744073709551615) = (if rv =? 0 then 0 else 1).
Proof.
  intros rv Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eqb_spec rv 0) as [->|NE]; [reflexivity|].
  destruct (Z.ltb_spec0 0 (rv mod 2^64)) as [L|G]; [reflexivity|]. exfalso.
  pose proof (Z.mod_pos_bound rv (2^64) ltac:(lia)). assert (E : rv mod 2^64 = 0) by lia.
  apply Znumtheory.Zmod_divide in E; [| lia]. destruct E as [q E]. assert (q = 0) by lia. subst q. lia.
Qed.

Lemma Forall_skipn' : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [exact H|]. destruct l as [|x l]; cbn; [constructor|].
  inversion H; subst. apply IH. assumption.
Qed.

Lemma unsigned_wz_mod32 : forall r, bv_unsigned (Z_to_bv 64 r) mod 2^32 = r mod 2^32.
Proof.
  intros r. rewrite unsigned_lit_wrap. apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section ApsKeeps.
  Context {B : Type} (f : APS -> B).
  Hypothesis FSO : forall v s, f (aset_so v s) = f s.

  Lemma a_upd_so_k : forall g, keeps f (upd_so aps_so aset_so g).
  Proof. intros g. unfold upd_so. apply keeps_upd. intros s. apply FSO. Qed.
  Lemma a_rd_so_k : keeps f (rd_so (St:=APS) aps_so).
  Proof. unfold rd_so. keeps_tac. Qed.
  Lemma a_stdio_write_loop_k : forall fuel fd iov, keeps f (stdio_write_loop (St:=APS) fuel fd iov).
  Proof. induction fuel as [|fuel IH]; intros fd iov; cbn; keeps_tac. Qed.
  Lemma a_stdio_write_k : forall fd buf s, keeps f (stdio_write (St:=APS) fd buf s).
  Proof. intros fd buf s. unfold stdio_write. pose proof a_stdio_write_loop_k. keeps_tac. Qed.
  Lemma a_stdout_stdio_write_k : forall s, keeps f (stdout_stdio_write aps_so aset_so s).
  Proof. intros s. unfold stdout_stdio_write. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdio_write_k. keeps_tac. Qed.
  Lemma a_stdout_writefn_k : forall s, keeps f (stdout_writefn aps_so aset_so s).
  Proof. intros s. unfold stdout_writefn. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdout_stdio_write_k. keeps_tac. Qed.
  Lemma a_stdout_towrite_k : keeps f (stdout_towrite aps_so aset_so).
  Proof. unfold stdout_towrite. apply a_upd_so_k. Qed.
  Lemma a_stdout_fwritex_k : forall s, keeps f (stdout_fwritex aps_so aset_so s).
  Proof. intros s. unfold stdout_fwritex. pose proof a_rd_so_k. pose proof a_upd_so_k. pose proof a_stdout_writefn_k. pose proof a_stdout_towrite_k. keeps_tac. Qed.
  Lemma a_out_pieces_k : forall ps, keeps f (out_pieces aps_so aset_so ps).
  Proof. induction ps as [|p ps IH]; cbn; [apply keeps_ret|]. pose proof a_stdout_fwritex_k. keeps_tac. Qed.
  Lemma a_s_emit_k : forall v, keeps f (s_emit aps_so aset_so v).
  Proof. intros v. unfold s_emit, stdout_vprintf. pose proof a_stdout_towrite_k. pose proof a_out_pieces_k. keeps_tac. Qed.
End ApsKeeps.

Lemma s_emit_aps_m : forall v, keeps aps_m (s_emit aps_so aset_so v).
Proof. intros v. apply a_s_emit_k. intros; reflexivity. Qed.
(* [comment removed for export] *)
Definition aps_mr (s : APS) : astate * list (Z * Z) := (aps_m s, aps_resv s).
Lemma s_emit_aps_mr : forall v, keeps aps_mr (s_emit aps_so aset_so v).
Proof. intros v. apply a_s_emit_k. intros; reflexivity. Qed.
(* [comment removed for export] *)
Definition aps_mra (s : APS) : astate * list (Z * Z) * Z := (aps_m s, aps_resv s, aps_atop s).
Lemma s_emit_aps_mra : forall v, keeps aps_mra (s_emit aps_so aset_so v).
Proof. intros v. apply a_s_emit_k. intros; reflexivity. Qed.

Lemma implF_etall : forall {R} RNG (t : itree node (exc R)) (P : R -> Prop) (Q : R -> footprint -> machine_state -> Prop) ms,
  implS bsegs RNG t (epostF Q) ms -> tall P t ->
  implS bsegs RNG t (epostF (fun r RNG' ms' => Q r RNG' ms' /\ P r)) ms.
Proof.
  intros R RNG t. revert RNG. induction t as [[|r]|n k IH]; cbn; intros RNG P Q ms H HP.
  - exact H.
  - eapply evtF_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp RNG' HF. apply IH; [apply Hk; exact HF| apply HP].
Qed.

Lemma implMA_keeps : forall {B A} (f : APS -> B) RNG (c : @Monad.M APS A) s Q ms,
  implMA RNG c s Q ms -> keeps f c -> implMA RNG c s (fun r s' RNG' ms' => Q r s' RNG' ms' /\ f s' = f s) ms.
Proof.
  intros B A f RNG c s Q ms H K. unfold implMA in *.
  eapply implF_epost_mono; [eapply implF_etall; [exact H| apply K]|]. cbn. intros [a s'] RNG' ms' [HQ E]. split; [exact HQ| exact E].
Qed.
End CANSEC2.
