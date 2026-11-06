(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx X_ax.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition e_target_run : Z := 0x1f2ec4.
Definition e_emit : Z := 0x1f3050.
(* [comment removed for export] *)
Definition p_loop : Z := 0x1f2f80.
Definition p_join : Z := 0x1f2f0c.

(* [comment removed for export] *)
Definition tr_calls (L : Z) (c0 : byte) : Z := if L =? 0 then 1 else Z.land (bv_unsigned c0) 3 + 1.

(* [comment removed for export] *)
Definition tr_frame (m : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 s4 s5 : word) : Prop :=
  exists junk (s6 s7 : word), rw_cells asegs m (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition libc_cells (m : word -> option byte) : Prop :=
  exists (cdt thr sec : byte) (tm1 : word), rw_cells asegs m 0xbc8160 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].

(* [comment removed for export] *)
Definition ax_chunks (k : bool) (fin : byte) (p1 p2 : list byte) (m : word -> option byte) : Prop :=
  rw_cells asegs m 0xbc7f20 (ax_cells k fin p1 p2) /\ rw_cells asegs m 0xbc8040 (ax_acells k).

(* [comment removed for export] *)
Definition pro_W (sp : Z) : list (Z * Z) := [(sp - 128, sp); (0xbc7f20, 0xbc7f50); (0xbc8040, 0xbc8050); (TR_INIT, TR_INIT + 1)].

Lemma ax_chunks_agree : forall k fin p1 p2 m m', ax_chunks k fin p1 p2 m ->
  agree_on (fun x => 0xbc7f20 <= x < 0xbc7f50 \/ 0xbc8040 <= x < 0xbc8050) m m' -> wmono asegs m m' -> ax_chunks k fin p1 p2 m'.
Proof.
  intros k fin p1 p2 m m' [A1 A2] AG WM. split.
  - apply (rw_cells_agree asegs m m' _ _ A1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize ax_cells Nat.add length] in Hx. cbv beta. lia.
  - apply (rw_cells_agree asegs m m' _ _ A2); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize ax_acells Nat.add length] in Hx. cbv beta. lia.
Qed.
Lemma libc_cells_agree : forall m m', libc_cells m -> agree_on (fun x => 0xbc8160 <= x < 0xbc8168) m m' -> wmono asegs m m' -> libc_cells m'.
Proof.
  intros m m' (c1 & c2 & c3 & t & C) AG WM. exists c1, c2, c3, t.
  apply (rw_cells_agree asegs m m' _ _ C); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma tr_pro_latch : forall (sp cp L pp plen : Z) (k : bool) (fin : byte) (p1 p2 : list byte)
    (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z),
  stk asegs m lo sp -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 ->
  0 < cp < 2^47 -> 0 <= L < 32768 -> 0 < pp < 2^47 -> 0 <= plen < 2^26 ->
  AXA k fin p1 p2 m -> libc_cells m -> ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0x1f3098)] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (fin' : byte) (m' : word -> option byte),
                 ms' = MS (mkR ra' (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
                               (Z_to_bv 64 pp) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 L) (Z_to_bv 64 cp)
                               (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 p_join) fc None m' (seg_rom asegs)
       /\ munch (pro_W sp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ tr_frame m' sp ra s0 s1 s2 s3 s4 s5 /\ stk asegs m' lo (sp - 80) /\ AXA true fin' p1 p2 m' /\ libc_cells m')
    (entry_st ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_target_run m).
Proof.
  intros until lo. intros ST SL LO U16 UT Hcp HL Hpp Hpl AX LC GI MI.
unfold entry_st, e_target_run. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
pose proof (wmono_refl asegs m) as WM.
assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
destruct AX as (ATX & ATA & LT). assert (AXC : ax_chunks k fin p1 p2 m) by (split; assumption). clear ATX ATA.
unfold AX_LATCH in LT. unfold GOT_LLVMINIT in GI.
assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
assert (EP : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
destruct k.
- (* [comment removed for export] *)
  pose proof (munch_refl [(sp - 128, sp)] m) as MU.
  carve_frame 80%nat ST.
  do 15 step. step. step. step. if_false.
  apply evt_done. do 16 eexists. exists fin, m0.
  split; [unfold p_join; reflexivity|].
  assert (AG : agree_on (fun x => 0x10000 <= x < 0xbca000) m m0).
  { apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn. split; [lia| exact I]. }
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn in Hx |- *; tauto|].
  split; [exact WM|]. split; [exact MI|].
  split; [do 3 eexists; replace (sp - 80) with (sp + -80) by lia; exact FR|].
  split; [replace (sp - 80) with (sp + -80) by lia; exact ST|].
  split; [split; [| split]; [..| exact LT] |].
  + exact (proj1 (ax_chunks_agree _ _ _ _ m m0 AXC ltac:(eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in *; lia) WM)).
  + exact (proj2 (ax_chunks_agree _ _ _ _ m m0 AXC ltac:(eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in *; lia) WM)).
  + exact (libc_cells_agree m m0 LC ltac:(eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in *; lia) WM).
- (* [comment removed for export] *)
  pose proof (munch_refl (pro_W sp) m) as MU. unfold pro_W, TR_INIT in MU.
  pose proof (munch_refl [(sp - 128, sp); (0xba3190, 0xba3191)] m) as MU2.
  carve_frame 80%nat ST.
  do 15 step. step. step. step. if_true.
  step. step.
  change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))).
  mem_after_store.
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (AG1 : agree_on (fun x => 0x10000 <= x < 0xbca000 /\ x <> 0xba3190) m mc)
      by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn; split; [lia|]; split; [lia| exact I]);
    destruct (ax_chunks_agree _ _ _ _ m mc AXC ltac:(eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; lia) WM) as [ATX ATA];
    pose proof (libc_cells_agree m mc LC ltac:(eapply agree_sub; [exact AG1|]; intros x Hx; cbv beta in *; lia) WM) as (cdt & thr & sec & tm1 & LIBC);
    clear AG1 MU2
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  assert (EU80 : bv_unsigned (Z_to_bv 64 (sp + -80)) = sp + -80) by (apply unsigned_lit; lia);
  eapply evt_cut; [eapply atexit_spec; [rewrite EU80; exact ST | exact ATX | exact ATA | exact LIBC | exact MI | rewrite EU80; lia | lia] | post_call asegs mc]
  end.
  rename x13 into m2. rename PC into ST. rename PC0 into ATX. rename POST into ATA. rename MI0 into MI.
  rewrite EU80 in ST. unfold ax_cells, ax_acells, ax_slot, AX_CALL, AX_GUARD, AX_COVD in ATX, ATA.
  (* [comment removed for export] *)
  step. if_true.
  step. step. step. if_false.
  step. step. step.
  step.
  change (Z_to_le_bytes 8 5955312) with (le8 (Z_to_bv 64 5955312)). mem_after_store.
  apply (rw_cells_merge asegs _ _ [] [C8 _] _) in FR; cbn [app cells_size csize Nat.add] in FR.
  step. step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
  apply evt_done; do 16 eexists; exists (Z_to_bv 8 0), mc end.
  split; [unfold p_join; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [do 3 eexists; replace (sp - 80) with (sp + -80) by lia; exact FR|].
  split; [exact ST|].
  split; [split; [exact ATX| split; [exact ATA| exact LT]]|].
  exists cdt, thr, sec, tm1; exact LIBC.
Qed.

(* [comment removed for export] *)
Lemma tr_pro_copy : forall (sp cp L pp plen : Z) (c0 : byte)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  0 < cp < 2^47 -> 0 <= L < 32768 -> 0 < plen < 2^26 ->
  (0 < L -> bytes_at asegs m cp [c0]) -> (SEGTOP_A <= cp \/ cp + 1 <= 0x10000) -> mem_inv asegs m ->
  evt asegs (eq (entry_st (Z_to_bv 64 0x1f2f28) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
                    (Z_to_bv 64 pp) (Z_to_bv 64 plen) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp)
                    (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m))
    (MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 p_join) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hcp HL Hpl HC0 Hcseg MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold SEGTOP_A in Hcseg.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_true. step. step.
    apply evt_done. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_eq L 0) LZ). reflexivity.
  - step. if_false.
    pose proof (u8ro_read asegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_false. step. step.
    apply evt_done. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_neq L 0) LNZ). rewrite ZX. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma tr_pro_empty : forall (sp cp L pp : Z) (c0 : byte)
    (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  0 < cp < 2^47 -> 0 <= L < 32768 ->
  (0 < L -> bytes_at asegs m cp [c0]) -> (SEGTOP_A <= cp \/ cp + 1 <= 0x10000) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists a0' : word,
      ms' = MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 TR_EMPTY) a0' a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0)) (Z_to_bv 64 0)
                    (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 p_loop) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 p_join) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros Hcp HL HC0 Hcseg MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold SEGTOP_A in Hcseg.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_false. step. step. step. step.
    apply evt_done. eexists. unfold tr_calls, p_loop, TR_EMPTY, TR_INIT. rewrite (proj2 (Z.eqb_eq L 0) LZ). reflexivity.
  - step. if_false.
    pose proof (u8ro_read asegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_true. step. step. step. step.
    apply evt_done. eexists. unfold tr_calls, p_loop, TR_EMPTY, TR_INIT. rewrite (proj2 (Z.eqb_neq L 0) LNZ). rewrite ZX. reflexivity.
Qed.

