(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its module paths, module names and numbers changed; 258 of its 325 lines of code are new or changed and 715 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_close.v, with its module paths, module names, addresses and numbers changed; 65 of its 87 lines of code are new or changed and 303 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel strchr_c.
Import ListNotations.
Open Scope Z_scope.

Definition MALLOC_FN : Z := 0x17514.
(* The mode link's caller passes is "w" at 0x10564 (MemFile.link_mf_mode_bytes); pcap's walk took "rb". strchr's
   8-byte reads past the string's NUL take the two bytes after it ("na" of "nan"); "rwa" at 0x10594 ends 8-aligned
   (0x10598), so it needs none. *)
Definition MODE_STR : list byte := [Z_to_bv 8 119].
Definition MODE_SLACK : list byte := [Z_to_bv 8 110; Z_to_bv 8 97].
Definition RWA_STR : list byte := [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97].
Definition RWA_SLACK : list byte := [].

Lemma mode_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10564 (MODE_STR ++ Z_to_bv 8 0 :: MODE_SLACK).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  cbn [MODE_STR MODE_SLACK app ro_bytes]. unfold ro_byte. repeat split; vm_compute; reflexivity.
Qed.

Lemma mode_bytes_w : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10564 (MODE_STR ++ Z_to_bv 8 0 :: []).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  cbn [MODE_STR app ro_bytes]. unfold ro_byte. repeat split; vm_compute; reflexivity.
Qed.

Lemma rwa_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10594 (RWA_STR ++ Z_to_bv 8 0 :: RWA_SLACK).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  cbn [RWA_STR RWA_SLACK app ro_bytes]. unfold ro_byte. repeat split; vm_compute; reflexivity.
Qed.

Definition fmemopen_pro_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists sp' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s4' t3 t4 t5 t6 m1,
    ms' = MS (mkR (Z_to_bv 64 0x1933c) sp' gp tp t0 t1 t2 s0 a0 a0' a1' a2' a3 a4 a5 a6 a7 a1 a2 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 MALLOC_FN) fc None m1 (seg_rom rsegs)
    /\ bv_unsigned sp' = bv_unsigned sp - 48 /\ a0' = Z_to_bv 64 1304 /\ s4' = Z_to_bv 64 0
    /\ rw_cells rsegs m1 (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (bv_unsigned sp - 48).

Lemma fmemopen_pro : strchr_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 0x97000 <= lo ->
    a2 = Z_to_bv 64 0x10564 -> bv_unsigned a0 <> 0 -> mem_inv rsegs m ->
    evt rsegs (fmemopen_pro_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x192a0) fc None m (seg_rom rsegs)).
Proof.
  intros HSTRCHR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO HI EA2 A0 MI.
  subst a2. unfold strchr_contract in HSTRCHR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (U48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HSTRCHR with (lo := lo) (str := MODE_STR) (slack := MODE_SLACK);
                       [ rewrite U48; eassumption | rewrite unsigned_lit by lia; apply mode_bytes; eassumption
                       | cbv; intros [H|H]; discriminate H || exact H
                       | rewrite unsigned_lit by lia; cbn; lia | eassumption
                       | rewrite U48; lia | rewrite U48, unsigned_lit by lia; cbn; lia ]
                    | unfold strchr_post; post_call rsegs mm] end.
  replace (Z_to_bv 64 (strchr_val (bv_unsigned (Z_to_bv 64 66916)) (bv_unsigned (Z_to_bv 64 43) mod 256) MODE_STR))
    with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U48 in H; rename H into ST end.
  match goal with H : mem_inv rsegs _ |- _ => pose proof (mode_bytes_w _ H) as BM end. cbn [MODE_STR app] in BM.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply HSTRCHR with (lo := lo) (str := RWA_STR) (slack := RWA_SLACK);
                       [ rewrite U48; eassumption | rewrite unsigned_lit by lia; apply rwa_bytes; eassumption
                       | cbv; intros [H|[H|[H|H]]]; discriminate H || exact H
                       | rewrite unsigned_lit by lia; cbn; lia | eassumption
                       | rewrite U48; lia | rewrite U48, unsigned_lit by lia; cbn; lia ]
                    | unfold strchr_post; post_call rsegs mm] end.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U48 in H; rename H into ST2 end.
  replace (Z_to_bv 64 (strchr_val (bv_unsigned (Z_to_bv 64 66964)) (bv_unsigned (Z_to_bv 64 119) mod 256) RWA_STR))
    with (Z_to_bv 64 66965) by (vm_compute; reflexivity).
  zstep. if_false. zstep. if_true. zstep. if_false. zstep. zstep.
  apply evt_done. unfold fmemopen_pro_post.
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  do 18 eexists. split; [reflexivity|].
  split; [exact U48|]. split; [reflexivity|]. split; [reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
