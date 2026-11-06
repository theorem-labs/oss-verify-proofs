(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and addresses changed; 2105 of its 2257 lines of code are new or changed and 859 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A5.v, with its module paths and addresses changed; 1044 of its 1143 lines of code are new or changed and 2158 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R1.v blob 85e78d1dcc93 at 6a74d5929d2.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R1.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R1.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (ExecF.evtF) twins of R1.v's six run lemmas (segment-runs-A.tsv row S_R1: r1_z_evt:189,
   r1_ld_evt:239, r1_mode_evt:341, r1_spill_evt:427, r1_shadow_evt:493, r1_call_evt:564). Each <r>_F is <r> with a
   footprint RNG bound FIRST, the same binders and premises in the same order, the footprint premises appended, and
   the conclusion an ExecF.evtF. Every rng premise names a region one of the lemma's OWN premises names:
   - r1_z_evt_F: the shadow byte [d / 8 + K] the check at 0x81420 loads (premise `ov_read_bytes ... (wa (d / 8 + K))
     1`) and the one byte [d] the turn stores (premise `store_ok ... (wa d) 1`);
   - r1_ld_evt_F: the two checked shadow bytes [q / 8 + K] and [(ou + t) / 8 + K], the input byte [q], the our[]
     pointer spill [A + 168, A + 176) and the stored byte [ou + t];
   - r1_mode_evt_F: the checked shadow byte [pm / 8 + K] and the mode byte [pm] (both read only when w <> 0; the
     rng premises are plain, their bounds hold on every arm);
   - r1_spill_evt_F: the six 8-byte spill stores [A + 48], [A + 56], [A + 72], [A + 80], [A + 88], [A + 128];
   - r1_shadow_evt_F: the one shadow byte [Sh + 332] that `sb zero,332(s3)` writes;
   - r1_call_evt_F: the count cell [fr + 2656, fr + 2664) that 0x814ec zeroes, plus what the callee
     reac_box_catalogue needs by its OWN footprint contract (reac_box_catalogue_c.v
     reac_box_catalogue_contract_F, taken in the SAME first-premise position as the plain contract): its frame
     [spv - 16, spv), the runtime cells GOT_CELL_K and CELL_K by name, and the count cell's shadow granule
     [Sh + 332] (shadow_addr (fr + 2656) = Sh + 332 is a premise of the lemma, and fr mod 8 = 0 makes the granule
     one byte).
   R1.v is unchanged. <r>_of_F re-derives R1.<r> from <r>_F at ExecF.RNG_all (every rng premise by ExecF.rng_all);
   <r>_of_F_verbatim pins the corollary to R1.v's text with constr_eq. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R1.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module RBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_catalogue_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LMS (lib.Lib's MState). *)
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* R1.v's three store / branch tactics, restated over evtF goals (their bodies are R1.v's, with `evt _ _` replaced
   by `ExecF.evtF _ _ _`; `step` and `mem_after_store` are now StepF's). r1_post matches only the memory goal, so
   R1.r1_post is reused as it stands. *)
Ltac r1_fix :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (r1_le1_lit z) by lia; mem_after_store
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (r1_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac r1_sb := step; r1_fix.

Ltac r1_br :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first
        [ replace c with true;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?LMS.unsigned_lit by lia; solve_cond]
        | replace c with false;
          [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_leu; rewrite ?LMS.unsigned_lit by lia; solve_cond] ]
  end.

(* Every rng premise of a twin at ExecF.RNG_all: the bounds come from the source lemma's own premises (some of
   them through the shadow divisor, hence the second branch). *)
Ltac r1F_rng_all := apply ExecF.rng_all; first [lia | (Z.div_mod_to_equations; lia)].

(* R1.v's end-of-turn tactic. Its body is R1.v's, with `rewrite EBS` made tolerant: StepF's store bookkeeping
   already leaves the stored byte list in canonical form, so the rewrite can be a no-op here. *)
Ltac r1_post v :=
  lazymatch goal with
  | |- munch _ ?m (write_to_mem ?m _ ?BS) /\ _ =>
      let EBS := fresh "EBS" in
      assert (EBS : BS = [v])
        by (first [apply le1_zxb | (apply r1_le1_lit; lia) | (vm_compute; reflexivity) | reflexivity]);
      rewrite ?EBS;
      split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|];
      split; [apply wmono_write, wmono_refl|];
      apply bytes_at_write_same; cbn [length]; lia
  end.

(* ---------------------------------------------------------------- r1_z_evt *)

Lemma r1_z_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d K l r : Z) (kb : byte),
    a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 l -> a3 = Z_to_bv 64 7 -> a4 = Z_to_bv 64 d ->
    s9 = Z_to_bv 64 0 -> s10 = Z_to_bv 64 K ->
    0 <= d -> d + 1 < 2 ^ 64 -> 1 <= l <= 6 -> 0 <= K -> d / 8 + K + 1 < 2 ^ 64 ->
    0 <= r < 8 -> d mod 8 = r ->
    ov_read_bytes rsegs m (wa (d / 8 + K)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ r < bv_signed kb) ->
    store_ok rsegs m (wa d) 1 = true ->
    ExecF.rng RNG (d / 8 + K) 1 ->
    ExecF.rng RNG d 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (d + 1)) (Z_to_bv 64 (l + 1)) a2 a3
                       (Z_to_bv 64 (d + 1)) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if l =? 6 then 0x81b14 else 0x81414)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d K l r kb -> -> -> -> -> -> Hd0 Hd Hl HK Hsh Hr Hdr HR HOK HS Rsh Rst.
  pose proof (rc_byte_signed kb) as KR.
  lazymatch goal with |- ExecF.evtF _ _ ?QQ _ => set (Q := QQ) end.
  step. r1_br.
  step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit d) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kb)) by lia.
  enough (KC : forall (x5 x6 : word),
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 l) a2 (Z_to_bv 64 7)
               (Z_to_bv 64 d) x5 x6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81428) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kb) 0) as [E|E]; cbn [negb]; [apply KC|].
    step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit d) by lia.
      rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (d mod 8) (bv_signed kb)) by lia.
    replace (d mod 8 <? bv_signed kb) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC. }
  intros x5 x6.
  step. step. step. step. step. step.
  destruct (Z.eq_dec l 6) as [E6|N6].
  - subst l. r1_br. step.
    apply ExecF.evtF_done. unfold Q. do 3 eexists. split; [reflexivity|]. r1_post (Z_to_bv 8 0).
  - r1_br.
    apply ExecF.evtF_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq l 6) N6).
    do 3 eexists. split; [reflexivity|]. r1_post (Z_to_bv 8 0).
Qed.

Lemma r1_z_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d K l r : Z) (kb : byte),
    a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 l -> a3 = Z_to_bv 64 7 -> a4 = Z_to_bv 64 d ->
    s9 = Z_to_bv 64 0 -> s10 = Z_to_bv 64 K ->
    0 <= d -> d + 1 < 2 ^ 64 -> 1 <= l <= 6 -> 0 <= K -> d / 8 + K + 1 < 2 ^ 64 ->
    0 <= r < 8 -> d mod 8 = r ->
    ov_read_bytes rsegs m (wa (d / 8 + K)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ r < bv_signed kb) ->
    store_ok rsegs m (wa d) 1 = true ->
    evt rsegs
      (fun ms' => exists (a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (d + 1)) (Z_to_bv 64 (l + 1)) a2 a3
                       (Z_to_bv 64 (d + 1)) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if l =? 6 then 0x81b14 else 0x81414)) fc None m' (seg_rom rsegs) /\
         munch [(d, d + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' d [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m d K l r kb E0 E1 E3 E4 E9 E10 Hd0 Hd Hl HK Hsh Hr Hdr HR HOK HS.
  eapply ExecF.evtF_evt, (r1_z_evt_F ExecF.RNG_all); try eassumption.
  - r1F_rng_all.
  - r1F_rng_all.
Qed.

Example r1_z_evt_of_F_verbatim : True.
Proof.
  let a := type of R1.r1_z_evt in let b := type of r1_z_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------------------------------------------------------- r1_ld_evt *)

Lemma r1_ld_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ou t K A q v : Z) (b kq kd : byte),
    a0 = Z_to_bv 64 (ou + t) -> a1 = Z_to_bv 64 (t + 1) -> a2 = Z_to_bv 64 6 -> a4 = Z_to_bv 64 (ou + t) ->
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 v -> s10 = Z_to_bv 64 K ->
    0 <= t <= 5 -> 0 <= ou -> ou + 8 < 2 ^ 64 -> ou mod 8 = 0 ->
    0 < q -> q + 1 < 2 ^ 64 -> 1 <= v -> v + 2 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 -> (ou + t) / 8 + K + 1 < 2 ^ 64 ->
    0 <= A -> A + 176 <= 2 ^ 64 -> ou + 8 <= A ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa ((ou + t) / 8 + K)) 1 = Some [kd] ->
    (bv_signed kd = 0 \/ t < bv_signed kd) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 ou)) ->
    store_ok rsegs m (wa (ou + t)) 1 = true ->
    ExecF.rng RNG (q / 8 + K) 1 ->
    ExecF.rng RNG ((ou + t) / 8 + K) 1 ->
    ExecF.rng RNG q 1 ->
    ExecF.rng RNG (A + 168) 8 ->
    ExecF.rng RNG (ou + t) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (x5 x6 x7 : word) (m' : word -> option byte),
         ms' = (if t =? 5
                then MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1)) a2 a3
                             (Z_to_bv 64 ou) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 q) (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (v - 1)) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x814a4) fc None m' (seg_rom rsegs)
                else MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t + 1)) (Z_to_bv 64 (t + 2)) a2 a3
                             (Z_to_bv 64 (ou + t + 1)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (q + 1)) (Z_to_bv 64 (v - 1)) (Z_to_bv 64 (v - 1)) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x81414) fc None m' (seg_rom rsegs)) /\
         munch [(ou + t, ou + t + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (ou + t) [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ou t K A q v b kq kd -> -> -> -> -> -> -> -> Ht Hou0 Hou Hou8 Hq0 Hq Hv0 Hv HK Hshq Hshd
    HA0 HA HAo HRq HOKq HRd HOKd HRb HSP HS Rshq Rshd Rq Rsp Rst.
  pose proof (rc_byte_signed kq) as KRq. pose proof (rc_byte_signed kd) as KRd.
  assert (Hdm : (ou + t) mod 8 = t) by (Z.div_mod_to_equations; lia).
  lazymatch goal with |- ExecF.evtF _ _ ?QQ _ => set (Q := QQ) end.
  step. r1_br.
  step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit q) by lia. rewrite rc_shr3.
  step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kq)) by lia.
  enough (KC1 : forall (x5 x6 : word),
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1))
               (Z_to_bv 64 6) a3 (Z_to_bv 64 (ou + t)) x5 x6 a7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
               (Z_to_bv 64 v) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81460) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kq) 0) as [E|E]; cbn [negb]; [apply KC1|].
    step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit q) by lia.
      rewrite rc_land7.
    step.
    rewrite (rc_lts_signed (q mod 8) (bv_signed kq)) by lia.
    replace (q mod 8 <? bv_signed kq) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC1. }
  intros x5 x6.
  step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (ou + t)) by lia.
    rewrite rc_shr3.
  step. step. step. step.
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed kd)) by lia.
  enough (KC2 : forall (y6 y7 : word),
    ExecF.evtF rsegs RNG Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1))
               (Z_to_bv 64 6) a3 (Z_to_bv 64 (ou + t)) (zxb b) y6 y7 s2 s3 s4 s5 (Z_to_bv 64 q) s7 s8
               (Z_to_bv 64 v) (Z_to_bv 64 K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81474) fc None m (seg_rom rsegs))).
  { destruct (Z.eqb_spec (bv_signed kd) 0) as [E|E]; cbn [negb]; [apply KC2|].
    step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (ou + t)) by lia.
      rewrite rc_land7. rewrite Hdm.
    step.
    rewrite (rc_lts_signed t (bv_signed kd)) by lia.
    replace (t <? bv_signed kd) with true by (symmetry; apply Z.ltb_lt; lia).
    apply KC2. }
  intros y6 y7.
  step. step. step.
  rewrite le1_zxb.
  assert (HL : ov_read_bytes rsegs (write_to_mem m (Z_to_bv 64 (ou + t)) [b]) (wa (A + 168)) 8
               = Some (le8 (Z_to_bv 64 ou))).
  { assert (HB' : bytes_at rsegs (write_to_mem m (Z_to_bv 64 (ou + t)) [b]) (A + 168) (le8 (Z_to_bv 64 ou)))
      by (apply bytes_at_write_other;
          [exact HSP | lia | cbn [length]; lia | rewrite length_le8; cbn [length]; lia]).
    pose proof (bytes_at_ov_read rsegs _ _ _ 0 8 HB' ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r in HH. rewrite HH. f_equal. }
  step. step.
  destruct (Z.eq_dec t 5) as [E5|N5].
  - subst t. r1_br.
    apply ExecF.evtF_done. unfold Q. cbv beta.
    do 4 eexists. split; [cbn [Z.eqb]; reflexivity|].
    split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    apply bytes_at_write_same; cbn [length]; lia.
  - r1_br.
    step. step. step. step. step. step.
    apply ExecF.evtF_done. unfold Q. cbv beta.
    rewrite (proj2 (Z.eqb_neq t 5) N5).
    replace (Z_to_bv 64 (ou + (t + 1))) with (Z_to_bv 64 (ou + t + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (t + 1 + 1)) with (Z_to_bv 64 (t + 2)) by (f_equal; lia).
    replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
    do 4 eexists. split; [reflexivity|].
    split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside length]; left; lia]|].
    split; [apply wmono_write, wmono_refl|].
    apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma r1_ld_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ou t K A q v : Z) (b kq kd : byte),
    a0 = Z_to_bv 64 (ou + t) -> a1 = Z_to_bv 64 (t + 1) -> a2 = Z_to_bv 64 6 -> a4 = Z_to_bv 64 (ou + t) ->
    s1 = Z_to_bv 64 A -> s6 = Z_to_bv 64 q -> s9 = Z_to_bv 64 v -> s10 = Z_to_bv 64 K ->
    0 <= t <= 5 -> 0 <= ou -> ou + 8 < 2 ^ 64 -> ou mod 8 = 0 ->
    0 < q -> q + 1 < 2 ^ 64 -> 1 <= v -> v + 2 < 2 ^ 64 ->
    0 <= K -> q / 8 + K + 1 < 2 ^ 64 -> (ou + t) / 8 + K + 1 < 2 ^ 64 ->
    0 <= A -> A + 176 <= 2 ^ 64 -> ou + 8 <= A ->
    ov_read_bytes rsegs m (wa (q / 8 + K)) 1 = Some [kq] ->
    (bv_signed kq = 0 \/ q mod 8 < bv_signed kq) ->
    ov_read_bytes rsegs m (wa ((ou + t) / 8 + K)) 1 = Some [kd] ->
    (bv_signed kd = 0 \/ t < bv_signed kd) ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b] ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 ou)) ->
    store_ok rsegs m (wa (ou + t)) 1 = true ->
    evt rsegs
      (fun ms' => exists (x5 x6 x7 : word) (m' : word -> option byte),
         ms' = (if t =? 5
                then MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t)) (Z_to_bv 64 (t + 1)) a2 a3
                             (Z_to_bv 64 ou) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 q) (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (v - 1)) (Z_to_bv 64 v) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x814a4) fc None m' (seg_rom rsegs)
                else MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ou + t + 1)) (Z_to_bv 64 (t + 2)) a2 a3
                             (Z_to_bv 64 (ou + t + 1)) x5 x6 x7 s2 s3 s4 s5 (Z_to_bv 64 (q + 1))
                             (Z_to_bv 64 (q + 1)) (Z_to_bv 64 (v - 1)) (Z_to_bv 64 (v - 1)) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x81414) fc None m' (seg_rom rsegs)) /\
         munch [(ou + t, ou + t + 1)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (ou + t) [b])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81414) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ou t K A q v b kq kd E0 E1 E2 E4 E_1 E6 E9 E10 Ht Hou0 Hou Hou8 Hq0 Hq Hv0 Hv HK Hshq Hshd
    HA0 HA HAo HRq HOKq HRd HOKd HRb HSP HS.
  eapply ExecF.evtF_evt, (r1_ld_evt_F ExecF.RNG_all); try eassumption.
  - r1F_rng_all.
  - r1F_rng_all.
  - r1F_rng_all.
  - r1F_rng_all.
  - r1F_rng_all.
Qed.

Example r1_ld_evt_of_F_verbatim : True.
Proof.
  let a := type of R1.r1_ld_evt in let b := type of r1_ld_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------------------------------------------------------- r1_mode_evt *)

Lemma r1_mode_evt_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pm w K : Z) (bm km : byte),
    s6 = Z_to_bv 64 (pm - 1) -> s7 = Z_to_bv 64 pm -> s8 = Z_to_bv 64 w -> s9 = Z_to_bv 64 (w + 1) ->
    s10 = Z_to_bv 64 K ->
    0 < pm -> pm + 2 < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> pm / 8 + K + 1 < 2 ^ 64 ->
    (w <> 0 -> ov_read_bytes rsegs m (wa (pm / 8 + K)) 1 = Some [km]) ->
    (w <> 0 -> bv_signed km = 0 \/ pm mod 8 < bv_signed km) ->
    (w <> 0 -> ov_read_bytes rsegs m (wa pm) 1 = Some [bm]) ->
    ExecF.rng RNG (pm / 8 + K) 1 ->
    ExecF.rng RNG pm 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 22 = Z_to_bv 64 (if w =? 0 then pm else pm + 1) /\
            getr R 25 = Z_to_bv 64 (if w =? 0 then 0 else w - 1)) \/
         (bv_unsigned bm mod 2 = 1 /\ 1 <= w /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                          (Z_to_bv 64 (pm + 1)) (zxb bm) (Z_to_bv 64 w) (Z_to_bv 64 (w - 1)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pm w K bm km -> -> -> -> -> Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm Rshm Rpm.
  pose proof (rc_byte_signed km) as KRk.
  pose proof (bv_unsigned_in_range 8 bm) as HBM. unfold bv_modulus in HBM. cbn in HBM.
  lazymatch goal with |- ExecF.evtF _ _ ?QQ _ => set (Q := QQ) end.
  step.
  destruct (Z.eq_dec w 0) as [E0|N0].
  - subst w. r1_br.
    step. step. step.
    apply ExecF.evtF_done. unfold Q. cbv beta. left. eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; reflexivity.
  - r1_br.
    specialize (HRk N0). specialize (HOKk N0). specialize (HRm N0).
    step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit pm) by lia.
      rewrite rc_shr3.
    step. step. step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed km)) by lia.
    enough (KC : forall (x0 x1 : word),
      ExecF.evtF rsegs RNG Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                 (Z_to_bv 64 (pm - 1)) (Z_to_bv 64 pm) (Z_to_bv 64 w) (Z_to_bv 64 (w + 1))
                 (Z_to_bv 64 K) s11
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x814bc) fc None m (seg_rom rsegs))).
    { destruct (Z.eqb_spec (bv_signed km) 0) as [E|E]; cbn [negb]; [apply KC|].
      step. step. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit pm) by lia.
        rewrite rc_land7.
      step.
      rewrite (rc_lts_signed (pm mod 8) (bv_signed km)) by lia.
      replace (pm mod 8 <? bv_signed km) with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. step. apply KC. }
    intros x0 x1.
    step. step. step.
    unfold zxb. rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit (bv_unsigned bm))
      by lia. rewrite r1_land1 by lia.
    step. step.
    destruct (Z.eq_dec (bv_unsigned bm mod 2) 0) as [Ev|Od].
    + rewrite Ev. r1_br.
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      apply ExecF.evtF_done. unfold Q. cbv beta. left. eexists.
      rewrite (proj2 (Z.eqb_neq w 0) N0).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    + r1_br.
      apply ExecF.evtF_done. unfold Q. cbv beta. right.
      split; [lia|]. split; [lia|].
      replace (Z_to_bv 64 (pm - 1 + 2)) with (Z_to_bv 64 (pm + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (w + 1 + -2)) with (Z_to_bv 64 (w - 1)) by (f_equal; lia).
      do 2 eexists. reflexivity.
Qed.

Lemma r1_mode_evt_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pm w K : Z) (bm km : byte),
    s6 = Z_to_bv 64 (pm - 1) -> s7 = Z_to_bv 64 pm -> s8 = Z_to_bv 64 w -> s9 = Z_to_bv 64 (w + 1) ->
    s10 = Z_to_bv 64 K ->
    0 < pm -> pm + 2 < 2 ^ 64 -> 0 <= w -> w + 2 < 2 ^ 64 -> 0 <= K -> pm / 8 + K + 1 < 2 ^ 64 ->
    (w <> 0 -> ov_read_bytes rsegs m (wa (pm / 8 + K)) 1 = Some [km]) ->
    (w <> 0 -> bv_signed km = 0 \/ pm mod 8 < bv_signed km) ->
    (w <> 0 -> ov_read_bytes rsegs m (wa pm) 1 = Some [bm]) ->
    evt rsegs
      (fun ms' =>
         (exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81b14) fc None m (seg_rom rsegs) /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
            getr R 22 = Z_to_bv 64 (if w =? 0 then pm else pm + 1) /\
            getr R 25 = Z_to_bv 64 (if w =? 0 then 0 else w - 1)) \/
         (bv_unsigned bm mod 2 = 1 /\ 1 <= w /\
          exists x0 x1 : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x0 x1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
                          (Z_to_bv 64 (pm + 1)) (zxb bm) (Z_to_bv 64 w) (Z_to_bv 64 (w - 1)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814a4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m pm w K bm km E6 E7 E8 E9 E10 Hpm0 Hpm Hw0 Hw HK Hshm HRk HOKk HRm.
  eapply ExecF.evtF_evt, (r1_mode_evt_F ExecF.RNG_all); try eassumption.
  - r1F_rng_all.
  - r1F_rng_all.
Qed.

Example r1_mode_evt_of_F_verbatim : True.
Proof.
  let a := type of R1.r1_mode_evt in let b := type of r1_mode_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------------------------------------------------------- r1_spill_evt *)

(* route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z, R amended 10:33Z): r1_spill_evt_F with its shadow_rw premise
   DROPPED and its post shadow_rw m' in the region form. R is empty: the run's six sd stores go to the spill cells
   [A + 48, A + 136), app memory that the rw_cells premises pay, and the run loads no shadow byte. The old proof used
   shadow_rw m only to carry it to m'; that carry is now R1.v's local transport twin r1_shadow_rw_on (a Theorem Labs lane,
   c5bc182745d). r1_spill_evt_F below is a corollary. *)
Lemma r1_spill_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (x48 x56 x72 x80 x88 x128 sh1 cs : list byte),
    s1 = Z_to_bv 64 A -> ra0 = Z_to_bv 64 (fr + 2496) -> t2 = Z_to_bv 64 (fr + 544) ->
    t3 = Z_to_bv 64 (fr + 2256) -> t4 = Z_to_bv 64 (fr + 2368) -> t5 = Z_to_bv 64 (fr + 2448) ->
    t6 = Z_to_bv 64 (fr + 2464) ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (A + 48) [CB 8 x48] -> rw_cells rsegs m (A + 56) [CB 8 x56] ->
    rw_cells rsegs m (A + 72) [CB 8 x72] -> rw_cells rsegs m (A + 80) [CB 8 x80] ->
    rw_cells rsegs m (A + 88) [CB 8 x88] -> rw_cells rsegs m (A + 128) [CB 8 x128] ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m ->
    ExecF.rng RNG (A + 48) 8 -> ExecF.rng RNG (A + 56) 8 -> ExecF.rng RNG (A + 72) 8 ->
    ExecF.rng RNG (A + 80) 8 -> ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 128) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814e8) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (Sh + 332) [CB 1 sh1] /\ rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))) /\
         bytes_at rsegs m' (A + 56) (le8 (Z_to_bv 64 (fr + 2368))) /\
         bytes_at rsegs m' (A + 72) (le8 (Z_to_bv 64 (fr + 2496))) /\
         bytes_at rsegs m' (A + 80) (le8 (Z_to_bv 64 (fr + 2464))) /\
         bytes_at rsegs m' (A + 88) (le8 (Z_to_bv 64 (fr + 2448))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv x48 x56 x72 x80 x88 x128 sh1 cs -> -> -> -> -> -> ->
    Hfr0 HfrA HspA HA64 HShlo HShA HAapp CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA ST HAC
    R48 R56 R72 R80 R88 R128.
  pose proof (munch_refl [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (Hsho : forall a, in_shadow a -> ~ (A + 48 <= a < A + 136)).
  { intros a Ha Hin. exact (app_not_shadow a (HAapp a ltac:(lia)) Ha). }
  apply ExecF.evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split.
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  split.
  { intros P HP. refine (r1_shadow_rw_on _ m m1 MU WM _ P HP). intros a Ha. left. pose proof (Hsho a Ha).
    cbn [outside]. repeat split; first [exact I | lia]. }
  split; [exact STA|]. split; [exact ST|].
  split; [exact CHsh|]. split; [exact CHc|].
  split.
  { destruct CH48 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH128 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH56 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH72 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { destruct CH80 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  { destruct CH88 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
Qed.

Lemma r1_spill_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (x48 x56 x72 x80 x88 x128 sh1 cs : list byte),
    s1 = Z_to_bv 64 A -> ra0 = Z_to_bv 64 (fr + 2496) -> t2 = Z_to_bv 64 (fr + 544) ->
    t3 = Z_to_bv 64 (fr + 2256) -> t4 = Z_to_bv 64 (fr + 2368) -> t5 = Z_to_bv 64 (fr + 2448) ->
    t6 = Z_to_bv 64 (fr + 2464) ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (A + 48) [CB 8 x48] -> rw_cells rsegs m (A + 56) [CB 8 x56] ->
    rw_cells rsegs m (A + 72) [CB 8 x72] -> rw_cells rsegs m (A + 80) [CB 8 x80] ->
    rw_cells rsegs m (A + 88) [CB 8 x88] -> rw_cells rsegs m (A + 128) [CB 8 x128] ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    ExecF.rng RNG (A + 48) 8 -> ExecF.rng RNG (A + 56) 8 -> ExecF.rng RNG (A + 72) 8 ->
    ExecF.rng RNG (A + 80) 8 -> ExecF.rng RNG (A + 88) 8 -> ExecF.rng RNG (A + 128) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814e8) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (Sh + 332) [CB 1 sh1] /\ rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))) /\
         bytes_at rsegs m' (A + 56) (le8 (Z_to_bv 64 (fr + 2368))) /\
         bytes_at rsegs m' (A + 72) (le8 (Z_to_bv 64 (fr + 2496))) /\
         bytes_at rsegs m' (A + 80) (le8 (Z_to_bv 64 (fr + 2464))) /\
         bytes_at rsegs m' (A + 88) (le8 (Z_to_bv 64 (fr + 2448))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv x48 x56 x72 x80 x88 x128 sh1 cs E1 Era Et2 Et3 Et4 Et5 Et6
    Hfr0 HfrA HspA HA64 HShlo HShA HAapp CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA ST HAC HSW
    R48 R56 R72 R80 R88 R128.
  eapply ExecF.evtF_mono;
    [exact (r1_spill_evt_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m A fr Sh spv x48 x56 x72 x80 x88 x128 sh1 cs E1 Era Et2 Et3 Et4 Et5 Et6
              Hfr0 HfrA HspA HA64 HShlo HShA HAapp CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA ST HAC
              R48 R56 R72 R80 R88 R128)|].
  intros ms' (m' & E & MU & WM & HAC' & HSW' & H). exists m'.
  do 4 (split; [assumption|]). split; [|exact H].
  exact (A.ShadowRwOn.shadow_rw_of_on_all m' (HSW' _ (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

Lemma r1_spill_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (x48 x56 x72 x80 x88 x128 sh1 cs : list byte),
    s1 = Z_to_bv 64 A -> ra0 = Z_to_bv 64 (fr + 2496) -> t2 = Z_to_bv 64 (fr + 544) ->
    t3 = Z_to_bv 64 (fr + 2256) -> t4 = Z_to_bv 64 (fr + 2368) -> t5 = Z_to_bv 64 (fr + 2448) ->
    t6 = Z_to_bv 64 (fr + 2464) ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (A + 48) [CB 8 x48] -> rw_cells rsegs m (A + 56) [CB 8 x56] ->
    rw_cells rsegs m (A + 72) [CB 8 x72] -> rw_cells rsegs m (A + 80) [CB 8 x80] ->
    rw_cells rsegs m (A + 88) [CB 8 x88] -> rw_cells rsegs m (A + 128) [CB 8 x128] ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814e8) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 64); (A + 72, A + 96); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (Sh + 332) [CB 1 sh1] /\ rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))) /\
         bytes_at rsegs m' (A + 56) (le8 (Z_to_bv 64 (fr + 2368))) /\
         bytes_at rsegs m' (A + 72) (le8 (Z_to_bv 64 (fr + 2496))) /\
         bytes_at rsegs m' (A + 80) (le8 (Z_to_bv 64 (fr + 2464))) /\
         bytes_at rsegs m' (A + 88) (le8 (Z_to_bv 64 (fr + 2448))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv x48 x56 x72 x80 x88 x128 sh1 cs E1 Era Et2 Et3 Et4 Et5 Et6
    Hfr0 HfrA HspA HA64 HShlo HShA HAapp CH48 CH56 CH72 CH80 CH88 CH128 CHsh CHc STA ST HAC HSW.
  eapply ExecF.evtF_evt, (r1_spill_evt_F ExecF.RNG_all); try eassumption;
    r1F_rng_all.
Qed.

Example r1_spill_evt_of_F_verbatim : True.
Proof.
  let a := type of R1.r1_spill_evt in let b := type of r1_spill_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------------------------------------------------------- r1_shadow_evt *)

(* route (C): r1_shadow_evt_F with its shadow_rw premise DROPPED and its post shadow_rw m' in the region form. R is
   empty: the run's one store, `sb zero,332(s3)` into the shadow byte [Sh + 332], is paid by the premise
   rw_cells rsegs m (Sh + 332) [CB 1 sh1], not by shadow_rw (ASSIGN 11:45Z: drop where a rw_cells / wr_at premise
   pays each store), and the run loads no shadow byte. In the post, the byte at Sh + 332 is present in m' because the
   run stored it (r1_ba_rd); every other shadow byte is outside the munch region. The carry is R1.v's local transport
   twin r1_shadow_rw_on (a Theorem Labs lane, c5bc182745d). r1_shadow_evt_F below is a corollary. *)
Lemma r1_shadow_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (sh1 cs : list byte),
    s3 = Z_to_bv 64 Sh ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    Sh + 392 <= spv - 16 -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    ExecF.rng RNG (Sh + 332) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814ec) fc None m' (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814e8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv sh1 cs -> Hfr0 HfrA HspA HA64 HShlo HShA HShsp HShD HAapp Hwapp
    CHsh CHc STA ST HAC H48b H128b Rsh.
  pose proof (munch_refl [(Sh + 332, Sh + 333)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HShD as [HShD|HShD].
  { r1_sb.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (HSHb : bytes_at rsegs m1 (Sh + 332) [Z_to_bv 8 0]).
    { destruct CHsh as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    apply ExecF.evtF_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split.
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    split.
    { intros P HP. refine (r1_shadow_rw_on _ m m1 MU WM _ P HP). intros a Ha.
      destruct (Z_le_gt_dec (Sh + 332) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 333)) as [H2|H2]|].
      - right. apply (r1_ba_rd m1 (Sh + 332) [Z_to_bv 8 0] a HSHb). cbn [length]. lia.
      - left. cbn [outside]. split; [lia | exact I].
      - left. cbn [outside]. split; [lia | exact I]. }
    split; [exact STA|]. split; [exact ST|]. split; [exact CHc|]. split; [exact HSHb|].
    split; [exact H48b | exact H128b]. }
  { r1_sb.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (HSHb : bytes_at rsegs m1 (Sh + 332) [Z_to_bv 8 0]).
    { destruct CHsh as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    apply ExecF.evtF_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split.
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    split.
    { intros P HP. refine (r1_shadow_rw_on _ m m1 MU WM _ P HP). intros a Ha.
      destruct (Z_le_gt_dec (Sh + 332) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 333)) as [H2|H2]|].
      - right. apply (r1_ba_rd m1 (Sh + 332) [Z_to_bv 8 0] a HSHb). cbn [length]. lia.
      - left. cbn [outside]. split; [lia | exact I].
      - left. cbn [outside]. split; [lia | exact I]. }
    split; [exact STA|]. split; [exact ST|]. split; [exact CHc|]. split; [exact HSHb|].
    split; [exact H48b | exact H128b]. }
Qed.

Lemma r1_shadow_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (sh1 cs : list byte),
    s3 = Z_to_bv 64 Sh ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    Sh + 392 <= spv - 16 -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    ExecF.rng RNG (Sh + 332) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814ec) fc None m' (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814e8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv sh1 cs E3 Hfr0 HfrA HspA HA64 HShlo HShA HShsp HShD HAapp Hwapp
    CHsh CHc STA ST HAC HSW H48b H128b Rsh.
  eapply ExecF.evtF_mono;
    [exact (r1_shadow_evt_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m A fr Sh spv sh1 cs E3 Hfr0 HfrA HspA HA64 HShlo HShA HShsp HShD HAapp Hwapp
              CHsh CHc STA ST HAC H48b H128b Rsh)|].
  intros ms' (m' & E & MU & WM & HAC' & HSW' & H). exists m'.
  do 4 (split; [assumption|]). split; [|exact H].
  exact (A.ShadowRwOn.shadow_rw_of_on_all m' (HSW' _ (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

Lemma r1_shadow_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr Sh spv : Z) (sh1 cs : list byte),
    s3 = Z_to_bv 64 Sh ->
    0 <= fr -> fr + 3136 <= A -> spv <= A -> A + 416 <= 2 ^ 64 -> 2147450880 <= Sh -> Sh + 392 <= A ->
    Sh + 392 <= spv - 16 -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    rw_cells rsegs m (Sh + 332) [CB 1 sh1] -> rw_cells rsegs m (fr + 2656) [CB 8 cs] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x814ec) fc None m' (seg_rom rsegs) /\
         munch [(Sh + 332, Sh + 333)] m m' /\ wmono rsegs m m' /\
         asan_cells m' /\ shadow_rw m' /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         rw_cells rsegs m' (fr + 2656) [CB 8 cs] /\ bytes_at rsegs m' (Sh + 332) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv sh1 cs E3 Hfr0 HfrA HspA HA64 HShlo HShA HShsp HShD HAapp Hwapp
    CHsh CHc STA ST HAC HSW H48b H128b.
  eapply ExecF.evtF_evt, (r1_shadow_evt_F ExecF.RNG_all); try eassumption.
  r1F_rng_all.
Qed.

Example r1_shadow_evt_of_F_verbatim : True.
Proof.
  let a := type of R1.r1_shadow_evt in let b := type of r1_shadow_evt_of_F in constr_eq a b.
  exact I.
Qed.

(* ---------------------------------------------------------------- r1_call_evt *)

(* route (C): r1_call_evt_F with the callee's _on contract RBC.reac_box_catalogue_contract_F_on (a Theorem Labs lane,
   a working branch d68c95046c8, reac_box_catalogue_c.v blob d3c4f4d7f9d: the callee's shadow_rw premise
   is DROPPED) and its own shadow_rw premise DROPPED. R is empty: the run stores the count cell [fr + 2656, fr + 2664)
   (app memory, paid by rw_cells) and the callee its frame [spv - 16, spv); the callee's one check reads the shadow
   byte shadow_addr (fr + 2656) = Sh + 332 through addressable m1 (fr + 2656) 8, which the run builds from the
   premise bytes_at rsegs m (Sh + 332) [Z_to_bv 8 0], not from shadow_rw. The carries are R1.v's local transport
   twin r1_shadow_rw_on (a Theorem Labs lane, c5bc182745d). r1_call_evt_F below takes the plain callee contract, so it keeps
   its own proof, byte-identical (a Theorem Labs lane 09:58Z). *)
Lemma r1_call_evt_F_on : RBC.reac_box_catalogue_contract_F_on ->
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr Sh spv : Z) (cs : list byte),
    sp = Z_to_bv 64 spv -> s2 = Z_to_bv 64 (fr + 2656) ->
    6283264 <= fr -> fr + 3136 <= 140737488355328 -> fr mod 8 = 0 -> fr + 3136 <= A -> spv <= A ->
    A + 416 <= 2 ^ 64 -> 6283264 <= spv - 16 -> spv <= 140737488355328 ->
    (fr + 2664 <= spv - 16 \/ spv <= fr) -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    shadow_addr (fr + 2656) = Sh + 332 ->
    (forall a, fr <= a < fr + 3136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (fr + 2656) [CB 8 cs] -> bytes_at rsegs m (Sh + 332) [Z_to_bv 8 0] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    ExecF.rng RNG (fr + 2656) 8 ->
    ExecF.rng RNG (spv - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (Sh + 332) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x814f8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 0x9e800 /\
         munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' (fr + 2656) (le8 (Z_to_bv 64 11)) /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814ec) fc None m (seg_rom rsegs)).
Proof.
  intros CATC RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv cs -> -> HfrGT HfrE Hfr8 HfrA HspA HA64 HspGT HspE Hsep HShD Hshc Happ Hwapp HAapp
    CHc HSHb STA ST HAC H48b H128b Rc Rwin Rgot Rcell Rsh.
  unfold RBC.reac_box_catalogue_contract_F_on, RBC.reac_box_catalogue_post, RBC.REAC_BOX_CATALOGUE,
    RBC.REAC_BOX_CATALOGUE_FRAME, RBC.BOX_CATALOGUE in CATC.
  assert (Hsh7 : shadow_addr (fr + 2656 + 7) = Sh + 332).
  { rewrite <- Hshc. unfold shadow_addr.
    assert (E : (fr + 2656 + 7) / 8 = (fr + 2656) / 8) by (Z.div_mod_to_equations; lia). lia. }
  pose proof (munch_refl [(fr + 2656, fr + 2664); (spv - 16, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HShD as [HShD|HShD].
  {
    step. step. step.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m1).
    { intros P HP. refine (r1_shadow_rw_on _ m m1 MU WM _ P HP). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply ExecF.evtF_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16) (RNG := RNG).
      - reflexivity.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc].
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact Rwin.
      - exact Rgot.
      - exact Rcell.
      - intros _. rewrite Hshc, Hsh7.
        replace (Sh + 332 - (Sh + 332) + 1) with 1 by lia.
        split; [exact Rc | exact Rsh]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; tauto | exact MU2]. }
    assert (HSW2 : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m').
    { intros P HP. refine (r1_shadow_rw_on _ m1 m' MU2 WM2 _ P (HSW1 P HP)). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
  {
    step. step. step.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m1).
    { intros P HP. refine (r1_shadow_rw_on _ m m1 MU WM _ P HP). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply ExecF.evtF_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16) (RNG := RNG).
      - reflexivity.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc].
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact Rwin.
      - exact Rgot.
      - exact Rcell.
      - intros _. rewrite Hshc, Hsh7.
        replace (Sh + 332 - (Sh + 332) + 1) with 1 by lia.
        split; [exact Rc | exact Rsh]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; tauto | exact MU2]. }
    assert (HSW2 : forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m').
    { intros P HP. refine (r1_shadow_rw_on _ m1 m' MU2 WM2 _ P (HSW1 P HP)). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
Qed.

Lemma r1_call_evt_F : RBC.reac_box_catalogue_contract_F ->
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr Sh spv : Z) (cs : list byte),
    sp = Z_to_bv 64 spv -> s2 = Z_to_bv 64 (fr + 2656) ->
    6283264 <= fr -> fr + 3136 <= 140737488355328 -> fr mod 8 = 0 -> fr + 3136 <= A -> spv <= A ->
    A + 416 <= 2 ^ 64 -> 6283264 <= spv - 16 -> spv <= 140737488355328 ->
    (fr + 2664 <= spv - 16 \/ spv <= fr) -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    shadow_addr (fr + 2656) = Sh + 332 ->
    (forall a, fr <= a < fr + 3136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (fr + 2656) [CB 8 cs] -> bytes_at rsegs m (Sh + 332) [Z_to_bv 8 0] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    ExecF.rng RNG (fr + 2656) 8 ->
    ExecF.rng RNG (spv - 16) 16 ->
    ExecF.rng RNG GOT_CELL_K 8 ->
    ExecF.rng RNG CELL_K 8 ->
    ExecF.rng RNG (Sh + 332) 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x814f8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 0x9e800 /\
         munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' (fr + 2656) (le8 (Z_to_bv 64 11)) /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814ec) fc None m (seg_rom rsegs)).
Proof.
  intros CATC RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv cs -> -> HfrGT HfrE Hfr8 HfrA HspA HA64 HspGT HspE Hsep HShD Hshc Happ Hwapp HAapp
    CHc HSHb STA ST HAC HSW H48b H128b Rc Rwin Rgot Rcell Rsh.
  unfold RBC.reac_box_catalogue_contract_F, RBC.reac_box_catalogue_post, RBC.REAC_BOX_CATALOGUE,
    RBC.REAC_BOX_CATALOGUE_FRAME, RBC.BOX_CATALOGUE in CATC.
  assert (Hsh7 : shadow_addr (fr + 2656 + 7) = Sh + 332).
  { rewrite <- Hshc. unfold shadow_addr.
    assert (E : (fr + 2656 + 7) / 8 = (fr + 2656) / 8) by (Z.div_mod_to_equations; lia). lia. }
  pose proof (munch_refl [(fr + 2656, fr + 2664); (spv - 16, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HShD as [HShD|HShD].
  {
    step. step. step.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply ExecF.evtF_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16) (RNG := RNG).
      - reflexivity.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - exact HSW1.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc].
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact Rwin.
      - exact Rgot.
      - exact Rcell.
      - intros _. rewrite Hshc, Hsh7.
        replace (Sh + 332 - (Sh + 332) + 1) with 1 by lia.
        split; [exact Rc | exact Rsh]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; tauto | exact MU2]. }
    assert (HSW2 : shadow_rw m').
    { apply (r1_shadow_rw _ m1 m' HSW1 MU2 WM2). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
  {
    step. step. step.
    match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    assert (Hsho : forall a, in_shadow a -> ~ (fr + 2656 <= a < fr + 2664) /\ ~ (spv - 16 <= a < spv)).
    { intros a Ha. split; intros Hin.
      - exact (app_not_shadow a (Happ a ltac:(lia)) Ha).
      - exact (app_not_shadow a (Hwapp a ltac:(lia)) Ha). }
    assert (HAC1 : asan_cells m1).
    { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
      repeat split; first [exact I | lia]. }
    assert (HSW1 : shadow_rw m1).
    { apply (r1_shadow_rw _ m m1 HSW MU WM). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (HADc : addressable m1 (fr + 2656) 8).
    { apply (r1_addr_z m1 (fr + 2656) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia
        | unfold APPMEM_END; lia | intros i Hi; apply Happ; lia |].
      rewrite Hshc. cbn [repeat]. exact HSHb. }
    assert (HWRc : wr_at rsegs m1 (fr + 2656) 8).
    { destruct CHc as (_ & Hw). cbn [cells_size csize Nat.add] in Hw. exact Hw. }
    eapply ExecF.evtF_cut.
    { eapply CATC with (c := fr + 2656) (lo := spv - 16) (RNG := RNG).
      - reflexivity.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact ST.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. lia.
      - exact HAC1.
      - exact HSW1.
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        intros x [Hx | [Hx | Hx]].
        + cbn [outside]. unfold GOT_CELL_K in Hx. repeat split; (exact I || lia).
        + cbn [outside]. unfold CELL_K in Hx. repeat split; (exact I || lia).
        + destruct (Hsho x Hx) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia).
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia.
        right. split; [Z.div_mod_to_equations; lia|]. split; [exact HWRc|].
        split; [lia | exact HADc].
      - rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) by lia. exact Rwin.
      - exact Rgot.
      - exact Rcell.
      - intros _. rewrite Hshc, Hsh7.
        replace (Sh + 332 - (Sh + 332) + 1) with 1 by lia.
        split; [exact Rc | exact Rsh]. }
    intros ms' PO.
    destruct PO as (a1' & a2' & m' & E & MU2 & WM2 & MI2 & ST2 & HZ).
    subst ms'.
    rewrite (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit spv) in MU2, ST2 by lia.
    replace (fr + 2656 + 8) with (fr + 2664) in MU2 by lia.
    rewrite (proj2 (Z.eqb_neq (fr + 2656) 0) ltac:(lia)) in HZ.
    replace (ret_pc (Z_to_bv 64 0x814f8)) with (Z_to_bv 64 0x814f8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (MUf : munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m').
    { apply (munch_trans _ m m1 m'); [exact MU|].
      apply (munch_weaken [(spv - 16, spv); (fr + 2656, fr + 2664)]);
        [intros x Hx; cbn [outside] in Hx |- *; tauto | exact MU2]. }
    assert (HSW2 : shadow_rw m').
    { apply (r1_shadow_rw _ m1 m' HSW1 MU2 WM2). intros a Ha. left.
      destruct (Hsho a Ha) as (D1 & D2). cbn [outside]. repeat split; (exact I || lia). }
    assert (STA2 : stk rsegs m' (A + 48) (A + 136)).
    { apply (r1_stk_tr _ m1 m' _ _ STA MU2 WM2). intros x Hx. left.
      cbn [outside]. repeat split; (exact I || lia). }
    apply ExecF.evtF_done. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
    split; [exact HSW2|]. split; [exact STA2|]. split; [exact ST2|].
    split; [exact HZ|].
    split.
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H48b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
    { apply (bytes_at_transport rsegs [(spv - 16, spv); (fr + 2656, fr + 2664)] m1 m' _ _ H128b MU2).
      cbn [disjoint_from]; rewrite ?length_le8; cbn [length]; repeat split; (exact I || lia). }
  }
Qed.

(* R1.r1_call_evt's statement, with the callee's FOOTPRINT contract in the place of the plain one (the first
   premise); every rng premise of the twin is discharged by ExecF.rng_all. *)
Lemma r1_call_evt_of_F : RBC.reac_box_catalogue_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr Sh spv : Z) (cs : list byte),
    sp = Z_to_bv 64 spv -> s2 = Z_to_bv 64 (fr + 2656) ->
    6283264 <= fr -> fr + 3136 <= 140737488355328 -> fr mod 8 = 0 -> fr + 3136 <= A -> spv <= A ->
    A + 416 <= 2 ^ 64 -> 6283264 <= spv - 16 -> spv <= 140737488355328 ->
    (fr + 2664 <= spv - 16 \/ spv <= fr) -> (Sh + 392 <= fr \/ fr + 3136 <= Sh) ->
    shadow_addr (fr + 2656) = Sh + 332 ->
    (forall a, fr <= a < fr + 3136 -> app_mem a) ->
    (forall a, spv - 16 <= a < spv -> app_mem a) ->
    (forall a, A + 48 <= a < A + 136 -> app_mem a) ->
    rw_cells rsegs m (fr + 2656) [CB 8 cs] -> bytes_at rsegs m (Sh + 332) [Z_to_bv 8 0] ->
    stk rsegs m (A + 48) (A + 136) -> stk rsegs m (spv - 16) spv -> asan_cells m -> shadow_rw m ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 (fr + 544))) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x814f8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 0x9e800 /\
         munch [(fr + 2656, fr + 2664); (spv - 16, spv)] m m' /\ wmono rsegs m m' /\
         shadow_rw m' /\ stk rsegs m' (A + 48) (A + 136) /\ stk rsegs m' (spv - 16) spv /\
         bytes_at rsegs m' (fr + 2656) (le8 (Z_to_bv 64 11)) /\
         bytes_at rsegs m' (A + 48) (le8 (Z_to_bv 64 (fr + 2256))) /\
         bytes_at rsegs m' (A + 128) (le8 (Z_to_bv 64 (fr + 544))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814ec) fc None m (seg_rom rsegs)).
Proof.
  intros CATC ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr Sh spv cs Esp Es2 HfrGT HfrE Hfr8 HfrA HspA HA64 HspGT HspE Hsep HShD Hshc Happ Hwapp HAapp
    CHc HSHb STA ST HAC HSW H48b H128b.
  assert (HShb : 0 <= Sh + 332 /\ Sh + 333 <= 2 ^ 64).
  { assert (E : Sh + 332 = shadow_addr (fr + 2656)) by (rewrite Hshc; reflexivity).
    unfold shadow_addr, ASAN_K in E. Z.div_mod_to_equations; lia. }
  eapply ExecF.evtF_evt, (r1_call_evt_F CATC ExecF.RNG_all); try eassumption.
  - r1F_rng_all.
  - r1F_rng_all.
  - apply ExecF.rng_all; unfold GOT_CELL_K; lia.
  - apply ExecF.rng_all; unfold CELL_K; lia.
  - r1F_rng_all.
Qed.

(* The pins: each *_of_F states R1.v's v1.9 text, term for term. r1_call_evt_of_F differs from R1.r1_call_evt only
   in the first premise, which names the _F contract in place of the plain one; both are checked by name. *)
Example r1_call_evt_of_F_verbatim : True.
Proof.
  lazymatch type of R1.r1_call_evt with ?P -> ?A =>
  lazymatch type of r1_call_evt_of_F with ?Q -> ?B =>
    constr_eq P RBC.reac_box_catalogue_contract;
    constr_eq Q RBC.reac_box_catalogue_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.
