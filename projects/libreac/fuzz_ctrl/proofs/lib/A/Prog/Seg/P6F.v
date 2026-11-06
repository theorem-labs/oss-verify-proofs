(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its module paths, module names, addresses and numbers changed; 312 of its 369 lines of code are new or changed and 807 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P6.v 26275b3ec1b0 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: p6_evt_of_pre_post / p6_evt_ro_of_pre_post re-derive P6.p6_evt / P6.p6_evt_ro from the two stretches at
   ExecF.RNG_all and the PLAIN callee contract; the *_verbatim pins check by constr_eq that their types are the
   types of P6.p6_evt / P6.p6_evt_ro. Mechanical re-run, route (a) (lead 22:15Z); SPLIT STRETCHES (a Theorem Labs lane 00:45Z),
   because reac_ctrl_identity_reply has no _F contract of record. Input to the ported walk only. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP RcAsanFPLib reac_ctrl_parse_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import P6.
(* FPState (fp_regs / fp_csr) by its full name: importing image-A's YK11 would shadow the getr of P6.v's run
   lemmas, and the post stretches must state P6.v's own post. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YK11.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module RG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.

(* ---- stretch 1: 0x81bd8 .. the entry of reac_ctrl_identity_reply (0x83f8c), ra = 0x81bf8 ---- *)

Lemma p6_evt_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S -> mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp -> -> HS Hpa Hpp H232 H224 Hmod HKS HST HMI HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS R232 R224.
  assert (HL232 : ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 pa))).
  { pose proof (bytes_at_ov_read rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) 0 8 H232
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL224 : ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 pp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) 0 8 H224
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. (* 81bd8 li a0,0 *)
  step. (* 81bdc li a1,0 *)
  step. (* 81be0 ld s7,232(s1) *)
  step. (* 81be4 mv a2,s7 *)
  step. (* 81be8 ld s8,224(s1) *)
  step. (* 81bec mv a3,s8 *)
  step. (* 81bf0 mv a4,s4 *)
  step. (* 81bf4 jal reac_ctrl_identity_reply *)
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- stretch 2: the return pc 0x81bf8 with the canonical register map; the source run ends there, so the
   stretch takes no step and its premises are exactly the machine-level facts P6.v's script holds right after it
   applies the callee contract. ---- *)

Section PostF.
Context {fx : AYK.FPState}.

Lemma p6_evt_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s1 s3 s6 s9 s10 : word) (m : word -> option byte) (S FS : Z),
    getr (RG.mkR_of regs) 2 = sp -> getr (RG.mkR_of regs) 3 = gp -> getr (RG.mkR_of regs) 4 = tp ->
    getr (RG.mkR_of regs) 8 = s0 -> getr (RG.mkR_of regs) 9 = s1 -> getr (RG.mkR_of regs) 19 = s3 ->
    getr (RG.mkR_of regs) 26 = s10 -> getr (RG.mkR_of regs) 10 = Z_to_bv 64 (-1) ->
    getr (RG.mkR_of regs) 22 = s6 -> getr (RG.mkR_of regs) 25 = s9 ->
    munch (p6_W S FS) m mem -> wmono rsegs m mem -> mem_inv rsegs mem -> shadow_rw mem ->
    stk rsegs mem (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    addressable mem (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R AYK.fp_regs (Z_to_bv 64 0x81bf8) AYK.fp_csr None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (RG.mkR_of regs) AYK.fp_regs (Z_to_bv 64 0x81bf8) AYK.fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s1 s3 s6 s9 s10 m S FS K2 K3 K4 K8 K9 K19 K26 K10 K22 K25
    MU WM MI SW ST AD FP.
  apply ExecF.evtF_done.
  exists (RG.mkR_of regs), mem.
  split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K10|]. split; [exact K22|]. split; [exact K25|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact SW|].
  split; [exact ST|]. split; [exact AD | exact FP].
Qed.

End PostF.

(* ---- the two stretches at ExecF.RNG_all, with the PLAIN callee contract, re-derive P6.v's runs ---- *)

Lemma p6_evt_of_pre_post : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S -> mem_inv rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x81bf8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\ getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp E1 E2 HS Hpa Hpp H232 H224 Hmod HKS HST HMI HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS.
  pose proof (bytes_at_bound rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) H232) as Hb232.
  rewrite length_le8 in Hb232.
  pose proof (bytes_at_bound rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) H224) as Hb224.
  rewrite length_le8 in Hb224.
  eapply LE.evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (p6_evt_pre_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 Fr fc m A S FS pa pp); try assumption.
    all: apply ExecF.rng_all; lia. }
  intros ms' ->.
  pose proof RPL as HR. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HR.
  eapply LE.evt_cut.
  { eapply HR with (fr := 0) (len := 0) (S := S) (FS := FS) (g := repeat (Z_to_bv 8 0) 50)
      (ja := []) (jp := []) (jn := []).
    all: try (symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.Z_to_bv_bv_unsigned).
    all: try reflexivity.
    all: try (let HH := fresh "HH" in intros HH; rewrite p6_args0 in HH; discriminate HH).
    all: try exact (u64_range _).
    all: try assumption.
    all: try (rewrite p6_Wc0, p6_D0; assumption).
    all: try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & _ & AC' & SW' & AD' & FP' & TL').
  subst ms'.
  rewrite p6_fp0 in MU. rewrite p6_Wc0, p6_D0 in FP'. rewrite p6_ret0.
  replace (ret_pc (Z_to_bv 64 0x81bf8)) with (Z_to_bv 64 0x81bf8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (@p6_evt_post_F (AYK.mkFP Fr fc) ExecF.RNG_all
           (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5 s6 (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3' t4' t5' t6')
           m' sp gp tp s0 s1 s3 s6 s9 s10 m S FS);
    try reflexivity; try assumption.
Qed.

(* The pin: p6_evt_of_pre_post states P6.p6_evt's v1.9 text, term for term (constr_eq: syntactic, not up to
   conversion), the plain callee contract included as the first premise. *)
Example p6_evt_of_pre_post_verbatim : True.
Proof.
  let a := type of P6.p6_evt in let b := type of p6_evt_of_pre_post in constr_eq a b.
  exact I.
Qed.

(* P6.v imports image-A's YK11 before its second half (P6.v:277), so p6_evt_ro's statement is written with that
   YK11's getr. Import it here too, after everything above, so the ro stretches state P6.v's text. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* The same stretch from ro_agree instead of mem_inv (P6.v p6_evt_ro's premises): the eight instructions read only
   the two spills, so the script is the same. Its ro_agree, and p6_evt_ro_post_F's, is lib.A.MemNorm's (the copy
   the image-A walk states). *)
Lemma p6_evt_ro_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.rng RNG (A + 224) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81bf8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s4 a5 a6 a7 s2 s3 s4 s5 s6
                                (Z_to_bv 64 pa) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp -> -> HS Hpa Hpp H232 H224 Hmod HKS HST HRO HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS R232 R224.
  assert (HL232 : ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (le8 (Z_to_bv 64 pa))).
  { pose proof (bytes_at_ov_read rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) 0 8 H232
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL224 : ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (le8 (Z_to_bv 64 pp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) 0 8 H224
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step. step. step. step. step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* ---- stretch 2: the return pc 0x81bf8 with the canonical register map; the source run ends there, so the
   stretch takes no step and its premises are exactly the machine-level facts P6.v's script holds right after it
   applies the callee contract. ---- *)

Section PostRoF.
Context {fx : FPState}.


Lemma p6_evt_ro_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (sp gp tp s0 s1 s3 s6 s9 s10 : word) (m : word -> option byte) (S FS : Z),
    getr (RG.mkR_of regs) 2 = sp -> getr (RG.mkR_of regs) 3 = gp ->
    getr (RG.mkR_of regs) 4 = tp ->
    getr (RG.mkR_of regs) 8 = s0 -> getr (RG.mkR_of regs) 9 = s1 ->
    getr (RG.mkR_of regs) 19 = s3 ->
    getr (RG.mkR_of regs) 26 = s10 -> getr (RG.mkR_of regs) 10 = Z_to_bv 64 (-1) ->
    getr (RG.mkR_of regs) 22 = s6 -> getr (RG.mkR_of regs) 25 = s9 ->
    munch (p6_W S FS) m mem -> wmono rsegs m mem ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs mem -> shadow_rw mem ->
    stk rsegs mem (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    addressable mem (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R fp_regs (Z_to_bv 64 0x81bf8) fp_csr None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\
         getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\
         getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (RG.mkR_of regs) fp_regs (Z_to_bv 64 0x81bf8) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem sp gp tp s0 s1 s3 s6 s9 s10 m S FS K2 K3 K4 K8 K9 K19 K26 K10 K22 K25
    MU WM RO SW ST AD FP.
  apply ExecF.evtF_done.
  exists (RG.mkR_of regs), mem.
  split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K10|]. split; [exact K22|]. split; [exact K25|].
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact SW|].
  split; [exact ST|]. split; [exact AD | exact FP].
Qed.

End PostRoF.

(* The ro run is the plain run on the normalized memory (P6.v:629-633 applies p6_evt there), so its derivation
   composes the two plain stretches under MemNorm.evt_normalize and carries the post back with P6.v's own
   mem_rel lemmas; the ro-form stretches above (p6_evt_ro_pre_F / p6_evt_ro_post_F) are the pieces the walk's
   glue consumes. Its two ro_agree are lib.A.MemNorm's by full path, as P6.p6_evt_ro's statement writes them, so
   the constr_eq pin below compares the same constant whether or not BzBridge also loads the root lib.MemNorm. *)
Lemma p6_evt_ro_of_pre_post : reac_ctrl_identity_reply_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A S FS pa pp : Z),
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 S ->
    0 <= S < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 ->
    bytes_at rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) ->
    bytes_at rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) ->
    S mod 16 = 0 -> REAC_CTRL_IDENTITY_REPLY_K <= S ->
    stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
       [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [] ->
    reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x81bf8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\
         getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 (-1) /\
         getr R 22 = s6 /\ getr R 25 = s9 /\
         munch (p6_W S FS) m m' /\ wmono rsegs m m' /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
         addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
            [(S - REAC_CTRL_IDENTITY_REPLY_K, S)] [])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81bd8) fc None m (seg_rom rsegs)).
Proof.
  intros RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A S FS pa pp E1 E2 HS Hpa Hpp H232 H224 Hmod HKS HST HRO HAC HSW Hlo Hhi HADW HADB HRB HRM HGC
    HC254 HC255 HFP HTLS.
  assert (HKv : REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  eapply LE.evt_mono.
  - eapply MN.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
    pose proof (bytes_at_bound rsegs m (A + 232) (le8 (Z_to_bv 64 pa)) H232) as Hb232.
    rewrite length_le8 in Hb232.
    pose proof (bytes_at_bound rsegs m (A + 224) (le8 (Z_to_bv 64 pp)) H224) as Hb224.
    rewrite length_le8 in Hb224.
    apply (p6_evt_of_pre_post RPL ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 Fr fc (MN.normalize rsegs m) A S FS pa pp E1 E2 HS Hpa Hpp).
    + exact (p6_ba_rel m _ _ _ REL H232).
    + exact (p6_ba_rel m _ _ _ REL H224).
    + exact Hmod.
    + exact HKS.
    + exact (p6_stk_rel m (MN.normalize rsegs m) (S - REAC_CTRL_IDENTITY_REPLY_K) S REL
               ltac:(lia) ltac:(lia) HST).
    + exact (MN.mem_inv_normalize rsegs m).
    + exact (p6_cells_rel m _ REL HAC).
    + exact (p6_shadow_rw_rel m _ REL HSW).
    + exact Hlo.
    + exact Hhi.
    + exact (p6_addressable_rel m _ _ _ REL HADW).
    + exact (p6_addressable_rel m _ _ _ REL HADB).
    + exact (p6_ba_rel m _ _ _ REL HRB).
    + exact (p6_ba_rel m _ _ _ REL HRM).
    + exact (p6_ba_rel m _ _ _ REL HGC).
    + exact (p6_ba_rel m _ _ _ REL HC254).
    + exact (p6_ba_rel m _ _ _ REL HC255).
    + exact (p6_fp_rel _ m _ _ _ _ _ _ _ REL HFP).
    + exact (p6_reply_tls_rel m _ _ _ _ _ REL HTLS).
  - pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
    intros s (s0' & (R & m0' & -> & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P10 & P22 & P25 & MU0 & WM0 & _ & SW0
               & ST0 & AD0
               & FP0) & MR & RS).
    destruct MR as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
    destruct s as [Rs Fs pcs svcs rvs fcs ms ros].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS. subst Rs Fs pcs svcs rvs fcs ros.
    exists R, ms. split; [reflexivity|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P10|].
    split; [exact P22|]. split; [exact P25|].
    split; [exact (MN.munch_rel rsegs _ m _ ms m0' REL Hmem RS MU0)|].
    split; [exact (MN.wmono_rel rsegs m _ ms m0' REL Hmem RS WM0)|].
    split; [exact (MN.ro_agree_same rsegs m ms HRO RS)|].
    split; [exact (p6_shadow_rw_back ms m0' Hmem SW0)|].
    split; [exact (p6_stk_rel_back ms m0' (S - REAC_CTRL_IDENTITY_REPLY_K) S Hmem ltac:(lia) ltac:(lia) ST0)|].
    split; [exact (p6_addressable_back ms m0' _ _ Hmem AD0)|].
    exact (p6_fp_back _ ms m0' _ _ _ _ _ _ Hmem FP0).
Qed.

(* The pin: p6_evt_ro_of_pre_post states P6.p6_evt_ro's v1.9 text, term for term. *)

Example p6_evt_ro_of_pre_post_verbatim : True.
Proof.
  let a := type of P6.p6_evt_ro in let b := type of p6_evt_ro_of_pre_post in constr_eq a b.
  exact I.
Qed.
