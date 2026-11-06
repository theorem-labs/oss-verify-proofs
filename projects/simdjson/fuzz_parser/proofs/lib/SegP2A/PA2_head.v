(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz PA2_reg APS2_iface A2Lib PA2_t0e PA2_entry PA2_win.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c PA2_sm5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2E_defs A2E_cert A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition GP0e : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0e_frame : SG.gp_frameP GP0e (fun _ _ => []). Proof. intros id args E M M' _ _. exact I. Qed.
Lemma GP0e_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds A2E_defs.SG GP0e c. Proof. intros c H. discriminate H. Qed.

Lemma a2e_run : forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  SX.aw_genuine E (SP.p_A A2E_defs.A2E) -> rfull R -> regs_ok E A2E_defs.T0_regs R -> know_ok A2E_defs.SG E m A2E_defs.T0_kn ->
  mem_inv A2E_defs.SG m -> frm0 fc ->
  ExecF.evtF A2E_defs.SG (SX.fp_of (SP.p_A A2E_defs.A2E) E) (SLib.xpost A2E_defs.SG GP0e A2E_defs.A2E E m rom)
    (MS R F (Z_to_bv 64 0x99f60) fc None m rom).
Proof.
  intros E m rom R F fc HAG HF HR HK MI HZ.
  exact (SLib.prog_evt A2E_defs.SG GP0e (fun _ _ => []) (fun _ => false) GP0e_frame GP0e_vc A2E_defs.A2E A2E_defs.A2E_IT 400 false []
           A2E_defs.T0 A2E_cert.a2e_cert (SP.itab_ranges_sound A2E_defs.SG _) ltac:(intros TA []) ltac:(intros Sm [])
           ltac:(left; reflexivity) E m rom R F fc HAG HF HR HK (Forall_nil _) MI HZ).
Qed.

(* [comment removed for export] *)
Lemma ez_w : forall ZL e (w : word), zok e = true -> zden ZL e mod M64 = u w -> edenot (mkEZ ZL) e = w.
Proof.
  intros ZL e w Hz H. rewrite zden_ok by exact Hz. apply bv_eq. rewrite u_Z_to_bv. exact H.
Qed.

Lemma a2e_regs : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (THIS DOC B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z),
  u sp mod 16 = 0 -> 0 <= THIS < M64 -> THIS mod 8 = 0 -> 0 <= DOC < M64 -> DOC mod 8 = 0 ->
  regs_ok (mkEZ (ZL_t0e (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                        (u s10) (u s11) (THIS / 8) (DOC / 8) B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
                        [u t0; u t1; u t2; u a2; u a3; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]))
    A2E_defs.T0_regs
    (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros. apply regs_ok_mkR.
  change (map (fun k => edenot ?E (sr_get A2E_defs.T0_regs (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl A2E_defs.T0_regs)).
  cbn [tl A2E_defs.T0_regs map].
  repeat (apply (f_equal2 (@cons word)); [apply ez_w; [reflexivity|];
            cbv [A2E_defs.vRA A2E_defs.vSP A2E_defs.vSP16 A2E_defs.vGP A2E_defs.vTP A2E_defs.vS0 A2E_defs.vS1 A2E_defs.vS2 A2E_defs.vS3
                 A2E_defs.vS4 A2E_defs.vS5 A2E_defs.vS6 A2E_defs.vS7 A2E_defs.vS8 A2E_defs.vS9 A2E_defs.vS10 A2E_defs.vS11
                 A2E_defs.vTHIS A2E_defs.vT8 A2E_defs.vDOC A2E_defs.vDOC8 A2E_defs.V A2E_defs.mul];
            cbn [zden nth ZL_t0e app]; rewrite ?u_Z_to_bv;
            first [ apply Z.mod_small; apply u_rngA | (pose proof (u_rngA sp); Z.div_mod_to_equations; lia) ] |]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xsm_regs : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  SP.gagree 35 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs A2E_defs.XSM) R' ->
  exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    R' = mkR (Z_to_bv 64 0x99fd4) (edenot E' (EVar 35)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0)) x5 x6 x7
             (Z_to_bv 64 (16 * nth 1 ZL 0)) (edenot E' (EVar 35)) (Z_to_bv 64 1312) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 2147450880) (Z_to_bv 64 (nth 7 ZL 0)) (Z_to_bv 64 (nth 8 ZL 0)) (Z_to_bv 64 (8 * nth 16 ZL 0))
             (Z_to_bv 64 (nth 10 ZL 0)) (Z_to_bv 64 (8 * nth 17 ZL 0)) (Z_to_bv 64 (nth 12 ZL 0)) (Z_to_bv 64 (nth 13 ZL 0))
             (Z_to_bv 64 (nth 14 ZL 0)) (Z_to_bv 64 (nth 15 ZL 0)) x28 x29 x30 x31.
Proof.
  intros ZL E' R' Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (EV : forall k, (k < 35)%nat -> edenot E' (EVar k) = Z_to_bv 64 (nth k ZL 0)).
  { intros k Hk. rewrite <- (SP.edenot_gagree 35 _ _ (EVar k) Hg Hb ltac:(cbn; apply Nat.leb_le; lia)). reflexivity. }
  assert (EZ : forall e, AxSymRun3.expr_vars_lt 35 e = true -> zok e = true -> edenot E' e = Z_to_bv 64 (zden ZL e)).
  { intros e H1 H2. rewrite <- (SP.edenot_gagree 35 _ _ e Hg Hb H1), zden_ok by exact H2. reflexivity. }
  change (sr_get (ST.t_regs A2E_defs.XSM) 1) with (ELit 0x99fd4);
  change (sr_get (ST.t_regs A2E_defs.XSM) 2) with (EVar 35);
  change (sr_get (ST.t_regs A2E_defs.XSM) 3) with (EVar 2); change (sr_get (ST.t_regs A2E_defs.XSM) 4) with (EVar 3);
  change (sr_get (ST.t_regs A2E_defs.XSM) 8) with (EMd M_MUL (ELit 16) (EVar 1));
  change (sr_get (ST.t_regs A2E_defs.XSM) 9) with (EVar 35); change (sr_get (ST.t_regs A2E_defs.XSM) 10) with (ELit 1312);
  change (sr_get (ST.t_regs A2E_defs.XSM) 18) with (ELit 2147450880);
  change (sr_get (ST.t_regs A2E_defs.XSM) 19) with (EVar 7); change (sr_get (ST.t_regs A2E_defs.XSM) 20) with (EVar 8);
  change (sr_get (ST.t_regs A2E_defs.XSM) 21) with (EMd M_MUL (ELit 8) (EVar 16));
  change (sr_get (ST.t_regs A2E_defs.XSM) 22) with (EVar 10);
  change (sr_get (ST.t_regs A2E_defs.XSM) 23) with (EMd M_MUL (ELit 8) (EVar 17));
  change (sr_get (ST.t_regs A2E_defs.XSM) 24) with (EVar 12); change (sr_get (ST.t_regs A2E_defs.XSM) 25) with (EVar 13);
  change (sr_get (ST.t_regs A2E_defs.XSM) 26) with (EVar 14); change (sr_get (ST.t_regs A2E_defs.XSM) 27) with (EVar 15).
  rewrite !(EZ (EMd M_MUL (ELit 16) (EVar 1))) by reflexivity. rewrite !(EZ (EMd M_MUL (ELit 8) (EVar 16))) by reflexivity.
  rewrite !(EZ (EMd M_MUL (ELit 8) (EVar 17))) by reflexivity.
  set (spw := edenot E' (EVar 35)). rewrite !EV by lia. cbn [zden edenot]. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma a2e_munch : forall (ZL : list Z) (m m' : amem) (zsp : Z),
  zsp = 16 * nth 1 ZL 0 -> 384 <= zsp < M64 ->
  (forall x : word, SP.outside_wins (mkEZ ZL) (SP.p_W A2E_defs.A2E) (u x) -> m' x = m x) ->
  munch [(zsp - 384, zsp)] m m'.
Proof.
  intros ZL m m' zsp E H FR x Hx. apply FR. unfold SP.outside_wins. cbn [SP.p_W A2E_defs.A2E SP.PGCA SP.PGX].
  pose proof (u_rngA x). cbn [outside] in Hx.
  repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity;
    cbn [zden A2E_defs.vSP A2E_defs.vSP16 A2E_defs.V A2E_defs.mul]; rewrite <- E; rewrite ?(Z.mod_small _ M64) by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma xsm_kfacts : forall (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (E' : env) (m1 : amem),
  SP.gagree 35 (mkEZ (ZL_t0e zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                             T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) E' ->
  eb (mkEZ (ZL_t0e zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                   T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) = eb E' ->
  know_ok asegs E' m1 (ST.t_know A2E_defs.XSM) ->
  0 <= 16 * SP16 < M64 ->
  u (edenot E' (EVar 35)) mod 32 = 0 /\ 384 <= (16 * SP16 - u (edenot E' (EVar 35))) mod M64 <= 415
  /\ bytes_at asegs m1 (16 * SP16 - 384) (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ (forall k, 0 <= k < 13 -> bytes_at asegs m1 (16 * SP16 - 8 - 8 * k)
                 (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0)))).
Proof.
  intros until m1. intros Hg Hb HK HSP.
  assert (ESP : edenot E' (EMd M_MUL (ELit 16) (EVar 1)) = Z_to_bv 64 (16 * SP16)).
  { rewrite <- (SP.edenot_gagree 35 _ _ (EMd M_MUL (ELit 16) (EVar 1)) Hg Hb eq_refl), zden_ok by reflexivity. reflexivity. }
  split; [| split; [| split]].
  - pose proof (know_nth _ _ _ _ 0 _ HK eq_refl) as K. exact (proj2 K).
  - pose proof (know_nth _ _ _ _ 1 _ HK eq_refl) as K. cbn [kentry_ok] in K.
    change (A2E_defs.sub A2E_defs.vSP (A2E_defs.V 35)) with (EAlu ALU_SUB (EMd M_MUL (ELit 16) (EVar 1)) (EVar 35)) in K.
    change (edenot E' (EAlu ALU_SUB (EMd M_MUL (ELit 16) (EVar 1)) (EVar 35)))
      with (alu64 ALU_SUB (edenot E' (EMd M_MUL (ELit 16) (EVar 1))) (edenot E' (EVar 35))) in K.
    rewrite alu_sub, ESP in K. unfold v_sub in K. rewrite !u_Z_to_bv, (Z.mod_small (16 * SP16)) in K by lia.
    exact K.
  - pose proof (know_nth _ _ _ _ 2 _ HK eq_refl) as K.
    lazymatch type of K with kentry_ok _ _ _ (KWord (SA ?b ?kk) ?w ?v) =>
      pose proof (kx_word_g asegs 35 _ E' m1 b kk w v Hg Hb eq_refl eq_refl eq_refl K) as B end. cbn [zden nth ZL_t0e app] in B.
    rewrite (Z.mod_small (16 * SP16)) in B by lia. replace (16 * SP16 + -384) with (16 * SP16 - 384) in B by lia. exact B.
  - intros k Hk.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
    destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
    match goal with |- bytes_at _ _ (16 * SP16 - 8 - 8 * ?k) _ =>
      let j := eval vm_compute in (Z.to_nat (3 + k)) in
      pose proof (know_nth _ _ _ _ j _ HK eq_refl) as K;
      lazymatch type of K with kentry_ok _ _ _ (KWord (SA ?b ?kk) ?w ?v) =>
        pose proof (kx_word_g asegs 35 _ E' m1 b kk w v Hg Hb eq_refl eq_refl eq_refl K) as B end; cbn [zden nth ZL_t0e app] in B;
      rewrite (Z.mod_small (16 * SP16)) in B by lia;
      let o := eval vm_compute in (-8 - 8 * k) in
      replace (16 * SP16 - 8 - 8 * k) with (16 * SP16 + o) by lia; exact B
    end.
Qed.

(* [comment removed for export] *)
Lemma blk_rngs8 : forall (AI : AMallocIface) L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
  rng RNG A n /\ rng RNG (A / 8 + SH) ((n + 7) / 8).
Proof.
  intros AI L RNG st LB m p A n AH Hin. destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (_ & _ & R1 & R2 & _).
  split; [exact R1|]. rewrite shad_div in R2. unfold shlen in R2. rewrite Z.shiftr_div_pow2 in R2 by lia. change (2 ^ 3) with 8 in R2.
  unfold ASHOFF in R2. replace (A / 8 + SH) with (2147450880 + A / 8) by lia. exact R2.
Qed.

(* [comment removed for export] *)
Lemma a2t0_regs : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word)
    (THIS DOC F SPAX B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 FLAG BO BG IG SG : Z),
  u sp mod 16 = 0 -> 0 <= THIS < M64 -> THIS mod 8 = 0 -> 0 <= DOC < M64 -> DOC mod 8 = 0 -> 0 <= F < M64 -> F mod 2048 = 0 ->
  0 <= SPAX < M64 -> SPAX mod 32 = 0 -> 384 <= u sp - SPAX <= 415 ->
  regs_ok (mkEZ (PA2_t0c.ZL_t0'' (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                        (u s10) (u s11) (THIS / 8) (DOC / 8) B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 (F / 2048) ((u sp - 384 - SPAX) / 16)
                        FLAG BO BG IG SG
                        [u x5; u x6; u x7; u a1; u a2; u a3; u a4; u a5; u a6; u a7; u s3; u s4; u s6; u s8; u s9; u s10; u s11;
                         u x28; u x29; u x30; u x31]))
    A2_defs.T0_regs
    (mkR (Z_to_bv 64 0x99fd4) (Z_to_bv 64 SPAX) gp tp x5 x6 x7 sp (Z_to_bv 64 SPAX) (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 2147450880) s3 s4 (Z_to_bv 64 THIS) s6 (Z_to_bv 64 DOC) s8 s9 s10 s11 x28 x29 x30 x31).
Proof.
  intros. apply regs_ok_mkR.
  change (map (fun k => edenot ?E (sr_get A2_defs.T0_regs (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl A2_defs.T0_regs)).
  cbn [tl A2_defs.T0_regs map].
  repeat (apply (f_equal2 (@cons word)); [apply ez_w; [reflexivity|];
            cbv [A2_defs.vRA A2_defs.vSP A2_defs.vSP16 A2_defs.vGP A2_defs.vTP A2_defs.vSPA A2_defs.vPB A2_defs.vF A2_defs.vF11
                 A2_defs.vTHIS A2_defs.vT8 A2_defs.vDOC A2_defs.vDOC8 A2_defs.V A2_defs.mul A2_defs.add A2_defs.sub];
            cbn [zden nth PA2_t0c.ZL_t0'' app]; rewrite ?u_Z_to_bv;
            first [ reflexivity | (apply Z.mod_small; apply u_rngA) | (f_equal; pose proof (u_rngA sp); Z.div_mod_to_equations; lia) ] |]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u32bytes_eqA : forall l, S2G2.u32bytes l = SjS1Bytes.u32bytes l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [S2G2.u32bytes SjS1Bytes.u32bytes]. rewrite IH. reflexivity. Qed.
Lemma bufbytes_eqA : forall d, S2G2.bufbytes d = s1buf d.
Proof. reflexivity. Qed.
Lemma s1buf_lenA : forall d, Z.of_nat (length (s1buf d)) = zlength d + 64.
Proof. intros d. unfold s1buf, zlength. rewrite length_map, length_app, repeat_length. lia. Qed.

(* [comment removed for export] *)
Lemma mbytes_of_bytes_at_heapA : forall m A bs, bytes_at asegs m A bs -> 0x665000 <= A -> A + Z.of_nat (length bs) < M64 ->
  S2G2.mbytes m A bs.
Proof.
  intros m A bs (H0 & H1 & HB) HA1 HA2 i Hi. specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  rewrite ref_mrd_overlay in HB by (rewrite u_Z_to_bv, Z.mod_small by lia; lia). unfold wa in HB. rewrite HB.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Section H.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM5 : stack_malloc_5_stmt AI fflag rng_fs.
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (FR : bvmap 5 word) (fc : bv 32)
            (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rstk : region) (d idx : list Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x24 x88 : word) (jtp jsb joc jia : list byte) (cls FA FN : Z).
  Hypothesis AH : AHEAP AI L RNG st LB m.
  Hypothesis ND : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia].
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * zlength idx + 16 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + zlength d + 64 <= ACP + ncp.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis NO5 : forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB.
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at asegs m BUF (s1buf d).
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Sn : 1 <= zlength idx <= zlength d.
  Hypothesis Hscan : scan d = (true, idx).
  Hypothesis Hd : Forall (fun c => 0 <= c < 256) d.
  Hypothesis HIDX : rw_cells asegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  Hypothesis HO8 : rw_cells asegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO24 : rw_cells asegs m (THIS + 24) [C4 x24].
  Hypothesis HO40 : rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  Hypothesis HDSH : rw_cells asegs m (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HDR : rng RNG DOC 16.
  Hypothesis HDSR : rng RNG (Z.shiftr DOC 3 + 2147450880) 2.
  Hypothesis HTB : rw_cells asegs m TPA [CB (Z.to_nat ntp) jtp].
  Hypothesis HSB : rw_cells asegs m SBA [CB (Z.to_nat nsb) jsb].
  Hypothesis HOC : rw_cells asegs m AOC [CB 8192 joc].
  Hypothesis HIA : rw_cells asegs m AIA [CB 1024 jia].
  Hypothesis HCIMG : client_img m.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis HSTK : stk asegs m lo (u sp).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis HCL : rclean m rstk.
  Hypothesis HCL1 : r_lo rstk <= lo.
  Hypothesis HCL2 : u sp <= r_hi rstk.
  Hypothesis HCLR : rrng RNG rstk.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis HMI : mem_inv asegs m.
  Hypothesis HZ : frm0 fc.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  Hypothesis HRS : rng RNG lo (al_top L - lo).
  Hypothesis HRI : rng_aimg RNG.
  Hypothesis HRIS : rng_aimg_sh RNG.
  Hypothesis HRFS : rng_fs L RNG.

  (* [comment removed for export] *)
  Definition ZL2 (F SPAX : Z) (rest : list Z) : list Z :=
    PA2_t0c.ZL_t0'' (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
      (u s9) (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) (zlength d) (ASI / 8) (zlength idx) (TPA / 8) (ntp / 8)
      (SBA / 8) nsb (AOC / 8) (AIA / 8) (F / 2048) ((u sp - 384 - SPAX) / 16) (fflag L 5 F) (BUF mod 8)
      ((zlength d + BUF mod 8 + 64) / 8) ((4 * zlength idx + 12 + 7) / 8) (nsb / 8) rest.

  (* [comment removed for export] *)
  Definition QT0 (ms2 : machine_state) : Prop :=
    exists (F SPAX : Z) (x5 x6 x7 a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 : word) (FR2 : bvmap 5 word) (fc2 : bv 32) (m2 : amem),
      let ZL := ZL2 F SPAX [u x5; u x6; u x7; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7'; u s3; u s4; u s6;
                            u s8; u s9; u s10; u s11; u x28; u x29; u x30; u x31] in
      let R2 := mkR (Z_to_bv 64 0x99fd4) (Z_to_bv 64 SPAX) gp tp x5 x6 x7 sp (Z_to_bv 64 SPAX) (Z_to_bv 64 F)
                    a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SH) s3 s4 (Z_to_bv 64 THIS) s6 (Z_to_bv 64 DOC) s8 s9 s10 s11 x28 x29 x30 x31 in
      ms2 = MS R2 FR2 (Z_to_bv 64 0x99fd4) fc2 None m2 (seg_rom asegs)
      /\ frm0 fc2 /\ mem_inv asegs m2
      /\ regs_ok (mkEZ ZL) A2_defs.T0_regs R2
      /\ know_ok asegs (mkEZ ZL) m2 A2_defs.T0_kn
      /\ SG.gholds (S2G2.gp2 asegs d (idx ++ [zlength d; zlength d; 0])) (mkEZ ZL) m2 (ST.t_ghost A2_defs.T0)
      /\ fp_le (SX.fp_of (SP.p_A A2_defs.A2) (mkEZ ZL)) RNG /\ SX.aw_genuine (mkEZ ZL) (SP.p_A A2_defs.A2)
      /\ SPAX mod 32 = 0 /\ 384 <= u sp - SPAX <= 415
      /\ AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2
      /\ aheap_pres CI LB (u sp) m m2
      /\ stk asegs m2 lo (u sp)
      /\ F mod 2048 = 0 /\ ablk F (F + 2048) /\ F + 2048 <= ATOP /\ rng RNG F 2048 /\ rng RNG (shad F) 256
      /\ rw_cells asegs m2 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]
      /\ (forall a, aclient_addr CI LB SPAX a -> a < shad F \/ shad F + 256 <= a).

  Lemma a2_head :
    evtF asegs RNG QT0
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 ASTAGE2) fc None m (seg_rom asegs)).
  Proof using All.
    pose proof Hlo2 as Hlo2'. unfold STAGE2_STACK_A in Hlo2'. atop_facts. pose proof (u_rngA sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & HTOP & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ith) as (_ & Ht0 & Ht1 & Ht2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isi) as (_ & Hi0 & Hi1 & Hi2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Icp) as (_ & Hc0 & Hc1 & Hc2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Itp) as (_ & Hp0 & Hp1 & Hp2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isb) as (_ & Hs0 & Hs1 & Hs2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ioc) as (_ & Ho0 & Ho1 & Ho2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Iia) as (_ & Ha0 & Ha1 & Ha2 & _).
    assert (HFN : 0 <= FN) by (unfold ablk in Hfk3; lia).
    pose proof (fake_band FA FN Hfk3 HFN) as (_ & Hf0 & Hf1).
    assert (Hsp47 : u sp <= 2 ^ 47) by lia.
    pose proof (e16_of_16 (u sp) Hsp16) as E_SP. pose proof (e8_of_16 THIS Ht2) as E_T8. pose proof (e8_of_8 DOC Hda) as E_DOC8.
    pose proof (e8_of_16 ASI Hi2) as E_I8.
    (* [comment removed for export] *)
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Ith) as [RT RTS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Isi) as [RI RIS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Icp) as [RC RCS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Itp) as [RP RPS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Isb) as [RS RSS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Ioc) as [RO ROS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH Iia) as [RA RAS].
    set (LEN := zlength d) in *. set (NN := zlength idx) in *.
    assert (R_STK : rng RNG (16 * (u sp / 16) - 8608) 8608) by (eapply rng_sub'; [exact HRS | lia]).
    assert (R_STKSH : rng RNG (2 * (u sp / 16) + SH - 1076) 1076).
    { pose proof (shclean_hull _ _ _ _ _ (rclean_shclean _ _ HCL)) as (HH1 & HH2 & HH3 & HH4 & HH5 & HH6).
      unfold rrng in HCLR. rewrite !shad_div in HCLR. unfold ASHOFF in HCLR. eapply rng_sub'; [exact HCLR|].
      clear - HH1 HH2 HH5 HCL1 HCL2 Hlo2' E_SP Hsp16. Z.div_mod_to_equations. lia. }
    assert (R_T : rng RNG (8 * (THIS / 8)) 96) by (eapply rng_sub'; [exact RT | clear - Ht2 Hnim; Z.div_mod_to_equations; lia]).
    assert (R_TS : rng RNG (THIS / 8 + SH) 12) by (eapply rng_sub'; [exact RTS | clear - Hnim; Z.div_mod_to_equations; lia]).
    assert (R_D : rng RNG (8 * (DOC / 8)) 16) by (eapply rng_sub'; [exact HDR | clear - Hda; Z.div_mod_to_equations; lia]).
    assert (R_DS : rng RNG (DOC / 8 + SH) 2).
    { rewrite Z.shiftr_div_pow2 in HDSR by lia. change (2 ^ 3) with 8 in HDSR. eapply rng_sub'; [exact HDSR | lia]. }
    assert (R_B : rng RNG (8 * (BUF / 8) + BUF mod 8) (LEN + 64)) by (eapply rng_sub'; [exact RC | clear - Hb1 Hb2; Z.div_mod_to_equations; lia]).
    assert (R_BS : rng RNG (BUF / 8 + SH) ((LEN + BUF mod 8 + 64) / 8))
      by (eapply rng_sub'; [exact RCS | clear - Hb1 Hb2 Hc0 Hc1 Hc2; Z.div_mod_to_equations; lia]).
    assert (R_I : rng RNG (8 * (ASI / 8)) (4 * NN + 12)) by (eapply rng_sub'; [exact RI | clear - Hi2 Hnsi; Z.div_mod_to_equations; lia]).
    assert (R_IS : rng RNG (ASI / 8 + SH) ((4 * NN + 12 + 7) / 8))
      by (eapply rng_sub'; [exact RIS | clear - Hnsi Hi2; Z.div_mod_to_equations; lia]).
    assert (R_TB : rng RNG (8 * (TPA / 8)) (8 * (ntp / 8))) by (eapply rng_sub'; [exact RP | clear - Hp2 Hntp8; Z.div_mod_to_equations; lia]).
    assert (R_TBS : rng RNG (TPA / 8 + SH) (ntp / 8)) by (eapply rng_sub'; [exact RPS | clear; Z.div_mod_to_equations; lia]).
    assert (R_SB : rng RNG (8 * (SBA / 8)) nsb) by (eapply rng_sub'; [exact RS | clear - Hs2; Z.div_mod_to_equations; lia]).
    assert (R_SBS : rng RNG (SBA / 8 + SH) (nsb / 8)) by (eapply rng_sub'; [exact RSS | clear; Z.div_mod_to_equations; lia]).
    assert (R_OC : rng RNG (8 * (AOC / 8)) 8192) by (eapply rng_sub'; [exact RO | clear - Ho2 Hnoc; Z.div_mod_to_equations; lia]).
    assert (R_OCS : rng RNG (AOC / 8 + SH) 1024) by (eapply rng_sub'; [exact ROS | clear - Hnoc; Z.div_mod_to_equations; lia]).
    assert (R_IA : rng RNG (8 * (AIA / 8)) 1024) by (eapply rng_sub'; [exact RA | clear - Ha2 Hnia; Z.div_mod_to_equations; lia]).
    assert (R_IAS : rng RNG (AIA / 8 + SH) 128) by (eapply rng_sub'; [exact RAS | clear - Hnia; Z.div_mod_to_equations; lia]).
    clear RT RTS RI RIS RC RCS RP RPS RS RSS RO ROS RA RAS.
    (* [comment removed for export] *)
    pose (ZLE := ZL_t0e (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
                        (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) LEN (ASI / 8) NN (TPA / 8) (ntp / 8)
                        (SBA / 8) nsb (AOC / 8) (AIA / 8) 0 0 0 (BUF mod 8) ((LEN + BUF mod 8 + 64) / 8)
                        ((4 * NN + 12 + 7) / 8) (nsb / 8)
                        [u t0; u t1; u t2; u a2; u a3; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]).
    assert (KN : know_ok asegs (mkEZ ZLE) m A2E_defs.T0_kn) by (unfold ZLE, LEN, NN; eapply a2e_kn_of; eassumption).
    assert (RG : regs_ok (mkEZ ZLE) A2E_defs.T0_regs
                   (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      by (unfold ZLE; apply a2e_regs; lia).
    assert (W_SP : 8608 <= 16 * (u sp / 16) <= 2 ^ 47) by (rewrite <- E_SP; clear - Hlo2' Hlo1 Hsp47; lia).
    assert (W_SZ : 0 <= LEN < 2^40 /\ 0 <= NN < 2^40 /\ 1 <= ntp / 8 < 2^40 /\ 1 <= nsb < 2^40 /\ 1 <= (LEN + BUF mod 8 + 64) / 8 < 2^40
                   /\ 1 <= (4 * NN + 12 + 7) / 8 < 2^40 /\ 1 <= nsb / 8 < 2^40 /\ 0 <= BUF mod 8 < 8)
      by (clear - Hlen Sn Hntp Hnsb; Z.div_mod_to_equations; lia).
    assert (W_B8 : 0 <= THIS / 8 /\ 0 <= DOC / 8 /\ 0 <= BUF / 8 /\ 0 <= ASI / 8 /\ 0 <= TPA / 8 /\ 0 <= SBA / 8 /\ 0 <= AOC / 8
                   /\ 0 <= AIA / 8 /\ 0 <= 0)
      by (clear - Ht0 Hi0 Hc0 Hp0 Hs0 Ho0 Ha0 Hf0 Hfk1 Hb1; Z.div_mod_to_equations; lia).
    assert (WIN : fp_le (SX.fp_of (SP.p_A A2E_defs.A2E) (mkEZ ZLE)) RNG /\ SX.aw_genuine (mkEZ ZLE) (SP.p_A A2E_defs.A2E)).
    { apply (a2e_wins RNG (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
               (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) LEN (ASI / 8) NN (TPA / 8) (ntp / 8)
               (SBA / 8) nsb (AOC / 8) (AIA / 8) 0 0 0 (BUF mod 8) ((LEN + BUF mod 8 + 64) / 8)
               ((4 * NN + 12 + 7) / 8) (nsb / 8)
               [u t0; u t1; u t2; u a2; u a3; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6]);
        first [ assumption | exact W_SP | exact W_SZ | exact W_B8 | exact HRI | exact HRIS ]. }
    destruct WIN as [FPL AWG].
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply evtF_weaken; [exact FPL|]. exact (a2e_run (mkEZ ZLE) m (seg_rom asegs) _ FR fc AWG (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) RG KN HMI HZ). }
    intros ms1 (X & E' & m1 & R1 & F1 & fc1 & HinX & -> & HZ1 & HF1 & HR1 & HK1 & _ & Hg & Hb & FR1 & WM1 & MI1 & STK1).
    cbn [SP.p_ex A2E_defs.A2E SP.PGCA SP.PGX] in HinX. destruct HinX as [<-|[]].
    destruct (xsm_regs ZLE E' R1 Hg (eq_sym Hb) HF1 HR1) as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->).
    destruct (xsm_kfacts (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
               (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) LEN (ASI / 8) NN (TPA / 8) (ntp / 8)
               (SBA / 8) nsb (AOC / 8) (AIA / 8) 0 0 0 (BUF mod 8) ((LEN + BUF mod 8 + 64) / 8)
               ((4 * NN + 12 + 7) / 8) (nsb / 8)
               [u t0; u t1; u t2; u a2; u a3; u a4; u a5; u a6; u a7; u t3; u t4; u t5; u t6] E' m1 Hg (eq_sym Hb) HK1 ltac:(lia))
      as (KA & KR & M_Z1 & M_SAVED1).
    set (spw := edenot E' (EVar 35)) in *. pose proof (u_rngA spw) as Rspw.
    rewrite <- E_SP in KR, M_Z1, M_SAVED1.
    assert (HSPX : 384 <= u sp - u spw <= 415) by (clear - KR Rsp Rspw Hsp47 Hlo1 Hlo2'; Z.div_mod_to_equations; lia).
    clear KR.
    (* [comment removed for export] *)
    pose proof (a2e_munch ZLE m m1 (u sp) ltac:(unfold ZLE; cbn [nth ZL_t0e app]; exact E_SP) ltac:(lia) FR1) as MU1.
    assert (PRES1 : aheap_pres CI LB (u sp) m m1).
    { eapply (aheap_pres_stack_writes AI CI L RNG st LB m [(u sp - 384, u sp)] m m1 (u sp) lo AH); [ | | exact MU1 | exact WM1 | | lia].
      - intros b Hb'. exact (AI_block_bounds AI _ _ _ _ _ _ AH Hb').
      - intros iv Hiv. exact (AI_aci_img AI iv Hiv).
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]; lia. }
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH | exact MU1 | exact WM1 |]. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. left; left. lia. }
    assert (STKm1 : stk asegs m1 lo (u sp)) by (apply STK1; exact HSTK).
    destruct (stk_split asegs m1 lo (u spw) (u sp) STKm1 ltac:(lia)) as [STK1a _].
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (nth 2 ZLE 0)) with gp by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 3 ZLE 0)) with tp by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (16 * nth 1 ZLE 0)) with sp by (unfold ZLE; cbn [nth ZL_t0e app]; rewrite <- E_SP; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 7 ZLE 0)) with s3 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 8 ZLE 0)) with s4 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (8 * nth 16 ZLE 0)) with (Z_to_bv 64 THIS) by (unfold ZLE; cbn [nth ZL_t0e app]; f_equal; exact E_T8).
    replace (Z_to_bv 64 (nth 10 ZLE 0)) with s6 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (8 * nth 17 ZLE 0)) with (Z_to_bv 64 DOC) by (unfold ZLE; cbn [nth ZL_t0e app]; f_equal; exact E_DOC8).
    replace (Z_to_bv 64 (nth 12 ZLE 0)) with s8 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 13 ZLE 0)) with s9 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 14 ZLE 0)) with s10 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    replace (Z_to_bv 64 (nth 15 ZLE 0)) with s11 by (unfold ZLE; cbn [nth ZL_t0e app]; symmetry; apply Z_to_bv_bv_unsigned).
    change (Z_to_bv 64 (ST.t_pc A2E_defs.XSM)) with (Z_to_bv 64 ASTKMALLOC5).
    eapply evtF_cut.
    { apply (SM5 L RNG (Z_to_bv 64 0x99fd4) spw gp tp x5 x6 x7 sp spw (Z_to_bv 64 1312) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 SH) s3 s4
               (Z_to_bv 64 THIS) s6 (Z_to_bv 64 DOC) s8 s9 s10 s11 x28 x29 x30 x31 F1 fc1 m1 st LB lo AH1 NO5 MI1 STK1a Hlo1
               ltac:(unfold SM5_STACK; lia) ltac:(lia) HTP HRS HRI HRFS). }
    intros ms2 (F & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & j0 & j1 & j2 & junk
                & -> & MI2 & STK2 & PRES2 & AH2 & HFm & HFb & HFt & HFc & HFs & HFr & HFsr & _ & HSHF).
    apply evtF_done.
    (* [comment removed for export] *)
    assert (Hbuf1 : bytes_at asegs m1 BUF (s1buf d)).
    { eapply aheap_pres_bytes_at; [exact PRES1 | exact Hbuf | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Icp); cbn [ab_addr ab_size];
        rewrite ?s1buf_lenA; unfold LEN in *; clear - Hb1 Hb2; lia]. }
    assert (HO8_1 : rw_cells asegs m1 (THIS + 8) [C4 (Z_to_bv 64 NN)])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HO8 | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Ith); cbn; clear - Hnim; lia]).
    assert (HO16_1 : rw_cells asegs m1 (THIS + 16) [C8 (Z_to_bv 64 ASI)])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HO16 | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Ith); cbn; clear - Hnim; lia]).
    assert (HO24_1 : rw_cells asegs m1 (THIS + 24) [C4 x24])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HO24 | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Ith); cbn; clear - Hnim; lia]).
    assert (HO40_1 : rw_cells asegs m1 (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HO40 | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Ith); cbn; clear - Hnim; lia]).
    assert (HO56_1 : rw_cells asegs m1 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 x88])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HO56 | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Ith); cbn; clear - Hnim; lia]).
    assert (HDOC1 : rw_cells asegs m1 DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)])
      by (eapply aheap_pres_rw_cells; [exact PRES1 | exact HDOC | eapply (PA2_sm5.acr_fake CI LB (u sp) _ _ _ _ _ Ifk); cbn; clear - Hfk1 Hfk2; lia]).
    assert (S_DOC1 : forall i, 0 <= i < 2 -> m1 (Z_to_bv 64 (SH + DOC / 8 + i)) = Some (Z_to_bv 8 0)).
    { assert (HD0 : 0x665000 <= DOC /\ DOC + 16 <= 0x7FFFFF800000) by (clear - Hfk1 Hfk2 Hf0 Hf1; atop_facts; lia).
      assert (ESH : Z.shiftr DOC 3 = DOC / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite ESH in HDSH.
      apply (PA2_sm5.shadow_pres CI LB (u sp) m m1 (DOC / 8) 2 PRES1 ltac:(clear - HD0; Z.div_mod_to_equations; lia)
               ltac:(clear - HD0; Z.div_mod_to_equations; lia)).
      - intros i Hi. right; right. exists cls, FA, FN. split; [exact Ifk | clear - Hda Hfk1 Hfk2 Hi; Z.div_mod_to_equations; lia].
      - intros i Hi. pose proof (shadow_cells2 m (DOC / 8 + 2147450880) ltac:(clear - HD0; Z.div_mod_to_equations; lia)
                                   ltac:(clear - HD0; Z.div_mod_to_equations; lia) HDSH i Hi) as HS0.
        replace (SH + DOC / 8 + i) with (DOC / 8 + 2147450880 + i) by ring. exact HS0. }
    assert (HFM1 : rw_cells asegs m1 AFMIN [C4 (Z_to_bv 64 8388608)]).
    { destruct (client_img_x m HCIMG) as (_ & X & _). eapply aheap_pres_rw_cells; [exact PRES1 | exact X |].
      eapply (PA2_sm5.acr_img CI LB (u sp) (0x10b978, 0x10b97c)); [apply HCI; cbn; tauto | cbn; unfold AFMIN; clear; lia | cbn; unfold AFMIN; clear; lia]. }
    assert (HFMCI : exists iv, In iv CI /\ fst iv <= AFMIN /\ AFMIN + 4 <= snd iv).
    { exists (0x10b978, 0x10b97c). split; [apply HCI; cbn; tauto | cbn; unfold AFMIN; clear; lia]. }
    assert (S_STK1 : forall i, 0 <= i < 1076 -> m1 (Z_to_bv 64 (SH + 2 * (u sp / 16) - 1076 + i)) = Some (Z_to_bv 8 0)).
    { intros i Hi. replace (SH + 2 * (u sp / 16) - 1076 + i) with (SH + (2 * (u sp / 16) - 1076) + i) by ring.
      apply (PA2_sm5.shadow_pres CI LB (u sp) m m1 (2 * (u sp / 16) - 1076) 1076 PRES1 ltac:(clear - E_SP Hlo1 Hlo2'; lia)
               ltac:(clear - E_SP Hsp47; lia)); [| | clear - Hi; lia].
      - intros i' Hi'. left. clear - E_SP Hlo1 Hlo2' Hsp47 Hi'. lia.
      - intros i' Hi'. destruct HCL as [(U & _) _].
        eapply (clean_shadow m (r_lo rstk) (r_hi rstk) (2 * (u sp / 16) - 1076) 1076 U); clear - E_SP HCL1 HCL2 Hlo2' Hi'; lia. }
    assert (HIMG1 : img_sh m1).
    { destruct (client_img_x m HCIMG) as (_ & _ & _ & _ & HI). exact (img_sh_pres AI LB (u sp) m m1 HCI HI PRES1). }
    assert (HFL : rw_cells asegs m2 (F + 2040) [C8 (Z_to_bv 64 (fflag L 5 F))]).
    { change [C8 j0; C8 j1; C8 j2; CB 2016 junk; C8 (Z_to_bv 64 (fflag L 5 F))]
        with ([C8 j0; C8 j1; C8 j2; CB 2016 junk] ++ [C8 (Z_to_bv 64 (fflag L 5 F))]) in HFc.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in HFc. exact (proj2 HFc). }
    assert (PRES12 : aheap_pres CI LB (u sp) m m2)
      by (eapply aheap_pres_trans; [exact PRES1 | eapply aheap_pres_weaken; [exact PRES2 | lia | tauto]]).
    pose proof (u_rngA spw) as Rspw'. assert (HFR : 0 <= F < M64) by (unfold ablk, AIMG_HI, KLS in HFb; clear - HFb HFt; atop_facts; lia).
    exists F, (u spw), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F1, fc1, m2. cbv zeta.
    split; [rewrite (ret_pc_even 0x99fd4) by (lia || reflexivity); rewrite !Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HZ1|]. split; [exact MI2|].
    split; [unfold ZL2; apply a2t0_regs; lia|].
    split; [unfold ZL2; eapply (PA2_sm5.a2t0_kn AI fflag L RNG st LB m1 m2) with (lo := lo) (cls := cls) (FA := FA) (FN := FN); eassumption|].
    split.
    { (* [comment removed for export] *)
      pose proof (scan_S1OUT d idx Hscan) as S1.
      assert (HBUF2 : bytes_at asegs m2 BUF (s1buf d)).
      { eapply aheap_pres_bytes_at; [exact PRES12 | exact Hbuf | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Icp); cbn [ab_addr ab_size];
          rewrite ?s1buf_lenA; unfold LEN in *; clear - Hb1 Hb2; lia]. }
      assert (HIDX2 : rw_cells asegs m2 ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))]).
      { eapply aheap_pres_rw_cells; [exact PRES12 | exact HIDX | eapply (PA2_sm5.acr_blk CI LB (u sp) _ _ _ Isi);
          cbn [ab_addr ab_size cells_size csize]; unfold NN, zlength in Hnsi |- *; clear - Hnsi; lia]. }
      assert (BB : 0x665000 <= BUF /\ BUF + LEN + 64 <= 0x7FFFFF800000) by (clear - Hb1 Hb2 Hc0 Hc1; atop_facts; lia).
      assert (IB : 0x665000 <= ASI /\ ASI + 4 * NN + 16 <= 0x7FFFFF800000) by (clear - Hi0 Hi1 Hnsi; atop_facts; lia).
      unfold SG.gholds. cbn [ST.t_ghost A2_defs.T0]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        cbv [A2_defs.vBUF A2_defs.vB8 A2_defs.vBO A2_defs.vLEN A2_defs.vIDX A2_defs.vI8 A2_defs.vN A2_defs.V A2_defs.mul A2_defs.add];
        cbn [ST.g_id ST.g_args map S2G2.gp2]; rewrite !u_zden by reflexivity; unfold ZL2; cbn [zden nth PA2_t0c.ZL_t0'' app].
      - replace (8 * (BUF / 8) + BUF mod 8) with BUF by (clear; Z.div_mod_to_equations; lia).
        rewrite !Z.mod_small by (clear - BB Sn; lia).
        split; [reflexivity|]. split; [clear - BB; lia|]. split; [exact Hd|]. rewrite bufbytes_eqA.
        apply mbytes_of_bytes_at_heapA; [exact HBUF2 | clear - BB; lia | rewrite s1buf_lenA; fold LEN; clear - BB; lia].
      - replace (8 * (ASI / 8)) with ASI by exact E_I8. rewrite !Z.mod_small by (clear - IB Sn; lia).
        assert (ZL3 : zlength (idx ++ [zlength d; zlength d; 0]) = NN + 3) by (unfold NN; rewrite zlength_app; reflexivity).
        rewrite ZL3. replace (NN + 3 - 3) with NN by ring.
        split; [reflexivity|]. split; [exact S1|]. split; [clear - IB; lia|]. rewrite u32bytes_eqA.
        destruct (cb_bytesA m2 _ _ _ HIDX2) as [BI LI].
        apply mbytes_of_bytes_at_heapA; [exact BI | clear - IB; lia | rewrite LI; unfold NN, zlength in IB; clear - IB; lia]. }
    assert (WIN2 : fp_le (SX.fp_of (SP.p_A A2_defs.A2) (mkEZ (ZL2 F (u spw) [u t0'; u t1'; u t2'; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7';
                     u s3; u s4; u s6; u s8; u s9; u s10; u s11; u t3'; u t4'; u t5'; u t6']))) RNG
                   /\ SX.aw_genuine (mkEZ (ZL2 F (u spw) [u t0'; u t1'; u t2'; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7';
                     u s3; u s4; u s6; u s8; u s9; u s10; u s11; u t3'; u t4'; u t5'; u t6'])) (SP.p_A A2_defs.A2)).
    { (* [comment removed for export] *)
      assert (R_F : rng RNG (2048 * (F / 2048)) 2048) by (replace (2048 * (F / 2048)) with F by (clear - HFm; Z.div_mod_to_equations; lia); exact HFr).
      assert (R_FS : rng RNG (256 * (F / 2048) + SH) 256).
      { rewrite shad_div in HFsr. unfold ASHOFF in HFsr. eapply rng_sub'; [exact HFsr | clear - HFm; Z.div_mod_to_equations; lia]. }
      unfold ZL2, PA2_t0c.ZL_t0''.
      apply (a2_wins RNG (u ra) (u sp / 16) (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9)
               (u s10) (u s11) (THIS / 8) (DOC / 8) (BUF / 8) LEN (ASI / 8) NN (TPA / 8) (ntp / 8)
               (SBA / 8) nsb (AOC / 8) (AIA / 8) (F / 2048) ((u sp - 384 - u spw) / 16) (fflag L 5 F) (BUF mod 8)
               ((LEN + BUF mod 8 + 64) / 8) ((4 * NN + 12 + 7) / 8) (nsb / 8));
        first [ assumption | exact W_SP | exact W_SZ | exact HRI | exact HRIS | (clear - W_B8 HFb Hf0 HFt; unfold ablk, AIMG_HI, KLS in HFb; Z.div_mod_to_equations; lia) ]. }
    split; [exact (proj1 WIN2)|]. split; [exact (proj2 WIN2)|].
    split; [exact KA|]. split; [exact HSPX|].
    split; [exact AH2|]. split; [exact PRES12|].
    split.
    { apply (stk_merge asegs m2 lo (u spw) (u sp)); [exact STK2 | | clear - HSPX Hlo2' Hlo1; lia].
      destruct (stk_split asegs m1 lo (u spw) (u sp) STKm1 ltac:(clear - HSPX Hlo2' Hlo1; lia)) as [_ SU].
      eapply aheap_pres_stk; [exact PRES2 | exact SU | clear; lia | clear - Hsp47; lia]. }
    do 5 (split; [assumption|]). split; [exact HFL|]. exact HSHF.
  Qed.
End H.
End CANSEC.
