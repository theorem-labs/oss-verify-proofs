(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Mem ITree Nodes Decode ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow SysStepF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes ARep AModelFacts F_memset F_apoison F_m2s F_annot F_annot_sg APoisonR_iface F_annot_grow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit ShadowTac AU_steptac AU_kit AU_h_kit AAnnot_iface AM_kitB AM_kitC AM_annotw BM_ctx.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.
Definition bxn (P : Prop) : Prop := P.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxn P) in H end.

Section CANSEC1. Context {rc : runConstT}.
Definition ACATN : Z := 0xb29ec.
Definition ACATN_GRET : Z := 0xb2a48.      (* [comment removed for export] *)
Definition ACATN_LOOP : Z := 0xb2a58.
Definition CATN_STACK : Z := 48 + ANNOTW_STACK.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ckb_b2ae0 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb2a6c) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb2a68) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep. if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition catn_W (SP V A n G : Z) : list (Z * Z) := [(SP - CATN_STACK, SP); (V + 8, V + 16); (shad A, shad A + G); (A, A + n)].

Definition catn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (V A n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (catn_W (bv_unsigned sp) V A n (shlen (rup8 n))) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 (A + n))]
    /\ rw_cells bsegs m' (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' (shad A) [CB (Z.to_nat (shlen (rup8 n))) (block_shadow_bytes n)]
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Section CATN.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : amem) (V A n lo ULO UHI G : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - 2784.
  Hypothesis SPH : SP + 16 <= 2^47.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis V8 : V mod 8 = 0.
  Hypothesis VBLK : ablk V (V + 24).
  Hypothesis BR : ablock_range A n.
  Hypothesis NR : 0 < n <= 2^29 - 2^16.
  Hypothesis VDJ : V + 24 <= A \/ A + rup8 n <= V.
  Hypothesis EG : shlen (rup8 n) = G.
  Hypothesis PC : poison_cells m.
  Hypothesis AC : annot_cells m.
  Hypothesis USH : unpoisoned m ULO UHI.
  Hypothesis U0 : ATOP <= ULO.
  Hypothesis U1 : ULO <= SP - 48.
  Hypothesis U2 : SP <= UHI.
  Hypothesis U3 : UHI <= 2^47.
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (SP - lo).
  Hypothesis RV : rng RNG V 24.
  Hypothesis RVS : rng RNG (shad V) 3.
  Hypothesis RBA : rng RNG A n.
  Hypothesis RSH : rng RNG (shad A) G.
  Hypothesis RTS : rng RNG (shad (SP - 48)) 3.

  Notation W4 := [(SP - 2784, SP); (V + 8, V + 16); (shad A, shad A + G); (A, A + n)].

  (* [comment removed for export] *)
  Lemma catn_facts : 0 <= lo /\ SP < 2^47 /\ 0x6d4000 <= V /\ V + 24 <= ATOP /\ (V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V)
    /\ 0x6d4000 <= A /\ A + n <= ATOP /\ A mod 16 = 0 /\ (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A)
    /\ 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000 /\ 0x7fff8000 <= shad A /\ shad A + G <= 0x10007fff8000
    /\ shad V = Z.shiftr V 3 + 2147450880 /\ Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1
    /\ 0x7fff7f800000 <= ATOP /\ ATOP <= 0x7fffff800000 /\ (shad V + 3 <= shad A \/ shad A + G <= shad V)
    /\ G = granules n /\ n / 8 <= G /\ 8 * G <= n + 7 /\ (A + n <= shad A \/ shad A + G <= A) /\ n <= rup8 n <= n + 7 /\ n <= 8 * G.
  Proof.
    pose proof atop_range as ATR. pose proof (bv_unsigned_in_range 64 sp) as RSP0.
    pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
    destruct BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & _ & BL3 & _). unfold AIMG_HI in BL1.
    assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
    assert (ANS : A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A) by (unfold ablk, AIMG_HI, KLS in BR1; clear - BR1 NR; lia).
    assert (AL : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
    assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
    assert (GG : G = granules n /\ n / 8 <= G /\ 8 * G <= n + 7 /\ n <= 8 * G)
      by (rewrite <- EG, <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; repeat split; clear - NR; Z.div_mod_to_equations; lia).
    destruct GG as (GG1 & GG2 & GG3 & GG4).
    repeat split; try exact GG1; try (unfold shad, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; clear - ATR RSP0 VLO VHI BL1 BL3 BR4 VNS ANS LOA LOS SPH V8 VDJ AL R8B NR GG2 GG3 GG4; Z.div_mod_to_equations; lia).
  Qed.

  (* [comment removed for export] *)
  Definition FRAME (m1 : amem) (pv : Z) : Prop :=
    rw_cells bsegs m1 (SP + -48) [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 (n + A)); C8 s1; C8 s0; C8 ra].
  Definition VEC (m1 : amem) : Prop := rw_cells bsegs m1 V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n))].
  Definition VSH (m1 : amem) : Prop := rw_cells bsegs m1 (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Definition FULL (m1 : amem) : Prop := rw_cells bsegs m1 (shad A) [CB (Z.to_nat G) (block_shadow_bytes n)].
  Definition INV (m1 : amem) (i pv : Z) : Prop :=
    FRAME m1 pv /\ stk bsegs m1 lo (SP + -48) /\ VEC m1 /\ VSH m1 /\ FULL m1
    /\ bytes_at bsegs m1 A (repeat (Z_to_bv 8 0) (Z.to_nat i)) /\ unpoisoned m1 A (A + n) /\ wr_at bsegs m1 A n
    /\ munch W4 m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rt_got m1 /\ rt_shbase m1.

  Notation LST pc mm va x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 0xb2a48) (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (n + A))
             (Z_to_bv 64 va) (Z_to_bv 64 va) (Z_to_bv 64 (-1)) xa3 xa4 xa5 xa6 xa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma INV_store : forall m1 i, INV m1 i (A + i) -> 0 <= i < n ->
    INV (write_to_mem m1 (wa (A + i)) [Z_to_bv 8 0]) (i + 1) (A + i).
  Proof.
    intros m1 i (FR1 & ST1 & VEC1 & VSH1 & FULL1 & PRE1 & UNP1 & WT1 & MU1 & WM1 & MI1 & GOT1 & SHB1) Hi.
    pose proof catn_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & SV1 & SV2 & SA1 & SA2 & _ & _ & ATR & ATR2 & SHDJ & GG1 & GG2 & GG3 & ADJ & R8B & GG4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    assert (SOK : store_ok bsegs m1 (wa (A + i)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    set (m2 := write_to_mem m1 (wa (A + i)) _).
    assert (MU2 : munch [(A + i, A + i + 1)] m1 m2).
    { apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn [inside length]. left. cbn. lia. }
    assert (WM2 : wmono bsegs m1 m2) by (apply wmono_write; apply wmono_refl).
    assert (XC : forall B cs, (B + Z.of_nat (cells_size cs) <= A + i \/ A + i + 1 <= B) -> rw_cells bsegs m1 B cs -> rw_cells bsegs m2 B cs).
    { intros B cs D H. eapply rw_cells_transport; [exact H| exact MU2| exact WM2|]. cbn [disjoint_from]. split; [exact D| exact I]. }
    split. { apply XC; [cbn [cells_size csize Nat.add]; clear - LOA LOS AH1 ATR Hi; lia| exact FR1]. }
    split. { apply stk_write; [exact ST1| lia| cbn; lia]. }
    split. { apply XC; [cbn [cells_size csize Nat.add]; clear - VDJ Hi R8B; lia| exact VEC1]. }
    split. { apply XC; [cbn [cells_size csize Nat.add]; clear - SV1 SV2 ANS Hi; lia| exact VSH1]. }
    split. { apply XC; [cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - ADJ Hi; lia| exact FULL1]. }
    split. { replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia. rewrite repeat_app. cbn [repeat].
             apply bytes_at_app_join.
             + eapply bytes_at_write_other; [exact PRE1| lia| cbn; lia| rewrite repeat_length; left; lia].
             + rewrite repeat_length. replace (A + Z.of_nat (Z.to_nat i)) with (A + i) by lia. apply bytes_at_write_same; [lia| cbn; lia]. }
    split. { eapply unpoisoned_munch; [exact UNP1| exact MU2|]. cbn [disjoint_from]. split; [| exact I]. rewrite !shad_div. unfold ASHOFF. clear - ANS AL1 AH1 ATR2 Hi; Z.div_mod_to_equations; lia. }
    split. { apply wr_at_write. exact WT1. }
    split. { apply munch_write; [exact MU1| lia| cbn; lia|]. cbn [inside length]. right. right. right. left. cbn. lia. }
    split. { apply wmono_write. exact WM1. }
    split. { apply mem_inv_store; [exact MI1| exact SOK]. }
    split. { apply XC; [cbn [cells_size csize Nat.add]; clear - AL1 ANS Hi; lia| exact GOT1]. }
    apply XC; [cbn [cells_size csize Nat.add]; clear - AL1 ANS Hi; lia| exact SHB1].
  Qed.

  (* [comment removed for export] *)
  Lemma catn_exit : forall m1 va (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    INV m1 n va -> va = n + A ->
    evtF bsegs RNG (catn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V A n lo m) (LST 0xb2a94 m1 va x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros m1 va x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 (FR1 & ST1 & VEC1 & VSH1 & FULL1 & PRE1 & UNP1 & WT1 & MU1 & WM1 & MI1 & GOT1 & SHB1) ->.
    pose proof catn_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & SV1 & SV2 & SA1 & SA2 & SHV & SHV8 & ATR & ATR2 & SHDJ & GG1 & GG2 & GG3 & ADJ & R8B & GG4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    unfold FRAME, VEC, VSH, FULL in *.
    (* [comment removed for export] *)
    assert (BLK1 : rw_cells bsegs m1 A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]).
    { split; [split|]; [cbn [cells_wf cell_wf]; rewrite repeat_length; split; [reflexivity| exact I]
                         | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact PRE1
                         | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact WT1]. }
    clear PRE1 WT1 UNP1.
    (* [comment removed for export] *)
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W4) by (repeat constructor; cbn; unfold AIMG_HI; clear - SA1 LOA LOS ATR VLO AL1; lia).
    pose proof (poison_cells_frame _ _ _ PC MU1 WM1 HWI) as PC1. pose proof (annot_cells_frame _ _ _ AC MU1 WM1 HWI) as AC1.
    assert (USH1 : unpoisoned m1 ULO UHI).
    { eapply unpoisoned_munch; [exact USH| exact MU1|]. cbn [disjoint_from]. pose proof USH as X; unfold unpoisoned in X; destruct X as (X0 & X1 & _).
      pose proof ATOP_al16 as ATA. rewrite !shad_div. unfold ASHOFF. clear - X0 X1 U0 U1 U2 U3 VNS VLO ANS AL1 AH1 A16 ATA GG2 GG3 LOA LOS ATR NR. Z.div_mod_to_equations. lia. }
    rw_split FR1 3%nat TX1 FRB.
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evtF_cut; [ eapply (ctx_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -48) V (n + A) lo ULO UHI)
                       | cbv beta; unfold ctx_dtor_post; rewrite ?unsigned_lit by (clear - LOS LOA LO0 SP47 ATR; lia); post_call bsegs mm ]
    end;
      rewrite ?unsigned_lit by (clear - LOS LOA LO0 SP47 ATR; lia);
      first [ exact MI1 | exact ST1 | exact TX1 | exact USH1 | exact VEC1 | exact VSH1 | exact V8 | exact VBLK | exact PC1 | exact AC1 | exact GOT1 | exact SHB1 | exact RIMG | exact RV | exact RVS
            | reflexivity
            | (clear - LOA ATR; lia) | (clear - LOS; lia) | (clear - SPH; lia) | (clear - SP16; Z.div_mod_to_equations; lia)
            | (clear - U1; lia) | (clear - U2; lia) | exact U3
            | (clear - AH1 AL1 NR ATR; lia)
            | (eapply rng_sub'; [exact RSTK| clear - LOS LO0; lia])
            | (replace (SP + -48) with (SP - 48) by lia; exact RTS)
            | idtac ].
    (* [comment removed for export] *)
    zstep. zstep. zstep.                    (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    match goal with TXx : rw_cells bsegs ?mm (SP + -48) [_; _; _], FRBx : rw_cells bsegs ?mm' (SP + -24) _ |- _ => rw_join TXx FRBx FRJ end.
    lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FRJ H (bv_unsigned sp) end.
    zstep.                                  (* [comment removed for export] *)
    apply evtF_done. unfold catn_post, catn_W, CATN_STACK, ANNOTW_STACK. rewrite EG.
    replace (n + A) with (A + n) in * by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
      lazymatch goal with MUx : munch _ m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm, STx : stk bsegs mm lo SP,
                          VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _, FULLx : rw_cells bsegs mm (shad A) _, BLKx : rw_cells bsegs mm A _ |- _ =>
      do 15 eexists; exists mm; split; [reflexivity|];
      split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|];
      split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULLx| exact BLKx]
      end end.
  Qed.

  (* [comment removed for export] *)
  Lemma catn_loop : forall fuel i m1 va (x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 : word),
    Z.of_nat fuel > n - i -> 0 <= i < n -> va = A + i -> INV m1 i va ->
    evtF bsegs RNG (catn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V A n lo m) (LST 0xb2a58 m1 va x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    induction fuel as [|fuel IH]; intros i m1 va x5 x6 x7 xa3 xa4 xa5 xa6 xa7 x28 x29 x30 x31 FUEL Hi -> INV1; [lia|].
    pose proof INV1 as (FR1 & ST1 & VEC1 & VSH1 & FULL1 & PRE1 & UNP1 & WT1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
    pose proof catn_facts as (LO0 & SP47 & VLO & VHI & VNS & AL1 & AH1 & A16 & ANS & SV1 & SV2 & SA1 & SA2 & _ & _ & ATR & ATR2 & SHDJ & GG1 & GG2 & GG3 & ADJ & R8B & GG4).
    pose proof (bv_unsigned_in_range 64 sp) as RSP0. unfold bv_modulus in RSP0. cbn in RSP0.
    unfold FRAME, VEC, VSH, FULL in FR1, VEC1, VSH1, FULL1.
    assert (SOK : store_ok bsegs m1 (wa (A + i)) 1 = true) by (eapply wr_at_store_ok; [exact WT1| lia| lia]).
    assert (ACCd : rng RNG (Z.shiftr (A + i) 3 + 2147450880) 1)
      by (eapply rng_sub'; [exact RSH| rewrite Z.shiftr_div_pow2, shad_div by lia; unfold ASHOFF; clear - Hi A16 AL1 GG4; Z.div_mod_to_equations; lia]).
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AL1 Hi; lia| clear K]).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.                           (* [comment removed for export] *)
    destruct (unpoisoned_check_rd bsegs _ A (A + n) (A + i) 1 UNP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b1 & RDb1 & CKb1).
    unfold shad, ASHOFF in RDb1. replace (2147450880 + Z.shiftr (A + i) 3) with (Z.shiftr (A + i) 3 + 2147450880) in RDb1 by lia.
    zstep. rewrite sxb_sval.                (* [comment removed for export] *)
    eapply evtF_cut;
    [ eapply ckb_b2ae0 with (b := b1); [ clear - AL1 AH1 ATR Hi; lia | exact CKb1 ]
    | cbv beta; let ms' := fresh "ms'" in let PO := fresh "PO" in intros ms' PO; destruct_exs PO; subst ms' ].
    clear RDb1 CKb1.
    (* [comment removed for export] *)
    box PRE1. box UNP1.
    zstep.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => set (m2 := mx) in * end.
    assert (INV2 : INV m2 (i + 1) (A + i)) by (exact (INV_store m1 i INV1 Hi)).
    clearbody m2. clear SOK FR1 ST1 VEC1 VSH1 FULL1 PRE1 UNP1 WT1 MU1 WM1 MI1 GOT1 SHB1 INV1.
    pose proof INV2 as (FR2 & ST2 & VEC2 & VSH2 & FULL2 & PRE2 & UNP2 & WT2 & MU2 & WM2 & MI2 & GOT2 & SHB2). clear INV2.
    unfold FRAME, VEC, VSH, FULL in FR2, VEC2, VSH2, FULL2.
    zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K AH1 ATR Hi; lia| clear K]).   (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    box PRE2. box UNP2.
    pose proof (munch_refl [(SP + -48, SP)] m2) as MUX.
    zstep.                                  (* [comment removed for export] *)
    zstep.                                  (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with MUXx : munch [(SP + -48, SP)] m2 mm |- _ =>
      assert (PRE3 : bytes_at bsegs mm A (repeat (Z_to_bv 8 0) (Z.to_nat (i + 1))))
        by (unfold bxn in PRE2; eapply bytes_at_transport; [exact PRE2| exact MUXx| cbn [disjoint_from]; rewrite repeat_length; clear - AH1 LOA LOS ATR Hi; lia]);
      assert (UNP3 : unpoisoned mm A (A + n))
        by (unfold bxn in UNP2; eapply unpoisoned_munch; [exact UNP2| exact MUXx| cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; clear - AH1 AL1 ANS LOA LOS ATR NR; Z.div_mod_to_equations; lia]);
      clear PRE2 UNP2 MUXx
      end end.
    zstep; (let K := fresh "Kn" in if_cases K; zify_cond K).
    - (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with FRx : rw_cells bsegs mm (SP + -48) _, STx : stk bsegs mm lo _, VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _,
                            FULLx : rw_cells bsegs mm (shad A) _, WTx : wr_at bsegs mm A n, MUx : munch _ m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm,
                            GOTx : rt_got mm, SHBx : rt_shbase mm |- _ =>
        assert (INV3 : INV mm (i + 1) (A + i + 1))
          by (split; [exact FRx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULLx|]; split; [exact PRE3|];
              split; [exact UNP3|]; split; [exact WTx|]; split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact GOTx| exact SHBx])
        end end.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (NEXT : forall va (y5 y6 y7 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word), va = A + (i + 1) ->
                  evtF bsegs RNG (catn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V A n lo m) (LST 0xb2a58 mm va y5 y6 y7 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31))
          by (intros va y5 y6 y7 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 ->; apply (IH (i + 1)); [lia| rewrite ?unsigned_lit in Kn by lia; lia| reflexivity| replace (A + (i + 1)) with (A + i + 1) by lia; exact INV3])
      end.
      apply NEXT; lia.
    - (* [comment removed for export] *)
      zstep.                                (* [comment removed for export] *)
      assert (En : i + 1 = n) by (rewrite ?unsigned_lit in Kn by lia; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with FRx : rw_cells bsegs mm (SP + -48) _, STx : stk bsegs mm lo _, VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _,
                            FULLx : rw_cells bsegs mm (shad A) _, WTx : wr_at bsegs mm A n, MUx : munch _ m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm,
                            GOTx : rt_got mm, SHBx : rt_shbase mm |- _ =>
        assert (INV3 : INV mm n (A + i + 1))
          by (split; [exact FRx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULLx|]; split; [rewrite <- En; exact PRE3|];
              split; [exact UNP3|]; split; [exact WTx|]; split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact GOTx| exact SHBx])
        end end.
      apply (catn_exit _ (A + i + 1)); [exact INV3| lia].
  Qed.
End CATN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma catn_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (V A n lo ULO UHI : Z) (jk : list byte) (st : astate) (p : AsanCtrl.aptr) (ch : achunk),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - CATN_STACK -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  poison_cells m -> annot_cells m -> artcells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 n ->
  rw_cells bsegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + n))] ->
  rw_cells bsegs m (shad V) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  V mod 8 = 0 -> ablk V (V + 24) -> (V + 24 <= A \/ A + rup8 n <= V) ->
  ablock_range A n -> 0 < n <= AREQMAX ->
  (a_live st) !! p = Some ch -> chunk_size ch = n -> (is_primary n = false -> A = chunk_user_beg ch) ->
  match ch with CPrim _ _ => is_primary n = true | CSec _ _ _ => is_primary n = false end ->
  rw_cells bsegs m (shad A) [CB (Z.to_nat (shlen (rup8 n))) (repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 n))))] ->
  rw_cells bsegs m A [CB (Z.to_nat n) jk] ->
  (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
       /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO))) ->
  unpoisoned m ULO UHI -> ATOP <= ULO -> ULO <= bv_unsigned sp - 48 -> bv_unsigned sp <= UHI -> UHI <= 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad A) (shlen (rup8 n)) -> rng RNG V 24 -> rng RNG (shad V) 3 ->
  rng RNG A n -> rng RNG (shad (bv_unsigned sp - 48)) 3 ->
  evtF bsegs RNG (catn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc V A n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACATN) fc None m (seg_rom bsegs)).
Proof.
  intros until ch. intros MI ST LOA LOS SPH SP16 PC AC ART PRM RR GOT SHB -> -> VEC VSH V8 VBLK VDJ BR NR LIVE CSZ UBEG KIND FULL BLK ARENA USH U0 U1 U2 U3 RIMG RSTK RSH RV RVS RBA RTS.
  unfold ACATN, CATN_STACK, ANNOTW_STACK in *. pose proof atop_range as ATR. unfold AREQMAX in NR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ablk_lin _ _ VBLK) as (VLO & _ & VHI & _). unfold AIMG_HI in VLO.
  assert (VNS : V + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= V) by (unfold ablk, AIMG_HI, KLS in VBLK; clear - VBLK; lia).
  pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
  assert (AL : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (R8B : n <= rup8 n <= n + 7) by (unfold rup8, rdn8; clear - NR; Z.div_mod_to_equations; lia).
  assert (AR : exists G, shlen (rup8 n) = G /\ G = granules n /\ n / 8 <= G /\ 0 <= n / 8 /\ 8 * G <= n + 7 /\ G <= n / 8 + 1)
    by (exists (shlen (rup8 n)); rewrite <- granules_rup8 by lia; unfold shlen, rup8, rdn8; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8;
        repeat split; clear - NR; Z.div_mod_to_equations; lia).
  destruct AR as (G & EG & EGG & GNG & N80 & G8 & GN1).
  rewrite EG in FULL, RSH.
  assert (SHV : shad V = Z.shiftr V 3 + 2147450880) by (unfold shad, ASHOFF; lia).
  assert (SHV8 : Z.shiftr (V + 8) 3 + 2147450880 = shad V + 1) by (rewrite SHV, !Z.shiftr_div_pow2 by lia; clear - V8; Z.div_mod_to_equations; lia).
  assert (SHVB : 0x7fff8000 <= shad V /\ shad V + 3 <= 0x10007fff8000) by (rewrite SHV, Z.shiftr_div_pow2 by lia; clear - VLO VHI ATR; Z.div_mod_to_equations; lia).
  assert (SHBB : 0x7fff8000 <= shad A /\ shad A + G <= 0x10007fff8000)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - BL1 BL3 NR ATR G8 R8B; Z.div_mod_to_equations; lia).
  assert (SHDJ : shad V + 3 <= shad A \/ shad A + G <= shad V)
    by (rewrite SHV; unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; clear - VDJ V8 AL G8 R8B NR GNG N80; Z.div_mod_to_equations; lia).
  pose proof PC as PC'. destruct PC' as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7). pose proof AC as AC'. destruct AC' as (AC1 & AC2 & AC3).
  assert (ACC1 : rng RNG (Z.shiftr (V + 8) 3 + 2147450880) 1) by (rewrite SHV8; eapply rng_sub'; [exact RVS| lia]).
  box SHV; box SHV8.
  pose proof (munch_refl [(bv_unsigned sp - 2784, bv_unsigned sp); (V + 8, V + 16); (shad A, shad A + G); (A, A + n)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof (proj2 BLK) as WT. cbn [cells_size csize Nat.add] in WT. rewrite Nat.add_0_r, Z2Nat.id in WT by lia.
  clear BLK.
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
  zstep. zstep. zstep.            (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (sh3_read mm (shad V) 1 ltac:(lia) VSH) as HR1; unfold bxn in SHV8; rewrite <- SHV8 in HR1; box SHV8 end.
  zstep. zstep. zstep.            (* [comment removed for export] *)
  astep. astep.                   (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K BL1 BL4 NR; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.            (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; clear - K BL1 BL4 NR; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  zstep.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono bsegs m mm |- _ =>
    assert (HWI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 2784, bv_unsigned sp); (V + 8, V + 16); (shad A, shad A + G); (A, A + n)]);
    [ apply Forall_cons; [cbn; unfold AIMG_HI; clear - LOA LOS ATR; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; clear - VLO; lia|];
      apply Forall_cons; [cbn; unfold AIMG_HI; clear - SHBB; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; clear - BL1; lia| apply Forall_nil]
    | ];
    pose proof (poison_cells_frame _ _ _ PC MUx WMx HWI) as PC1q;
    pose proof (annot_cells_frame _ _ _ AC MUx WMx HWI) as AC1q;
    pose proof (artcells_frame _ _ _ ART MUx WMx HWI) as ART1;
    pose proof (premap_cells_frameA _ _ _ PRM MUx WMx HWI) as PRM1;
    pose proof (arelro_munchA _ _ _ RR MUx HWI) as RR1;
    assert (ARENA1 : exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
               /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs mm (shad RLO) (shlen (RHI - RLO)))
      by (destruct ARENA as (RLO & RHI & X1 & X2 & X3 & X4 & X5 & X6); exists RLO, RHI; repeat (split; [assumption|]); eapply wr_at_transport; [exact X6| exact WMx])
    end end.
  name_sp sp (-48)%Z.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evtF_cut;
    [ eapply (annotw_increase_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ V A n lo st p ch);
      first [ exact PC1q | exact AC1q | exact ART1 | exact PRM1 | exact RR1 | exact V8 | exact VBLK | exact VDJ | exact BR | exact LIVE | exact CSZ | exact UBEG | exact KIND
            | exact ARENA1 | exact RIMG | exact RV | exact RVS | reflexivity
            | (pose proof ART1 as (_ & Xg & _ & _ & Xs & _); first [exact Xg | exact Xs])
            | (rewrite Hsp; eassumption) | (rewrite EG; exact FULL) | eassumption
            | (rewrite Hsp; unfold ANNOTW_STACK; clear - LOS; lia) | (rewrite Hsp; clear - RSP LOS LOA SPH ATR; lia)
            | (unfold AREQMAX; clear - NR; lia)
            | (rewrite EG; exact RSH)
            | (rewrite Hsp; eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
            | lia | idtac ]
    | cbv beta; unfold annotw_grow_post, ANNOTW_STACK; rewrite ?EG; clear PC1q AC1q ART1 PRM1 RR1 ARENA1; post_call bsegs mm ]
    end.
  unname_sp.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with BODY : rw_cells bsegs mm (shad A) [CB _ (repeat _ _)], LAST : (n mod 8 <> 0 -> rw_cells bsegs mm _ [C1 _]) |- _ =>
    pose proof (bsb_cells_join mm (shad A) n ltac:(lia) BODY LAST) as FULL3; rewrite <- EGG in FULL3;
    assert (UNP3 : unpoisoned mm A (A + n))
      by (apply ablock_unpoisoned; [apply (ablock_shadow_of_cells mm A n ltac:(lia) ltac:(lia)); rewrite <- EGG; exact FULL3| exact AL| lia| lia| lia]);
    clear BODY LAST
    end end.
  zstep.                          (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K NR; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with FRx : rw_cells bsegs mm (bv_unsigned sp + -48) _, STx : stk bsegs mm lo _, VECx : rw_cells bsegs mm V _, VSHx : rw_cells bsegs mm (shad V) _,
                        WTx : wr_at bsegs mm A n, MUx : munch _ m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm, GOTx : rt_got mm, SHBx : rt_shbase mm |- _ =>
    eapply (catn_loop RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m V A n lo ULO UHI G
              LOA LOS SPH SP16 V8 VBLK BR NR VDJ EG PC AC USH U0 U1 U2 U3 RIMG RSTK RV RVS RBA RSH RTS (S (Z.to_nat n)) 0 mm A);
    [ clear - NR; lia | clear - NR; lia | clear; lia |];
    split; [exact FRx|]; split; [exact STx|]; split; [exact VECx|]; split; [exact VSHx|]; split; [exact FULL3|];
    split; [| split; [exact UNP3|]; split; [exact WTx|]; split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact GOTx| exact SHBx]];
    change (Z.to_nat 0) with 0%nat; cbn [repeat]; apply bytes_at_nil; clear - BL2 BL4 NR; lia
    end end.
Qed.
End CANSEC1.
