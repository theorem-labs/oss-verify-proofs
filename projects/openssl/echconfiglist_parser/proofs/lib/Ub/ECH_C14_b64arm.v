(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_B64 ECH_LibState ECH_LibStateMF ECH_LibFrame ECH_Rostr ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C3_stmt ECH_C3_phase ECH_C4_stmt ECH_C4_frame ECH_C4_frame2 ECH_C4_raise ECH_C4 ECH_C5_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_newmembuf ECH_C8_stmt ECH_C9_stmt ECH_C9_bionew ECH_C9_push ECH_C9_biofreeall ECH_C10_stmt ECH_C13_stmt ECH_C14_stmt ECH_KitSeg ECH_LibMid F_time ECH_C14_bio2buf ECH_C14_ladder ECH_C14_ladloop ECH_C14_tail ECH_C14_b2b ECH_C14_fcc ECH_C14_dec ECH_C14_decexts ECH_C14_flat_seg ECH_C14_fmt ECH_C14_flatten ECH_C14_readcfg ECH_C8_blockA ECH_C9_rdloop ECH_C9_bioread ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition FB_R1 : Z := 0x2b3124.   (* [comment removed for export] *)
Definition FB_R2 : Z := 0x2b3130.   (* [comment removed for export] *)
Definition FB_R3 : Z := 0x2b3138.   (* [comment removed for export] *)
Definition FB_R4 : Z := 0x2b314c.   (* [comment removed for export] *)
Definition FB_R5 : Z := 0x2b315c.   (* [comment removed for export] *)
Definition FB_R6 : Z := 0x2b3178.   (* [comment removed for export] *)
Definition FB_R7 : Z := 0x2b3194.   (* [comment removed for export] *)
Definition FB_631_R1 : Z := 0x2b3264. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bf_fresh2 (R : b64frep) (nx : Z) : b64frep := mkBF 256 0 0 nx 0 (bf_ctx R) (bf_enc R) (bf_id R) (bf_cid R) (bf_eid R).

(* [comment removed for export] *)
Lemma b64r_loop_rv : forall fuel rest d ret outl acc used,
  0 <= outl -> Z.of_nat (length acc) = ret ->
  (br_rv (b64r_loop fuel rest d ret outl acc used) = Z.of_nat (length (br_out (b64r_loop fuel rest d ret outl acc used)))
   \/ (br_rv (b64r_loop fuel rest d ret outl acc used) = -1 /\ br_out (b64r_loop fuel rest d ret outl acc used) = []))
  /\ Z.of_nat (length (br_out (b64r_loop fuel rest d ret outl acc used))) <= ret + outl.
Proof.
  induction fuel as [|fuel IH]; intros rest d ret outl acc used OL LA.
  - cbn [b64r_loop]. destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
    + split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
    + split; [left; symmetry; exact LA| lia].
  - cbn [b64r_loop]. destruct (Z.leb_spec outl 0) as [E0|E0]; [cbn [br_rv br_out]; split; [left; symmetry; exact LA| lia]|].
    destruct rest as [|c rest'].
    + destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
      * destruct (decode_final_rv d <? 0); cbn [br_rv br_out].
        -- split; [| lia]. right. split; [reflexivity|]. destruct acc; [reflexivity| cbn in LA; lia].
        -- split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
      * split; [left; symmetry; exact LA| lia].
    + cbv zeta. set (r := decode_update d (firstn 1024 (c :: rest'))). clearbody r.
      destruct (dr_rv r <? 0); cbn [br_rv br_out].
      * destruct (Z.eqb_spec ret 0) as [E|E]; cbn [br_rv br_out].
        -- split; [| lia]. destruct acc; [left; reflexivity| cbn in LA; lia].
        -- split; [left; symmetry; exact LA| lia].
      * set (i := Z.min (Z.of_nat (length (dr_out r))) outl).
        assert (LI : Z.of_nat (length (acc ++ firstn (Z.to_nat i) (dr_out r))) = ret + i).
        { rewrite length_app, length_firstn. subst i. rewrite Nat2Z.inj_add, Nat2Z.inj_min, Z2Nat.id by lia. lia. }
        destruct (dr_rv r =? 0); cbn [br_rv br_out].
        -- destruct (Z.eqb_spec (ret + i) 0) as [E|E]; cbn [br_rv br_out].
           ++ split; [| lia]. destruct (acc ++ firstn (Z.to_nat i) (dr_out r)); [left; reflexivity| cbn in LI; lia].
           ++ split; [left; symmetry; exact LI| lia].
        -- destruct (IH (skipn 1024 (c :: rest')) (dr_d r) (ret + i) (outl - i) (acc ++ firstn (Z.to_nat i) (dr_out r)) (used + length (firstn 1024 (c :: rest')))%nat
                       ltac:(lia) LI) as [K1 K2].
           split; [exact K1| lia].
Qed.
Lemma b64_read_rv : forall txt outl, 0 <= outl ->
  (br_rv (b64_read_spec txt outl) = Z.of_nat (length (br_out (b64_read_spec txt outl)))
   \/ (br_rv (b64_read_spec txt outl) = -1 /\ br_out (b64_read_spec txt outl) = []))
  /\ Z.of_nat (length (br_out (b64_read_spec txt outl))) <= outl.
Proof. intros txt outl OL. unfold b64_read_spec. pose proof (b64r_loop_rv (S (S (length txt))) txt [] 0 outl [] 0%nat OL eq_refl) as K. rewrite Z.add_0_l in K. exact K. Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma ENCCTX_rebase : forall L L' m0 e d pid, ENCCTX L m0 e d pid -> In (pid, e, ENCCTX_SIZE) L' -> ENCCTX L' m0 e d pid.
  Proof.
    intros L L' m0 e d pid (raw & line & K1 & K2 & K3 & K4 & K5 & K6 & K7) IN. exists raw, line.
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact IN|]. split; [exact K6| exact K7].
  Qed.
  Lemma ENCCTX_xpres : forall L L' SP m1 m2 e d pid, ENCCTX L m1 e d pid -> xpres L' SP [] m1 m2 -> In (pid, e, ENCCTX_SIZE) L' -> ENCCTX L m2 e d pid.
  Proof.
    intros L L' SP m1 m2 e d pid (raw & line & K1 & K2 & K3 & K4 & K5 & K6 & K7) XP IN. exists raw, line.
    split; [exact K1|]. split; [exact K2|]. split; [| split; [exact K4| split; [exact K5| split; [exact K6| exact K7]]]].
    eapply xpres_rw_cells'; [exact XP| exact K3| | apply Forall_nil].
    right; right. exists (pid, e, ENCCTX_SIZE). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENCCTX_SIZE. lia.
  Qed.
  Lemma B64F_fresh_xpres : forall L L' SP m1 m2 a' Rx, B64F_fresh L m1 a' Rx -> xpres L' SP [] m1 m2 ->
    In (bf_id Rx, a', BIO_SIZE) L' -> In (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE) L' -> B64F_fresh L m2 a' Rx.
  Proof.
    intros until Rx. intros (BC & [junk [LJ CJ]] & REST) XP I1 I2. split; [| split; [exists junk; split; [exact LJ|]| exact REST]].
    - eapply xpres_rw_cells'; [exact XP| exact BC| | apply Forall_nil].
      right; right. exists (bf_id Rx, a', BIO_SIZE). split; [exact I1|]. unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply xpres_rw_cells'; [exact XP| exact CJ| | apply Forall_nil].
      right; right. exists (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE). split; [exact I2|]. unfold b64ctx_fresh_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold B64CTX_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma FX_at : forall (X : list (Z * Z)) (TB : list block) (b : block) (q sz : Z),
    Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X ->
    In b TB -> blk_addr b <= q -> q + sz <= blk_addr b + blk_size b -> 0 <= sz ->
    Forall (fun iv : Z * Z => q + sz <= fst iv \/ snd iv <= q) X.
  Proof.
    intros X TB b q sz FX IN LOQ HIQ SZ. eapply Forall_impl; [| exact FX]. cbn beta. intros iv Fb.
    pose proof (proj1 (Forall_forall _ _) Fb b IN) as K. cbn beta in K. clear - K LOQ HIQ SZ. lia.
  Qed.
  Lemma ENCCTX_xpresX : forall L L' SP X m1 m2 e d pid, ENCCTX L m1 e d pid -> xpres L' SP X m1 m2 -> In (pid, e, ENCCTX_SIZE) L' ->
    Forall (fun iv : Z * Z => e + ENCCTX_SIZE <= fst iv \/ snd iv <= e) X -> ENCCTX L m2 e d pid.
  Proof.
    intros L L' SP X m1 m2 e d pid (raw & line & K1 & K2 & K3 & K4 & K5 & K6 & K7) XP IN FX. exists raw, line.
    split; [exact K1|]. split; [exact K2|]. split; [| split; [exact K4| split; [exact K5| split; [exact K6| exact K7]]]].
    eapply xpres_rw_cells'; [exact XP| exact K3| | cbn [cells_size csize Nat.add length]; unfold ENCCTX_SIZE in FX; exact FX].
    right; right. exists (pid, e, ENCCTX_SIZE). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENCCTX_SIZE. lia.
  Qed.
  Lemma B64F_used_xpres : forall L L' SP X m1 m2 a' Rx, B64F_used L m1 a' Rx -> xpres L' SP X m1 m2 ->
    In (bf_id Rx, a', BIO_SIZE) L' -> In (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE) L' ->
    Forall (fun iv : Z * Z => a' + BIO_SIZE <= fst iv \/ snd iv <= a') X -> Forall (fun iv : Z * Z => bf_ctx Rx + B64CTX_SIZE <= fst iv \/ snd iv <= bf_ctx Rx) X ->
    B64F_used L m2 a' Rx.
  Proof.
    intros until Rx. intros (BC & (hdr & junk & elen & LH & LJ & EL & CJ) & REST) XP I1 I2 F1 F2. split; [| split; [exists hdr, junk, elen; split; [exact LH| split; [exact LJ| split; [exact EL|]]]| exact REST]].
    - eapply xpres_rw_cells'; [exact XP| exact BC| | unfold bio_cells; cbn [cells_size csize Nat.add length]; unfold BIO_SIZE in F1; exact F1].
      right; right. exists (bf_id Rx, a', BIO_SIZE). split; [exact I1|]. unfold bio_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold BIO_SIZE. lia.
    - eapply xpres_rw_cells'; [exact XP| exact CJ| | unfold b64ctx_used_cells; cbn [cells_size csize Nat.add length]; unfold B64CTX_SIZE in F2; exact F2].
      right; right. exists (bf_cid Rx, bf_ctx Rx, B64CTX_SIZE). split; [exact I2|]. unfold b64ctx_used_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold B64CTX_SIZE. lia.
  Qed.
  Lemma B64F_used_rebase : forall L L' m0 a' Rx, B64F_used L m0 a' Rx -> (forall b, In b (blocks_B64F a' Rx) -> In b L') -> B64F_used L' m0 a' Rx.
  Proof.
    intros L L' m0 a' Rx (BC & CX & (I1 & I2 & I3 & REST)) SUB. split; [exact BC|]. split; [exact CX|].
    split; [apply SUB; left; reflexivity|]. split; [apply SUB; right; left; reflexivity|]. split; [apply SUB; right; right; left; reflexivity| exact REST].
  Qed.

  (* [comment removed for export] *)
  Definition chainBT (TB : list block) (a mb2 : Z) (FBl MBl : list block) (m0 : mem) : Prop :=
    exists (R9 : b64frep) (d9 : list Z) (M9 : membio),
         B64F_used TB m0 a R9 /\ blocks_B64F a R9 = FBl /\ bf_next R9 = mb2 /\ ENCCTX TB m0 (bf_enc R9) d9 (bf_eid R9)
      /\ MEMBIO TB m0 mb2 M9 /\ blocks_MEMBIO mb2 M9 = MBl /\ mb_next M9 = 0.
  Lemma chainBT_frame : forall FBl MBl a mb2 (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
    chainBT (FBl ++ MBl) a mb2 FBl MBl m1 -> xpres L SP X m1 m2 -> (forall b, In b (FBl ++ MBl) -> In b L) -> hceil <= SP ->
    Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) (FBl ++ MBl)) X ->
    chainBT (FBl ++ MBl) a mb2 FBl MBl m2.
  Proof.
    intros until m2. intros (R9 & d9 & M9 & BU & BLK & NX & EC & MB & MBK & MNX) XP SUB CE FX. exists R9, d9, M9.
    pose proof BU as (_ & _ & (I1 & I2 & I3 & RG1 & RG2 & RG3 & _)).
    pose proof RG1 as (_ & _ & Z1 & _). pose proof RG2 as (_ & _ & Z2 & _). pose proof RG3 as (_ & _ & Z3 & _).
    split; [| split; [exact BLK| split; [exact NX| split; [| split; [| split; [exact MBK| exact MNX]]]]]].
    - eapply B64F_used_xpres; [exact BU| exact XP| apply SUB; exact I1| apply SUB; exact I2| |].
      + eapply (FX_at X _ (bf_id R9, a, BIO_SIZE)); [exact FX| exact I1| cbn; lia| cbn; lia| unfold BIO_SIZE; lia].
      + eapply (FX_at X _ (bf_cid R9, bf_ctx R9, B64CTX_SIZE)); [exact FX| exact I2| cbn; lia| cbn; lia| unfold B64CTX_SIZE; lia].
    - pose proof EC as (_ & _ & _ & _ & _ & _ & IE & _).
      eapply ENCCTX_xpresX; [exact EC| exact XP| apply SUB; exact IE|].
      eapply (FX_at X _ (bf_eid R9, bf_enc R9, ENCCTX_SIZE)); [exact FX| exact IE| cbn; lia| cbn; lia| unfold ENCCTX_SIZE; lia].
    - eapply (MEMBIO_frame0 L _ SP m2 m2); [| intros b Hb; rewrite MBK in Hb; apply in_or_app; right; exact Hb| apply xpres_refl].
      eapply (MEMBIO_frameA _ L SP X m1 m2); [exact MB| intros b Hb; apply SUB; rewrite MBK in Hb; apply in_or_app; right; exact Hb| exact XP|].
      eapply Forall_impl; [| exact FX]. cbn beta. intros iv Fb. rewrite MBK. eapply incl_Forall; [| exact Fb]. intros b Hb. apply in_or_app. right. exact Hb.
  Qed.
  Lemma blocks_B64F_facts : forall a' Rx, Z.of_nat (length (blocks_B64F a' Rx)) = 3 /\ lb_bytes (blocks_B64F a' Rx) = B64F_BYTES /\ lb_big (blocks_B64F a' Rx) = 1.
  Proof. intros a' Rx. unfold blocks_B64F, B64F_BYTES. cbn. repeat split; reflexivity. Qed.

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [unfold RA; lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma subw_len : forall n k, 0 <= k <= 31 -> 1 <= n <= 512 ->
    bv_swrap 32 (bv_unsigned (Z_to_bv 64 n) - bv_unsigned (Z_to_bv 64 (- (512 * k)))) = n + 512 * k.
  Proof.
    intros n k KR NR. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
    Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fb_seg1 :
    forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (n k : Z),
      0 <= k <= 31 -> 1 <= n <= 512 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R1) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 (n + 512 * k)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (n + 512 * k)) (Z_to_bv 64 (- (512 * k))) s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom usegs))
        (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 n) (Z_to_bv 64 (- (512 * k))) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FM_B64) fc None m (seg_rom usegs)).
  Proof.
    intros until k. intros KR NR MI. unfold FM_B64, FB_R1, P_BIO_new_mem_buf.
    step. rewrite subw_len by assumption. do 3 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fb_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mb2 : Z),
      0 < mb2 < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 mb2) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_f_base64) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mb2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R1)) fc None m (seg_rom usegs)).
  Proof. intros until mb2. intros MR MI. retpc FB_R1. unfold FB_R1, FB_R2, P_BIO_f_base64. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_new) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R2)) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. retpc FB_R2. unfold FB_R2, FB_R3, P_BIO_new. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg4 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      0 < a < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 256) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 a) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_set_flags) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R3)) fc None m (seg_rom usegs)).
  Proof. intros until a. intros AR MI. retpc FB_R3. unfold FB_R3, FB_R4, P_BIO_set_flags. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. do 4 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R5) sp gp tp t0 t1 t2 s0 s1 s6 s2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_push) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R4)) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. retpc FB_R4. unfold FB_R4, FB_R5, P_BIO_push. do 4 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R6) sp gp tp t0 t1 t2 s0 s1 s7 (Z_to_bv 64 A_ECHS_FILE_RP) (Z_to_bv 64 626) a3 a4 a5 a6 a7 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R5) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R5)) fc None m (seg_rom usegs)).
  Proof. intros until m. intros MI. retpc FB_R5. unfold FB_R5, FB_R6, P_CRYPTO_malloc, A_ECHS_FILE_RP. do 7 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (Bb : Z),
      0 < Bb < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 FB_R7) sp gp tp t0 t1 t2 s0 s1 s2 (Z_to_bv 64 Bb) s8 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 Bb) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R6) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Bb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R6)) fc None m (seg_rom usegs)).
  Proof. intros until Bb. intros BR MI. retpc FB_R6. unfold FB_R6, FB_R7, P_BIO_read. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. do 6 step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma fb_seg8 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (rv : Z),
      - 2^31 <= rv < 2^31 -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = if rv <=? 0
                            then MS (mkR (Z_to_bv 64 FB_631_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom usegs)
                            else MS (mkR (Z_to_bv 64 FB_R7) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 rv) s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 DF_DEC) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 FB_R7) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (Z_to_bv 64 FB_R7)) fc None m (seg_rom usegs)).
  Proof.
    intros until rv. intros RR MI. retpc FB_R7. unfold FB_R7, FB_631_R1, P_ERR_new, DF_DEC.
    destruct (Z.leb_spec rv 0) as [LE0|GT0].
    - step. if_cases K2; zify_cond K2.
      + clear K2. step. step. apply evt_done. reflexivity.
      + exfalso. change 18446744073709551615 with (Z.ones 64) in K0, K1. rewrite Z.land_ones in K0, K1 by (clear; lia). clear - K0 K1 LE0 RR. Z.div_mod_to_equations. lia.
    - step. if_cases K2; zify_cond K2.
      + exfalso. try (change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by (clear; lia); rewrite Z.mod_small in K2 by (clear - GT0 RR; lia)).
        apply Bool.andb_false_iff in K2. destruct K2 as [K2|K2]; [apply Z.ltb_ge in K2| apply Z.ltb_ge in K2]; clear - K2 GT0 RR; lia.
      + clear K0 K1. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fb_631g : rp_glue FB_631_R1 DF_TX_R2 P_ERR_set_debug A_ECHS_FILE_RP 631 A_ECHS_FUNC_RP.
  Proof.
    unfold rp_glue. intros. retpc FB_631_R1. unfold FB_631_R1, DF_TX_R2, P_ERR_set_debug, A_ECHS_FILE_RP, A_ECHS_FUNC_RP.
    do 8 step. apply evt_done. do 12 eexists. reflexivity.
  Qed.
End S.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Hypothesis CERTO3 : egs_fresh_stmt H.
  Hypothesis CERTA : getdefctx_fresh_stmt H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let HRE : realloc_sr_stmt H := proj1 (proj2 HX).
  Let STATICS : statics_of_RHEAP H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).

  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word).
  Hypotheses (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo)
             (MBO : MEMBIO LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (DS : bytes_at usegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : hs_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : hs_KREL H s mo)
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= hs_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= hs_LIVE_CNT_MAX H)
             (BUDG : lb_big (mid_errblocks M ++ LB) + mid_big M + DECODE_BIG <= hs_LIVE_BIG_MAX H)
             (AUX : hs_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk usegs m lo (bv_unsigned sp)) (CEIL : hceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M)
             (ERR : rw_cells usegs m (errno_addr tp) [C4 errv]) (MI : mem_inv usegs m) (TP : tp = Z_to_bv 64 RATP) (RAE : bv_unsigned ra mod 2 = 0).
  Hypothesis PAYS : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S.
  Hypothesis TIME : time_sr_stmt H.

  Local Notation L0c := (L0 LB M).
  Local Notation SPc := (SP' sp).
  Local Notation RBPc := (RBP sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation XFc := (XF M st mb R).
  Local Notation RCFACTS := (rc_facts H HX ra sp tp a0 a1 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  Local Notation FWK := (fwk H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B R ds).
  Local Notation FWKX := (fwk_x H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                           HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  Local Notation DWKG p A nA pbin Bb nB bs R' jt TB BT := (dwkG H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt TB BT).
  Local Notation RPES p A nA pbin Bb nB bs R' jt bt TB BT := (rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation BTFREE p A nA pbin Bb nB bs R' jt bt TB BT := (btfree_stmt H ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo LIB LB M st mb lo B S R ds p A nA pbin Bb nB bs R' jt bt TB BT).
  Local Notation DWKINIT := (dwk_init H HX ra sp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                              HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  Local Notation RPFLAT := (rp_flat H HX CERTO3 ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                             HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE PAYS).
  Local Notation RPTAILXG := (rp_tailXg H HX CERTO3 ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M x st mb lo B S R ds errv A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6
                               HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE).
  Local Notation DLOOPB := (dloop_budget H HX m s LB M HP BUD BUDC BUDG).
  Hypothesis RPE : forall (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (jt : list byte) (bt : Z) (TB : list block) (BT : mem -> Prop),
      1 <= mb_len R <= nA /\ nA <= 512 * 3 ->
      0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN ->
      mb_static R R' -> mb_pos R' = mb_len R ->
      0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1 ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
          BT m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
          Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X -> BT m2) ->
      RPES p A nA pbin Bb nB bs R' jt bt TB BT.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac stack_tac LO STK0 SPR LO0 := unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia);
    match goal with |- _ <= _ - ?c => let v := eval vm_compute in c in change c with v end; clear - LO STK0; lia.

  (* [comment removed for export] *)
  Lemma xpres_stack : forall L s' m1 m2, munch [(lo, SPc)] m1 m2 -> wmono usegs m1 m2 -> hs_RHEAP H s' L m1 \/ (forall b, In b L -> blk_addr b + blk_size b <= hceil) -> xpres L SPc [] m1 m2.
  Proof using HH CEIL LO.
    intros L s' m1 m2 MU WM HB. eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros q Hq [HC _]. cbn [outside fst snd]. split; [| exact I].
    hcb. pose proof (readcfg_stack_lo M) as STK0.
    assert (HB' : forall b, In b L -> blk_addr b + blk_size b <= hceil) by (destruct HB as [HB|HB]; [exact (HH_blocks_below H HH _ _ _ HB)| exact HB]).
    destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP' in *; clear - HC; lia| unfold SP' in *; clear - HC CEIL HCEILB LO STK0; lia|].
    pose proof (HB' b Hb) as E. clear - E Hr CEIL. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_headw : forall Lx p0 A0' n0 m1 m2 W s',
    hs_RHEAP H s' (Lx ++ (p0, A0', n0) :: L0c) m1 -> munch W m1 m2 -> wmono usegs m1 m2 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc) \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    xpres ((p0, A0', n0) :: L0c) SPc [] m1 m2.
  Proof using HH CEIL LO.
    intros until s'. intros HP1 MU WM FW. hcb. pose proof (readcfg_stack_lo M) as STK0.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP1) as ND. destruct (nd_app _ _ ND) as [D2 _].
    pose proof (HH_blocks_below H HH _ _ _ HP1) as HB.
    eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros q Hq [HC _].
    clear MU WM. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [| apply IH; eapply Forall_inv_tail; exact FW].
    destruct K as [[K1 K2]|(b & Hb & K1 & K2)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP' in *; clear - HC K2; lia| unfold SP' in *; clear - HC K1 CEIL HCEILB; lia|].
      pose proof (HB b ltac:(apply in_or_app; right; exact Hb)) as E. clear - E Hr K1 CEIL. lia.
    - pose proof (client_outside_block H HH _ _ _ b ((p0, A0', n0) :: L0c) SPc q HP1 ltac:(apply in_or_app; left; exact Hb) ltac:(intros b' Hb'; apply in_or_app; right; exact Hb')
                    ltac:(intros c c' Hc Hc'; destruct Hc as [<-|[]]; exact (D2 _ _ Hb Hc')) ltac:(unfold SP'; clear - CEIL LO STK0; lia) HC) as O.
      clear - O K1 K2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fwk_wL : forall Lx p0 A0' n0 R' j0 j2 rb m1 mo1 s1' m2 W,
    FWK Lx p0 A0' n0 R' j0 j2 rb m1 mo1 s1' ->
    munch W m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 -> stk usegs m2 lo SPc ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc) \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) W ->
    FWK Lx p0 A0' n0 R' j0 j2 rb m2 mo1 s1'.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX.
    intros until W. intros FW MU WM MI2 ST2 FWW.
    pose proof FW as (HP1 & KREL1 & MP1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv1 ERR1] & _ & _ & _ & AUX1 & _).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof (HH_blocks_below H HH _ _ _ HP1) as HB.
    pose proof (xpres_headw Lx p0 A0' n0 m1 m2 W s1' HP1 MU WM FWW) as XP.
    assert (OFF : forall b, In b Lx -> blk_addr b + blk_size b <= IMG_LO \/ IMG_HI <= blk_addr b).
    { intros b Hb. pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP1 ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & O). unfold IMG_LO, IMG_HI. exact O. }
    assert (HP2 : hs_RHEAP H s1' (Lx ++ (p0, A0', n0) :: L0c) m2).
    { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta.
      intros iv [[K1 K2]|(b & Hb & K1 & K2)]; [left; clear - K1 CEIL; lia| right; right; exists b; split; [apply in_or_app; left; exact Hb| split; assumption]]. }
    assert (ERR2 : rw_cells usegs m2 RERRNO [C4 errv1]).
    { eapply rw_cells_transport; [exact ERR1| exact MU| exact WM|]. clear - FWW HB OFF CEIL HCEILB. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FWW) as K. cbn in K.
      split; [| apply IH; eapply Forall_inv_tail; exact FWW]. unfold RERRNO, IMG_LO, IMG_HI in *.
      destruct K as [[K1 K2]|(b & Hb & K1 & K2)]; [lia| pose proof (OFF b Hb); lia]. }
    assert (AUX2 : hs_rauxv_ok H m2 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU| exact WM|]. eapply Forall_impl; [| exact FWW]. cbn beta. unfold RAUXV_CELL, SP', IMG_LO, IMG_HI in *.
      intros iv [[K1 K2]|(b & Hb & K1 & K2)]; [clear - K1 K2 SPB CEIL HCEILB LO STK0; lia|].
      pose proof (OFF b Hb) as O. pose proof (HB b ltac:(apply in_or_app; left; exact Hb)) as E. clear - K1 K2 O E SPB CEIL HCEILB LO STK0. lia. }
    exact (FWKX Lx Lx p0 A0' n0 R' j0 j2 rb m1 mo1 s1' m2 mo1 s1' FW XP HP2 KREL1 MP1 (ex_intro _ errv1 ERR2) MI2 ST2 AUX2).
  Qed.

  (* [comment removed for export] *)
  Lemma xpres_blocksw : forall L s' Lh m1 m2 W,
    hs_RHEAP H s' Lh m1 -> (forall b, In b L -> In b Lh) ->
    munch W m1 m2 -> wmono usegs m1 m2 ->
    Forall (fun iv : Z * Z => (lo <= fst iv /\ snd iv <= SPc)
                           \/ (exists b, In b Lh /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b /\ forall c, In c L -> blk_id c <> blk_id b)) W ->
    xpres L SPc [] m1 m2.
  Proof using HH CEIL LO.
    intros L s' Lh m1 m2 W HP1 SUB MU WM FW. hcb. pose proof (readcfg_stack_lo M) as STK0.
    pose proof (HH_blocks_below H HH _ _ _ HP1) as HB.
    eapply xpres_of_munch_gen; [exact MU| exact WM|]. intros q Hq [HC _].
    clear MU WM. induction W as [|[u v] W IH]; [exact I|]. cbn. pose proof (Forall_inv FW) as K. cbn in K.
    split; [| apply IH; eapply Forall_inv_tail; exact FW].
    destruct K as [[K1 K2]|(b & Hb & K1 & K2 & NE)].
    - destruct HC as [HC|[[HC _]|(b & Hb & Hr)]]; [unfold SP' in *; clear - HC K2; lia| unfold SP' in *; clear - HC K1 CEIL HCEILB; lia|].
      pose proof (HB b (SUB _ Hb)) as E. clear - E Hr K1 CEIL. lia.
    - pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP1 Hb) as (_ & _ & _ & _ & O). pose proof (HB b Hb) as E.
      destruct HC as [HC|[[HC _]|(c & Hc & Hr)]]; [unfold SP' in *; clear - HC K2 E CEIL LO STK0; lia| clear - HC K1 K2 O; lia|].
      pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ c b HP1 (SUB _ Hc) Hb (NE _ Hc)) as D. clear - D Hr K1 K2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma btfree_chain : forall p A nA pbin Bb nB bs R' jt a mb2 FBl MBl,
    BTFREE p A nA pbin Bb nB bs R' jt a (FBl ++ MBl) (chainBT (FBl ++ MBl) a mb2 FBl MBl).
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HX PERM.
    intros until MBl. unfold btfree_stmt.
    intros NB S' M' LE fr j3 m1 mo1 s1' ra0 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 Q DW RAR RAE2 K.
    pose proof DW as (HP1 & KREL1 & MP1 & LM1 & STP1 & _ & CTX1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BT1 & _ & _ & _ & _ & [errv1 ERR1] & MI1 & ST1 & AUX1 & _).
    destruct BT1 as (R9 & d9 & M9 & BU & BLK & NX & EC & MB & MBK & MNX).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof LM1 as (IM1 & _ & CP1 & _ & _ & _ & _ & _ & GM1 & _ & _ & MM1 & MB1 & _). rewrite CTX1, CTX in CP1.
    pose proof (dec_stack M M' STP1) as (_ & _ & STKR & _).
    unfold drest in HP1. cbn [app] in HP1.
    assert (SUBT : forall b, In b (FBl ++ MBl) -> In b (mid_errblocks M' ++ NB ++ (FBl ++ MBl) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { intros b Hb. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP1) as NDf.
    assert (PF : Permutation (mid_errblocks M' ++ NB ++ (FBl ++ MBl) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)
                             ((FBl ++ MBl) ++ (mid_errblocks M' ++ NB) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { rewrite (app_assoc (mid_errblocks M') NB). apply Permutation_app_swap_app. }
    pose proof (Permutation_NoDup (Permutation_map blk_id PF) NDf) as NDp. destruct (nd_app _ _ NDp) as [DJT _].
    assert (NDT : List.NoDup (map blk_id (FBl ++ MBl))) by (rewrite map_app in NDp; exact (NoDup_app_remove_r _ _ NDp)).
    eapply (sr_seq H HH).
    { eapply (biofreeall_spec H HH) with (LB := mid_errblocks M' ++ NB ++ (FBl ++ MBl) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) (a := a) (mb := mb2) (R := R9) (M := M9) (d := d9) (x := x) (lo := lo) (B := B).
      all: try first [reflexivity| exact NX| exact MNX| exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact IM1| exact GM1| exact MM1| exact MB1].
      all: lazymatch goal with
           | |- B64F_used _ _ _ _ => eapply B64F_used_rebase; [exact BU| intros b Hb; apply SUBT; rewrite <- BLK; apply in_or_app; left; exact Hb]
           | |- ENCCTX _ _ _ _ _ => pose proof EC as (raw & line & _ & _ & _ & _ & IE & _); eapply ENCCTX_rebase; [exact EC| apply SUBT; exact IE]
           | |- MEMBIO _ _ _ _ => eapply MEMBIO_mono; [exact MB| exact SUBT]
           | |- CTXPH _ _ _ => eapply CTXPH_mono; [exact CP1| intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb];
                                 [do 3 (apply in_or_app; right); right; right; apply in_or_app; left; exact Hb| do 3 (apply in_or_app; right); right; right; apply in_or_app; right; apply SUBL; exact Hb]]
           | |- List.NoDup _ => rewrite BLK, MBK; exact NDT
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
           | |- lo <= _ - _ => stack_tac LO STK0 SPR LO0
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- bv_unsigned _ mod 2 = 0 => rewrite unsigned_lit by (clear - RAR; lia); exact RAE2
           | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; Z.div_mod_to_equations; lia
           | |- ?G => idtac "BFAPRE" G
           end. }
    intros [ms2 mo2] PO. unfold biofreeall_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m2 & errv2 & s2' & LBr & -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & PL & IM2 & GM2 & MBt2 & MMt2 & XP2).
    unfold SP' in ST2, XP2. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST2, XP2 by (clear - SPR LO STK0 LO0; lia). fold (SP' sp) in ST2, XP2. rewrite errno_RATP in ERR2.
    rewrite BLK, MBK in PL. rewrite (app_assoc FBl MBl LBr) in PL.
    assert (PR : Permutation LBr ((mid_errblocks M' ++ NB) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { eapply Permutation_app_inv_l. eapply Permutation_trans; [apply Permutation_sym; exact PL| exact PF]. }
    eapply K; [| exact KREL2| eapply (mpres_trans H HH); [exact MP1| exact MP2]| exact MI2| exact ST2| exact ERR2| exact AUX2|].
    - eapply PERM; [exact HP2|]. rewrite (app_assoc (mid_errblocks M') NB). exact PR.
    - eapply xpres_weaken; [exact XP2| clear; lia| | intros q Hq; exact Hq].
      intros b Hb. assert (HbF : In b (mid_errblocks M' ++ NB ++ (FBl ++ MBl) ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
      { apply in_or_app. right. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb| apply in_or_app; right; apply in_or_app; right; exact Hb]. }
      pose proof (Permutation_in _ PL HbF) as Hb2. apply in_app_or in Hb2. destruct Hb2 as [Hb2|Hb2]; [| exact Hb2].
      exfalso. apply (DJT b b Hb2); [| reflexivity]. apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb| right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_b64arm : rp_b64K H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB M st mb lo B S R ds.
  Proof using A0 A1 SO SE SEO STL MBO MP0 MN0 MBB MBS DS DSL PAYL PAYS NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC BUDG AUX SPB BHI SPA ST CEIL LO ERR MI TP RAE HH HRE HX CERTO3 CERTA PERM STATICS TIME RPE.
    unfold rp_b64K. intros k n p A R' j0 j2 m1 mo1 s1' rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s10w s11w u3 u4 u5 u6 KR NEQ NR L5 FW.
    pose proof FW as (HP1 & KREL1 & MP1 & MBO1 & MST & POS & NA1 & NA2 & DSm1 & DSA1 & FRlo1 & RB1 & FRhi1 & [errv1 ERR1] & LM1 & MI1 & ST1 & AUX1 & XA1).
    destruct RCFACTS as (SEQ & SIN & SBR & BEL0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA). hcb. pose proof (word_range sp) as SPR.
    pose proof DSL as DSL1. unfold zlength in DSL1. unfold OSSL_ECH_MAX_ECHCONFIG_LEN in L5.
    pose proof LM1 as (IM1 & MFa & CP1 & _ & _ & _ & _ & _ & GM1 & GE1 & _ & MM1 & MB1 & _ & RL1). rewrite MF1 in MFa. rewrite CTX in CP1.
    destruct (lad_head_facts H HX L0c _ _ _ _ _ HP1) as (BR & BH & NIP & DISJ & BEL). pose proof BR as (Ba1 & Ba2 & Ba3 & Ba4 & Ba5).
    (* [comment removed for export] *)
    pose proof (errph_nonneg (mid_err M)) as (EN1 & EN2 & EN3). pose proof (ctxph_nonneg3 (mid_ctx M)) as (CN1 & CN2 & CN3).
    assert (BY0 : lb_bytes L0c + 512 * (k + 1) + 126976 <= hs_LIVE_MAX H) by (unfold L0, mid_bytes, DECODE_BYTES, ERRSTR_BYTES in BUD |- *; clear - BUD EN1 CN1 KR NEQ NR L5; lia).
    assert (CT0 : Z.of_nat (length L0c) + 750 <= hs_LIVE_CNT_MAX H) by (unfold L0, mid_cnt, DECODE_CNT, ERRSTR_CNT in BUDC |- *; clear - BUDC EN2 CN2; lia).
    assert (BG0 : lb_big L0c + 6 <= hs_LIVE_BIG_MAX H) by (unfold L0, mid_big, DECODE_BIG in BUDG |- *; clear - BUDG EN3 CN3; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL1| eapply fb_seg1; [exact KR| exact NR| exact MI1]|]. intros ms2 ->.
    replace (n + 512 * k) with (mb_len R) by (clear - NEQ; lia).
    pose proof (newmembuf_spec H HX (cnewex_spec H HX CERTA)) as NM. unfold newmembuf_stmt in NM.
    eapply (sr_seq H HH).
    { eapply NM with (ph := CtxReady x) (buf := A) (len := mb_len R) (v := 1) (lo := lo) (B := B) (LB := (p, A, 512 * (k + 1)) :: L0c) (s := s1') (errv := errv1); clear NM; try reflexivity.
      all: try first [exact HP1| exact KREL1| exact AUX1| exact MI1| exact CEIL| exact MFa| exact IM1| exact GM1| exact MM1| exact RL1| exact Ba1].
      all: lazymatch goal with
           | |- _ + _ <= hceil => clear - BH NA1; lia
           | |- 0 <= mb_len R < _ => clear - L5; lia
           | |- lb_bytes _ + _ + _ <= _ => rewrite lb_bytes_cons; cbn [blk_size snd ctxph_bytes]; unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; clear - BY0; lia
           | |- Z.of_nat (length _) + _ + _ <= _ => cbn [length ctxph_cnt]; rewrite Nat2Z.inj_succ; clear - CT0; lia
           | |- lb_big _ + _ <= _ => rewrite lb_big_cons; cbn [blk_size snd ctxph_big]; pose proof (big1_range (512 * (k + 1))); clear - BG0 H0; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST1
           | |- lo <= _ - _ => stack_tac LO STK0 SPR LO0
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR1
           | |- CTXPH _ _ _ => eapply CTXPH_mono; [exact CP1| intros b Hb; right; apply SUB0; apply SUBL; exact Hb]
           | |- ?G => idtac "NMPRE" G
           end. }
    clear NM. intros [ms3 mo3] PO. unfold newmembuf_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & z3 & z4 & z5 & z6 & m3 & errv3 & s3' & LBN & x2 & mb2 & M2 & -> & KREL3 & MP3 & MI3 & ST3 & ERR3 & AUX3
                    & HP3 & CD3 & CP3 & _ & MBO3 & MBUF & MLEN & MPOS & MNR & MNX & MPV & MBP & MAP & MF3 & IM3 & GM3 & MM3 & RL3 & XP3).
    cbn [ctxph_delta ctxph_foot] in CD3, XP3. destruct CD3 as [-> ->]. cbn [app] in HP3, CP3, MBO3.
    unfold SP' in ST3, XP3. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST3, XP3 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR3. fold (SP' sp) in ST3, XP3.
    pose proof (xpres_drop_memflag _ _ [] [] m1 m3 MFa MF3 XP3) as XP3'. cbn [app] in XP3'.
    pose proof (FWKX [] (blocks_MEMBIO mb2 M2) p A (512 * (k + 1)) R' j0 j2 (wz n) m1 mo1 s1' m3 mo3 s3' FW XP3' HP3 KREL3
                  ltac:(eapply (mpres_trans H HH); [exact MP1| exact MP3]) (ex_intro _ errv3 ERR3) MI3 ST3 AUX3) as FW3.
    clear XP3 XP3' FW HP1 KREL1 MI1 ST1 AUX1 ERR1 XA1 DSm1 DSA1 FRlo1 RB1 FRhi1.
    set (MB2 := blocks_MEMBIO mb2 M2) in *.
    pose proof (HH_blocks_below H HH _ _ _ HP3) as HB3. destruct (membio_blocks_facts mb2 M2) as (MBY & MBL & MBG). fold MB2 in MBY, MBL, MBG.
    pose proof MBO3 as (_ & _ & _ & _ & I21 & I22 & I23 & I24 & _).
    assert (MBH : mb2 + BIO_SIZE <= hceil) by (pose proof (HB3 _ I21) as K0; cbn [blk_addr blk_size fst snd] in K0; exact K0).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL3| eapply fb_seg2; [clear - MBP MBH HCEILB; unfold BIO_SIZE in *; lia| exact MI3]|]. intros ms4 ->.
    eapply (sr_evt_krel H HH); [exact KREL3| eapply biofb64_spec with (lo := lo); [unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST3| stack_tac LO STK0 SPR LO0| exact MI3| reflexivity]|].
    cbv beta. intros ms5 (w0' & w1' & w2' & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3' & w4' & w5' & w6' & m4 & -> & MU4 & WM4 & MI4 & ST4).
    unfold SP' in MU4, ST4. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in MU4, ST4 by (clear - SPR LO STK0 LO0; lia). fold (SP' sp) in MU4, ST4.
    pose proof (fwk_wL MB2 p A _ R' j0 j2 (wz n) m3 mo3 s3' m4 _ FW3 MU4 WM4 MI4 ST4 ltac:(apply Forall_cons; [left; cbn; clear; lia| apply Forall_nil])) as FW4.
    assert (XP34 : xpres (MB2 ++ (p, A, 512 * (k + 1)) :: L0c) SPc [] m3 m4) by (eapply xpres_stack; [exact MU4| exact WM4| left; exact HP3]).
    assert (MBO4 : MEMBIO (MB2 ++ (p, A, 512 * (k + 1)) :: L0c) m4 mb2 M2).
    { eapply (MEMBIO_frame0 _ _ SPc); [exact MBO3| intros b Hb; apply in_or_app; left; exact Hb| exact XP34]. }
    clear FW3 MU4 WM4 MI3 ST3 KREL3 AUX3 ERR3 MBO3 CP3.
    pose proof FW4 as (HP4 & KREL4 & MP4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv4 ERR4] & LM4 & MI4' & ST4' & AUX4 & _).
    pose proof LM4 as (IM4 & MF4 & CP4 & _ & _ & _ & _ & _ & GM4 & GE4 & _ & MM4 & MB4 & _ & RL4). rewrite MF1 in MF4. rewrite CTX in CP4.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4| eapply fb_seg3; exact MI4|]. intros ms6 ->.
    pose proof (bionew_b64_spec H HX) as BN. unfold bionew_b64_stmt in BN.
    eapply (sr_seq H HH).
    { eapply BN with (x := x) (v := 1) (lo := lo) (B := B) (s := s3') (errv := errv4); clear BN; try reflexivity.
      all: try first [exact HP4| exact KREL4| exact AUX4| exact MI4| exact CEIL| exact MF4| exact IM4| exact GM4| exact MB4| exact RL4].
      all: lazymatch goal with
           | |- lb_bytes _ + _ <= _ => rewrite lb_bytes_app, lb_bytes_cons, MBY; cbn [blk_size snd]; unfold MEMBIO_BYTES, B64F_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, B64CTX_SIZE; clear - BY0 KR; lia
           | |- Z.of_nat (length _) + _ <= _ => rewrite length_app, MBL; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - CT0; lia
           | |- lb_big _ + _ <= _ => rewrite lb_big_app, lb_big_cons, MBG; cbn [blk_size snd]; pose proof (big1_range (512 * (k + 1))); clear - BG0 H0; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST4
           | |- lo <= _ - _ => stack_tac LO STK0 SPR LO0
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR4
           | |- CTXPH _ _ _ => eapply CTXPH_mono; [exact CP4| intros b Hb; apply in_or_app; right; right; apply SUB0; apply SUBL; exact Hb]
           | |- ?G => idtac "BNPRE" G
           end. }
    clear BN. intros [ms7 mo7] PO. unfold bionew_b64_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m5 & errv5 & s5' & a & Rf & -> & KREL5 & MP5 & MI5 & ST5 & ERR5 & AUX5
                    & HP5 & CP5 & BC5 & FL0 & RT0 & NR0 & NX0 & PV0 & [cj [CJL CJ5]] & BB5 & BAP & EC5 & APOS & MF5 & IM5 & GM5 & MB5 & RL5 & XP5).
    cbv zeta in HP5. cbv zeta in CP5. cbv zeta in BB5. cbv zeta in EC5.
    unfold SP' in ST5, XP5. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST5, XP5 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR5. fold (SP' sp) in ST5, XP5.
    pose proof (xpres_drop_memflag _ _ [] [] m4 m5 MF4 MF5 XP5) as XP5'. cbn [app] in XP5'.
    set (FB := blocks_B64F a Rf) in *.
    assert (HP5' : hs_RHEAP H s5' ((FB ++ MB2) ++ (p, A, 512 * (k + 1)) :: L0c) m5) by (rewrite <- app_assoc; exact HP5).
    pose proof (FWKX MB2 (FB ++ MB2) p A (512 * (k + 1)) R' j0 j2 (wz n) m4 mo3 s3' m5 mo7 s5' FW4
                  ltac:(eapply xpres_weaken; [exact XP5'| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq])
                  HP5' KREL5 ltac:(eapply (mpres_trans H HH); [exact MP4| exact MP5]) (ex_intro _ errv5 ERR5) MI5 ST5 AUX5) as FW5.
    pose proof (HH_blocks_below H HH _ _ _ HP5') as HB5.
    set (TB := FB ++ MB2) in *.
    (* [comment removed for export] *)
    assert (MBO5 : MEMBIO TB m5 mb2 M2).
    { eapply (MEMBIO_frame0 _ TB SPc m5 m5); [| intros b Hb; unfold TB; apply in_or_app; right; exact Hb| apply xpres_refl].
      eapply (MEMBIO_frame0 _ _ SPc); [exact MBO4| intros b Hb; apply in_or_app; left; exact Hb| exact XP5']. }
    assert (EC5' : ENCCTX TB m5 (bf_enc Rf) [] (bf_eid Rf)) by (eapply ENCCTX_rebase; [exact EC5| unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity]).
    clear MBO4 XP5 XP5' XP34 FW4 HP4 KREL4 MP4 ERR4 LM4 MI4' ST4' AUX4 MI4 ST4 HP5 EC5.
    pose proof BB5 as (IF1 & IF2 & IF3 & RG1 & RG2 & RG3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RG1 as (_ & AAL & _ & AH & AOFF). pose proof RG2 as (CXP & _ & _ & CXH & CXOFF). pose proof RG3 as (ENP & _ & _ & ENH & ENOFF).
    pose proof FW5 as (_ & KREL5' & MP5' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv5' ERR5'] & LM5 & MI5' & ST5' & AUX5' & _).
    (* [comment removed for export] *)
    assert (APM : Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) MB2) FB).
    { apply Forall_forall. intros b Hb. apply Forall_forall. intros b' Hb'.
      eapply (perm_split_disjoint H HX _ _ FB (MB2 ++ (p, A, 512 * (k + 1)) :: L0c)); [exact HP5'| unfold TB; rewrite <- app_assoc; apply Permutation_refl| exact Hb| apply in_or_app; left; exact Hb']. }
    pose proof (Forall_inv APM) as APa. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APe. cbn beta in APa, APe.
    pose proof (Forall_inv APa) as Da1. pose proof (Forall_inv (Forall_inv_tail APa)) as Da2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APa))) as Da3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APa)))) as Da4. pose proof (Forall_inv APe) as De1.
    cbn [blk_addr blk_size fst snd] in Da1, Da2, Da3, Da4, De1. clear APa APe.
    assert (APP : Forall (fun b' => A + 512 * (k + 1) <= blk_addr b' \/ blk_addr b' + blk_size b' <= A) TB).
    { apply Forall_forall. intros b' Hb'.
      pose proof (perm_split_disjoint H HX _ _ TB ((p, A, 512 * (k + 1)) :: L0c) _ _ _ HP5' (Permutation_refl _) Hb' (or_introl eq_refl)) as K0.
      cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    pose proof APP as APP'. unfold TB in APP'. apply Forall_app in APP'. destruct APP' as [APf APm].
    assert (MSEP : MEMBIO_sep mb2 M2).
    { split; [exact MAP|]. rewrite MBUF, MLEN.
      pose proof (Forall_inv APm) as Q1. pose proof (Forall_inv (Forall_inv_tail APm)) as Q2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APm))) as Q3.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APm)))) as Q4.
      cbn [blk_addr blk_size fst snd] in Q1, Q2, Q3, Q4. clear - Q1 Q2 Q3 Q4 NA1. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. repeat split; lia. }
    assert (MBLO : MEMBIO_below mb2 M2 lo).
    { unfold MEMBIO_below. pose proof (HB3 _ I21) as K1. pose proof (HB3 _ I22) as K2. pose proof (HB3 _ I23) as K3. pose proof (HB3 _ I24) as K4.
      cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4. clear - K1 K2 K3 K4 CEIL. repeat split; lia. }
    assert (BFL : B64F_below a Rf lo) by (unfold B64F_below; clear - AH CXH ENH CEIL; repeat split; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL5| eapply fb_seg4; [clear - APOS AH HCEILB; unfold BIO_SIZE in *; lia| exact MI5]|]. intros ms8 ->.
    pose proof biosetflags_spec as SF. unfold biosetflags_stmt, bioacc_stmt_at in SF.
    eapply (sr_evt_krel H HH); [exact KREL5| eapply SF with (a := a) (x := 256) (lo := lo) (B := b64f_bio Rf); clear SF;
      [reflexivity| reflexivity| clear; lia| exact APOS| clear - AAL; lia| exact BC5| | clear - AH CEIL; lia| unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST5| stack_tac LO STK0 SPR LO0| exact MI5| reflexivity]|].
    { unfold bio_ok, b64f_bio. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite].
      rewrite FL0, RT0, NR0, NX0, PV0. unfold A_b64_method. clear - CXP CXH HCEILB. unfold B64CTX_SIZE in CXH. repeat split; lia. }
    clear SF. cbv beta. intros ms9 (x0 & x1 & x2' & f1 & f2 & f3 & f4 & f5 & f6 & f7 & x3 & x4 & x5 & x6 & m6 & -> & MU6 & WM6 & MI6 & ST6 & BC6).
    unfold SP' in MU6, ST6. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in MU6, ST6 by (clear - SPR LO STK0 LO0; lia). fold (SP' sp) in MU6, ST6.
    unfold b64f_bio in BC6. cbn [bio_with_flags bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC6.
    rewrite FL0, RT0, NR0, NX0, PV0 in BC6. cbn [Z.lor] in BC6.
    change (rw_cells usegs m6 a (bio_cells (b64f_bio (bf_fresh2 Rf 0)))) in BC6.
    pose proof (fwk_wL TB p A _ R' j0 j2 (wz n) m5 mo7 s5' m6 _ FW5 MU6 WM6 MI6 ST6
                  ltac:(apply Forall_cons; [left; cbn; clear; lia|]; apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [unfold TB, FB, blocks_B64F; apply in_or_app; left; left; reflexivity| cbn; clear; lia]| apply Forall_nil])) as FW6.
    pose proof FW6 as (HP6 & KREL6 & MP6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv6 ERR6] & LM6 & MI6' & ST6' & AUX6 & _).
    pose proof LM6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM6 & MB6 & _).
    assert (MBO6 : MEMBIO TB m6 mb2 M2).
    { eapply (MEMBIO_transport _ m5 m6); [exact MU6| exact WM6| | | | | exact MBO5].
      - pose proof (HB3 _ I21) as K0. cbn [blk_addr blk_size fst snd] in K0. cbn [disjoint_from]. clear - K0 CEIL Da1. unfold BIO_SIZE in *. split; [lia| split; [lia| exact I]].
      - pose proof (HB3 _ I22) as K0. cbn [blk_addr blk_size fst snd] in K0. cbn [disjoint_from]. clear - K0 CEIL Da2. unfold BIO_SIZE, BIOBUFMEM_SIZE in *. split; [lia| split; [lia| exact I]].
      - pose proof (HB3 _ I23) as K0. cbn [blk_addr blk_size fst snd] in K0. cbn [disjoint_from]. clear - K0 CEIL Da3. unfold BIO_SIZE, BUFMEM_SIZE in *. split; [lia| split; [lia| exact I]].
      - pose proof (HB3 _ I24) as K0. cbn [blk_addr blk_size fst snd] in K0. cbn [disjoint_from]. clear - K0 CEIL Da4. unfold BIO_SIZE, BUFMEM_SIZE in *. split; [lia| split; [lia| exact I]]. }
    pose proof BAP as (BA1 & BA2 & BA3).
    assert (CJ6 : rw_cells usegs m6 (bf_ctx Rf) (b64ctx_fresh_cells (bf_enc Rf) cj)).
    { eapply rw_cells_transport; [exact CJ5| exact MU6| exact WM6|]. unfold b64ctx_fresh_cells. cbn [cells_size csize Nat.add length disjoint_from].
      clear - CXH CEIL BA1. unfold BIO_SIZE, B64CTX_SIZE in *. split; [lia| split; [lia| exact I]]. }
    assert (EC6 : ENCCTX TB m6 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_transport; [exact MU6| exact WM6| | exact EC5']. cbn [disjoint_from]. clear - ENH CEIL BA2. unfold BIO_SIZE in *. split; [lia| split; [lia| exact I]]. }
    clear MU6 WM6 MI6 ST6 CJ5 EC5' MBO5 FW5 HP5' KREL5 KREL5' MP5 MP5' ERR5 ERR5' LM5 MI5 MI5' ST5 ST5' AUX5 AUX5'.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL6| eapply fb_seg5; exact MI6'|]. intros ms10 ->.
    eapply (sr_evt_krel H HH); [exact KREL6| eapply biopush_spec' with (LB := TB) (a := a) (mb := mb2) (lo := lo) (R := bf_fresh2 Rf 0) (M := M2);
      [reflexivity| reflexivity| | exact BAP| reflexivity| exact BFL| exact MBO6| exact MBLO| exact MSEP| exact APM| exact MB6| exact MM6
      | unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST6'| exact CEIL| stack_tac LO STK0 SPR LO0| exact MI6'| reflexivity]|].
    { split; [exact BC6|]. split; [exists cj; split; [exact CJL| exact CJ6]|]. split; [| clear; repeat split; reflexivity].
      unfold B64F_blocks. cbn [bf_id bf_cid bf_eid bf_ctx bf_enc bf_flags bf_retry bf_nread bf_next bf_prev bf_fresh2].
      split; [unfold TB, FB, blocks_B64F; apply in_or_app; left; left; reflexivity|].
      split; [unfold TB, FB, blocks_B64F; apply in_or_app; left; right; left; reflexivity|].
      split; [unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity|].
      split; [exact RG1|]. split; [exact RG2|]. split; [exact RG3|]. clear; repeat split; lia. }
    cbv beta. intros ms11 (q0 & q1 & q2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & q3 & q4 & q5 & q6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & BF7 & MBO7).
    unfold SP' in MU7, ST7. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in MU7, ST7 by (clear - SPR LO STK0 LO0; lia). fold (SP' sp) in MU7, ST7.
    change (B64F_fresh TB m7 a (bf_fresh2 Rf mb2)) in BF7.
    set (M2' := mb_with_hdr M2 (mb_flags M2) (mb_numf M2) (mb_next M2) a) in MBO7.
    pose proof (fwk_wL TB p A _ R' j0 j2 (wz n) m6 mo7 s5' m7 _ FW6 MU7 WM7 MI7 ST7
                  ltac:(apply Forall_cons; [left; cbn; clear; lia|];
                        apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [unfold TB, FB, blocks_B64F; apply in_or_app; left; left; reflexivity| cbn; clear; lia]|];
                        apply Forall_cons; [right; exists (mb_id M2, mb2, BIO_SIZE); split; [unfold TB, MB2, blocks_MEMBIO; apply in_or_app; right; left; reflexivity| cbn; clear; lia]| apply Forall_nil])) as FW7.
    pose proof FW7 as (HP7 & KREL7 & MP7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [errv7 ERR7] & LM7 & MI7' & ST7' & AUX7 & _).
    pose proof LM7 as (IM7 & MF7 & _ & _ & _ & _ & _ & _ & GM7 & _). rewrite MF1 in MF7.
    assert (EC7 : ENCCTX TB m7 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_transport; [exact MU7| exact WM7| | exact EC6]. cbn [disjoint_from]. clear - ENH CEIL BA2 De1. unfold BIO_SIZE in *. split; [lia| split; [lia| split; [lia| exact I]]]. }
    clear MU7 WM7 MI7 ST7 EC6 MBO6 CJ6 BC6 FW6 HP6 KREL6 MP6 ERR6 LM6 MI6' ST6' AUX6.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL7| eapply fb_seg6; exact MI7'|]. intros ms12 ->.
    pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
    eapply (sr_seq H HH).
    { eapply CM with (n := mb_len R) (lo := lo) (B := B) (LB := TB ++ (p, A, 512 * (k + 1)) :: L0c) (s := s5') (v := 1) (errv := errv7); clear CM; try reflexivity.
      all: try first [exact HP7| exact KREL7| exact AUX7| exact MI7'| exact IM7| exact GM7| exact MF7| exact CEIL].
      all: lazymatch goal with
           | |- 1 <= _ < _ => clear - L5; lia
           | |- lb_bytes _ + _ <= _ => unfold TB; rewrite !lb_bytes_app, lb_bytes_cons, MBY; cbn [blk_size snd]; unfold FB, blocks_B64F; cbn [lb_bytes fold_right blk_size snd Z.add];
                                       unfold MEMBIO_BYTES, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, B64CTX_SIZE; clear - BY0 KR L5; lia
           | |- Z.of_nat (length _) + _ <= _ => unfold TB; rewrite !length_app, MBL; unfold FB, blocks_B64F; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - CT0; lia
           | |- lb_big _ + _ <= _ => unfold TB; rewrite !lb_big_app, lb_big_cons, MBG; unfold FB, blocks_B64F; cbn [lb_big fold_right blk_size snd];
                                     pose proof (big1_range (512 * (k + 1))) as G1; pose proof (big1_range BIO_SIZE) as G2; pose proof (big1_range B64CTX_SIZE) as G3; pose proof (big1_range 92) as G4;
                                     rewrite (big1_small (mb_len R)) by (unfold BIGB; clear - L5; lia); rewrite (big1_small BIO_SIZE) by (unfold BIGB, BIO_SIZE; clear; lia); rewrite (big1_small 92) by (unfold BIGB; clear; lia);
                                     clear - BG0 G1 G3; lia
           | |- bv_unsigned _ <= B => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPB; lia
           | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST7'
           | |- lo <= _ - _ => stack_tac LO STK0 SPR LO0
           | |- rw_cells _ _ (errno_addr _) _ => rewrite errno_RATP; exact ERR7
           | |- ?G => idtac "CMPRE" G
           end. }
    clear CM. intros [ms13 mo13] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & v3 & v4 & v5 & v6 & m8 & errv8 & Bb & junk8 & pbin & s8' & -> & KREL8 & MP8 & MI8 & ST8 & ERR8 & AUX8 & XP8 & BRB & HP8 & CELLS8 & MF8 & IM8 & GM8).
    unfold SP' in ST8, XP8. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in ST8, XP8 by (clear - SPR LO STK0 LO0; lia). rewrite errno_RATP in ERR8. fold (SP' sp) in ST8, XP8.
    pose proof (xpres_drop_memflag _ _ [] [] m7 m8 MF7 MF8 XP8) as XP8'. cbn [app] in XP8'.
    pose proof BRB as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5).
    pose proof (FWKX TB ((pbin, Bb, mb_len R) :: TB) p A (512 * (k + 1)) R' j0 j2 (wz n) m7 mo7 s5' m8 mo13 s8' FW7
                  ltac:(eapply xpres_weaken; [exact XP8'| clear; lia| intros b Hb; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]) HP8 KREL8
                  ltac:(eapply (mpres_trans H HH); [exact MP7| exact MP8]) (ex_intro _ errv8 ERR8) MI8 ST8 AUX8) as FW8.
    pose proof FW8 as (HP8' & KREL8' & MP8' & _ & _ & _ & _ & _ & DSm8 & DSA8 & _ & _ & _ & [errv8' ERR8'] & LM8 & MI8' & ST8' & AUX8' & _).
    pose proof LM8 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MM8 & MB8 & _).
    assert (BF8 : B64F_fresh TB m8 a (bf_fresh2 Rf mb2)).
    { eapply B64F_fresh_xpres; [exact BF7| exact XP8'| unfold TB, FB, blocks_B64F; apply in_or_app; left; apply in_or_app; left; left; reflexivity
        | unfold TB, FB, blocks_B64F; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity]. }
    assert (EC8 : ENCCTX TB m8 (bf_enc Rf) [] (bf_eid Rf)).
    { eapply ENCCTX_xpres; [exact EC7| exact XP8'| unfold TB, FB, blocks_B64F; apply in_or_app; left; apply in_or_app; left; right; right; left; reflexivity]. }
    assert (MBO8 : MEMBIO TB m8 mb2 M2').
    { eapply (MEMBIO_frame0 TB TB SPc m7 m8); [exact MBO7| intros b Hb; unfold TB; apply in_or_app; right; exact Hb|].
      eapply xpres_weaken; [exact XP8'| clear; lia| intros b Hb; apply in_or_app; left; exact Hb| intros q Hq; exact Hq]. }
    assert (APB : Forall (fun b => Bb + mb_len R <= blk_addr b \/ blk_addr b + blk_size b <= Bb) TB).
    { apply Forall_forall. intros b' Hb'.
      pose proof (perm_split_disjoint H HX _ _ [(pbin, Bb, mb_len R)] (TB ++ (p, A, 512 * (k + 1)) :: L0c) _ _ _ HP8 (Permutation_refl _) (or_introl eq_refl) ltac:(apply in_or_app; left; exact Hb')) as K0.
      cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    pose proof APB as APB'. unfold TB in APB'. apply Forall_app in APB'. destruct APB' as [APBf APBm].
    assert (DAB : A + 512 * (k + 1) <= Bb \/ Bb + mb_len R <= A).
    { pose proof (perm_split_disjoint H HX _ _ [(pbin, Bb, mb_len R)] (TB ++ (p, A, 512 * (k + 1)) :: L0c) _ _ _ HP8 (Permutation_refl _) (or_introl eq_refl)
                    ltac:(apply in_or_app; right; left; reflexivity)) as K0. cbn [blk_addr blk_size fst snd] in K0. clear - K0. lia. }
    assert (MRO : memrd_out mb2 M2' Bb (mb_len R) lo SPc).
    { unfold memrd_out. cbn [mb_buf mb_len M2' mb_with_hdr]. change (blocks_MEMBIO mb2 M2') with MB2. rewrite MBUF, MLEN.
      split; [left; clear - Bb4 CEIL; lia|]. split; [exact Bb1|]. split; [clear - Bb4 HCEILB; lia|]. split; [exact APBm|].
      split; [clear - DAB NA1; lia|]. unfold A_mem_buf_method, O_METH_BREAD. clear - Bb5 L5. lia. }
    clear XP8 XP8' FW7 HP7 KREL7 MP7 ERR7 LM7 MI7' ST7' AUX7 BF7 EC7 MBO7 HP8.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL8| eapply fb_seg7; [clear - Bb1 Bb3 Bb4 HCEILB; lia| exact MI8]|]. intros ms14 ->.
    pose proof bioread_b64_spec as BRD. unfold bioread_b64_stmt in BRD.
    eapply (sr_evt_krel H HH); [exact KREL8| eapply BRD with (LB := TB) (a := a) (mb := mb2) (out := Bb) (outl := mb_len R) (lo := lo) (R := bf_fresh2 Rf mb2) (M := M2') (txt := ds) (junk := junk8); clear BRD;
      lazymatch goal with
      | |- _ = Z_to_bv _ _ => reflexivity
      | |- 0 < mb_len R < _ => clear - L5; lia
      | |- B64F_fresh _ _ _ _ => exact BF8
      | |- ECH_Rep.B64F_apart _ _ => exact BAP
      | |- bf_next _ = _ => reflexivity
      | |- B64F_below _ _ _ => exact BFL
      | |- ENCCTX _ _ _ _ _ => exact EC8
      | |- MEMBIO _ _ _ _ => exact MBO8
      | |- mb_pos _ = 0 => exact MPOS
      | |- MEMBIO_below _ _ _ => exact MBLO
      | |- MEMBIO_sep _ _ => exact MSEP
      | |- bytes_at _ _ _ _ => cbn [mb_buf M2' mb_with_hdr]; rewrite MBUF; exact DSA8
      | |- zlength ds = _ => cbn [mb_len M2' mb_with_hdr]; rewrite MLEN; exact DSL
      | |- zlength ds <= _ => rewrite DSL; clear; lia
      | |- rw_cells _ _ Bb _ => exact CELLS8
      | |- memrd_out _ _ _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact MRO
      | |- Bb + _ <= A_b64_method + _ \/ _ => unfold A_b64_method, O_METH_BREAD; clear - Bb5 L5; lia
      | |- Forall _ (blocks_B64F _ _) => first [exact APBf| exact APM| cbn [mb_buf mb_len M2' mb_with_hdr]; rewrite MBUF, MLEN; eapply Forall_impl; [| exact APf]; cbn beta; intros b0 Hb0; clear - Hb0 NA1; lia| match goal with |- ?G => idtac "FORALLPRE" G end]
      | |- METH_b64 _ => exact MB8
      | |- METH_mem _ => exact MM8
      | |- B64TAB _ => apply B64TAB_of_mem_inv; exact MI8
      | |- stk _ _ _ _ => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); exact ST8'
      | |- hceil <= lo => exact CEIL
      | |- lo <= _ - _ => stack_tac LO STK0 SPR LO0
      | |- mem_inv _ _ => exact MI8
      | |- bv_unsigned _ mod 2 = 0 => reflexivity
      | |- bv_unsigned _ mod 16 = 0 => unfold SP'; rewrite unsigned_lit by (clear - SPR LO STK0 LO0; lia); clear - SPA; Z.div_mod_to_equations; lia
      | |- Bb + _ < 2 ^ 64 => clear - Bb3 Bb4 HCEILB; lia
      | |- ?G => idtac "BRDPRE" G
      end|].
    cbv beta. intros ms15 PO. unfold bioread_b64_post in PO. cbv zeta in PO.
    destruct PO as (r0 & r1 & r2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & r3 & r4 & r5 & r6 & m9 & R9 & d9 & M9 & junk9 & -> & MU9 & WM9 & MI9 & ST9 & BU9 & BLK9 & NX9 & EC9 & MBO9 & MBK9 & MBF9 & MLN9 & MNX9 & DSA9 & OUT9).
    unfold SP' in MU9, ST9. rewrite (unsigned_lit (bv_unsigned sp + -2368)) in MU9, ST9 by (clear - SPR LO STK0 LO0; lia). fold (SP' sp) in MU9, ST9.
    set (res := b64_read_spec (map bv_unsigned ds) (mb_len R)) in *.
    pose proof (fwk_wL ((pbin, Bb, mb_len R) :: TB) p A _ R' j0 j2 (wz n) m8 mo13 s8' m9 _ FW8 MU9 WM9 MI9 ST9
      ltac:(unfold B64F_foot, MEMBIO_foot; cbn [app bf_ctx bf_enc bf_fresh2 mb_bm M2' mb_with_hdr];
            apply Forall_cons; [left; cbn; clear; lia|];
            apply Forall_cons; [right; exists (pbin, Bb, mb_len R); split; [left; reflexivity| cbn; clear; lia]|];
            apply Forall_cons; [right; exists (bf_id Rf, a, BIO_SIZE); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; left; reflexivity| cbn; clear; lia]|];
            apply Forall_cons; [right; exists (bf_cid Rf, bf_ctx Rf, B64CTX_SIZE); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; right; left; reflexivity| cbn; clear; lia]|];
            apply Forall_cons; [right; exists (bf_eid Rf, bf_enc Rf, 92); split; [right; unfold TB, FB, blocks_B64F; apply in_or_app; left; right; right; left; reflexivity| cbn; clear; lia]|];
            apply Forall_cons; [right; exists (mb_id M2, mb2, BIO_SIZE); split; [right; unfold TB, MB2, blocks_MEMBIO; apply in_or_app; right; left; reflexivity| cbn; clear; lia]|];
            apply Forall_cons; [right; exists (mb_bmid M2, mb_bm M2, BUFMEM_SIZE); split; [right; unfold TB, MB2, blocks_MEMBIO; apply in_or_app; right; right; right; left; reflexivity| cbn; clear; lia]| apply Forall_nil])) as FW9.
    pose proof FW9 as (HP9 & KREL9 & MP9 & _ & MST9 & POS9 & NA1' & NA2' & _ & _ & _ & _ & _ & _ & _ & MI9' & _).
    assert (RVF : (br_rv res = Z.of_nat (length (br_out res)) \/ (br_rv res = -1 /\ br_out res = [])) /\ Z.of_nat (length (br_out res)) <= mb_len R)
      by (apply b64_read_rv; clear - L5; lia).
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app usegs m9 Bb [CB (length (br_out res)) (map (Z_to_bv 8) (br_out res))] [CB _ junk9]) OUT9) as [OUTa _].
    destruct (rw_cells_CB_bytes_at _ _ _ _ _ OUTa) as [BS9 _].
    set (bs := map (Z_to_bv 8) (br_out res)) in *.
    assert (ZL : zlength bs = Z.of_nat (length (br_out res))) by (unfold zlength, bs; rewrite length_map; reflexivity).
    (* [comment removed for export] *)
    pose proof BLK9 as BLK9'. unfold blocks_B64F in BLK9'. cbn [bf_id bf_cid bf_eid bf_ctx bf_enc bf_fresh2] in BLK9'. injection BLK9' as Eid Ecid Ectx Eeid Eenc.
    assert (BT9 : chainBT TB a mb2 FB MB2 m9).
    { exists R9, d9, M9. split; [exact BU9|]. split; [exact BLK9|]. split; [exact NX9|]. split; [rewrite Eenc, Eeid; exact EC9|].
      split; [exact MBO9|]. split; [exact MBK9|]. cbn [mb_next M2' mb_with_hdr] in MNX9. rewrite MNX9. exact MNX. }
    (* [comment removed for export] *)
    destruct (blocks_B64F_facts a Rf) as (TL1 & TBY1 & TG1). fold FB in TL1, TBY1, TG1.
    assert (BTR : 0 <= a < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072 /\ lb_big TB <= 1).
    { unfold TB. rewrite length_app, lb_bytes_app, lb_big_app, Nat2Z.inj_add, TL1, TBY1, TG1, MBY, MBL, MBG.
      unfold B64F_BYTES, MEMBIO_BYTES, BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *. clear - APOS AH HCEILB. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (BTF : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
              chainBT TB a mb2 FB MB2 m1 -> xpres L SP X m1 m2 -> (forall b, In b TB -> In b L) -> hceil <= SP ->
              Forall (fun iv : Z * Z => Forall (fun b => blk_addr b + blk_size b <= fst iv \/ snd iv <= blk_addr b) TB) X -> chainBT TB a mb2 FB MB2 m2).
    { intros L1 SP1 X1 ma mb' C1 X2 S1 CE1 F1. eapply chainBT_frame; [exact C1| exact X2| exact S1| exact CE1| exact F1]. }
    destruct (DLOOPB (512 * (k + 1)) (mb_len R) TB ltac:(clear - NA1' NA2' KR; lia) ltac:(unfold OSSL_ECH_MAX_ECHCONFIG_LEN; clear - L5; lia) (proj1 (proj2 BTR)) (proj1 (proj2 (proj2 BTR))) (proj2 (proj2 (proj2 BTR)))) as (B1 & B2 & B3).
    assert (DW9 : DWKG p A (512 * (k + 1)) pbin Bb (mb_len R) bs R' (le8 (wz n) ++ firstn 2040 j2) TB (chainBT TB a mb2 FB MB2) [] [] S M []
                    [CB 48 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 st)] (skipn 2040 j2) m9 mo13 s8').
    { eapply DWKINIT; [exact FW9| exact BS9| exact BT9| unfold OSSL_ECH_MAX_ECHCONFIG_LEN; clear - L5; lia]. }
    clear FW8 HP8' KREL8 KREL8' MP8 MP8' ERR8 ERR8' LM8 MI8 MI8' ST8 ST8' AUX8 AUX8' BF8 EC8 MBO8 MU9 WM9 ST9 OUT9 OUTa CELLS8.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL9| eapply fb_seg8; [clear - RVF L5; lia| exact MI9]|]. intros ms16 ->.
    destruct (Z.leb_spec (br_rv res) 0) as [LE0|GT0].
    - (* [comment removed for export] *)
      eapply (RPTAILXG p A (512 * (k + 1)) pbin Bb (mb_len R) bs R' (le8 (wz n) ++ firstn 2040 j2) a TB (chainBT TB a mb2 FB MB2)) with (line := 631).
      + clear - NA1' NA2' KR. lia.
      + rewrite ZL. unfold OSSL_ECH_MAX_ECHCONFIG_LEN. clear - RVF L5. lia.
      + exact MST9.
      + exact POS9.
      + exact BTR.
      + exact BTF.
      + apply btfree_chain.
      + exact DW9.
      + reflexivity.
      + clear. lia.
      + unfold FB_631_R1. clear. lia.
      + reflexivity.
      + exact fb_631g.
      + clear - B1 B2 B3. clearbody TB. unfold dbud, drest. cbn [app]. rewrite !lb_bytes_app, !lb_bytes_cons, !lb_big_app, !lb_big_cons, !length_app. cbn [length blk_size snd].
        rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ. unfold ERRDEBUG_BYTES, DLOOP_BYTES, DLOOP_CNT, DLOOP_BIG in *. lia.
    - (* [comment removed for export] *)
      replace (Z_to_bv 64 (br_rv res) : word) with (Z_to_bv 64 (zlength bs) : word) by (rewrite ZL; f_equal; clear - RVF GT0; lia).
      eapply (RPFLAT p A (512 * (k + 1)) pbin Bb (mb_len R) bs R' (le8 (wz n) ++ firstn 2040 j2) a TB (chainBT TB a mb2 FB MB2)).
      + clear - NA1' NA2' KR. lia.
      + rewrite ZL. unfold OSSL_ECH_MAX_ECHCONFIG_LEN. clear - RVF L5. lia.
      + exact MST9.
      + exact POS9.
      + exact BTR.
      + exact BTF.
      + exact TIME.
      + apply RPE; [clear - NA1' NA2' KR; lia| rewrite ZL; unfold OSSL_ECH_MAX_ECHCONFIG_LEN; clear - RVF L5; lia| exact MST9| exact POS9| exact BTR| exact BTF].
      + apply btfree_chain.
      + exact B1.
      + exact B2.
      + exact B3.
      + exact DW9.
  Qed.
End RC.
