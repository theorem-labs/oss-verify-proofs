(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_ctrl W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition BIO_VPRINTF : Z := 0x23adb8.
Definition BVPF_SS1_RA : Z := 0x23aee0.   (* [comment removed for export] *)
Definition BVPF_SS2_RA : Z := 0x23af18.   (* [comment removed for export] *)
Definition BVPF_VSN_RA : Z := 0x23af34.   (* [comment removed for export] *)
Definition BVPF_BW_RA  : Z := 0x23afac.   (* [comment removed for export] *)
Definition BVPF_SS3_RA : Z := 0x23afbc.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_VPRINTF_NULL_STACK : Z := BVPF_FRAME + BIO_WRITE_NULL_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition vfmtA_ok (A : Z) (fmt : list Z) (args : list parg) (o : list Z) : Prop :=
  ro_bytes ctasegs A (zb fmt) /\ Forall (fun c => 0 <= c < 256) fmt
  /\ 0x10000 <= A /\ A + zlength fmt <= STATIC_SPLIT
  /\ (forall (AR' : ARun) (Σ' : rts (@ar_RT AR')) OW' LB' m', @BnHeapA.AHEAP AR' Σ' OW' LB' m' -> acc ctasegs m' A (zlength fmt))
  /\ pass1x_ok fmt = true
  /\ printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o))
  /\ fp_callsx (length fmt) fmt args = []
  /\ pcomx_ok fmt args = true
  /\ fmtz_ok fmt = true.

Lemma vfmtA_vfmt : forall (AR' : ARun) Σ' OW' LB' m' A fmt args o,
  vfmtA_ok A fmt args o -> @BnHeapA.AHEAP AR' Σ' OW' LB' m' -> mem_inv ctasegs m' -> vfmt_ok m' A fmt args o.
Proof.
  intros AR' Σ' OW' LB' m' A fmt args o (RO & FA & A1 & A2 & ACC & P1 & P2 & P3 & P4 & P5) HEAP MI. unfold vfmt_ok.
  split; [| split; [exact FA| split; [exact A1| split; [exact A2| split; [exact (ACC AR' Σ' OW' LB' m' HEAP)| split; [exact P1| split; [exact P2| split; [exact P3| split; [exact P4| exact P5]]]]]]]]].
  apply (ro_bytes_at ctasegs m' A _ MI); [lia| | exact RO]. unfold zb. rewrite length_map. unfold zlength, STATIC_SPLIT in A2. lia.
Qed.

(* [comment removed for export] *)
Definition vargA_ok (OW LB : list block) (m : mem) (slot : word) (a : parg) : Prop :=
  match a with
  | PA_s s => exists slack : list byte,
      Forall (fun c => 0 < c < 256) s /\ zlength s + 1 <= 2^40
      /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
      /\ ( (exists b, In b (OW ++ LB) /\ blk_addr b <= bv_unsigned slot
                    /\ bv_unsigned slot + zlength s + 1 + zlength slack <= blk_addr b + blk_size b
                    /\ bytes_at ctasegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack))
         \/ (0x10000 <= bv_unsigned slot /\ bv_unsigned slot + zlength s + 1 + zlength slack <= SEGTOP_A
             /\ ro_bytes ctasegs (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
             /\ forall (AR' : ARun) (Σ' : rts (@ar_RT AR')) m', @BnHeapA.AHEAP AR' Σ' OW LB m' -> acc ctasegs m' (bv_unsigned slot) (zlength s + 1)) )
  | PA_sn => bv_unsigned slot = 0
  | PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
  | PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
  | PA_z u => bv_unsigned slot = u
  | PA_g _ => False
  end.
Fixpoint vargsA_ok (OW LB : list block) (m : mem) (slots : list word) (args : list parg) : Prop :=
  match args with
  | [] => True
  | a :: args' => match slots with
                  | [] => False
                  | w :: slots' => vargA_ok OW LB m w a /\ vargsA_ok OW LB m slots' args'
                  end
  end.

(* [comment removed for export] *)
Lemma vargsA_ok_agree : forall OW LB m m' slots args,
  vargsA_ok OW LB m slots args -> agree_on (in_block (OW ++ LB)) m m' -> vargsA_ok OW LB m' slots args.
Proof.
  intros OW LB m m' slots args. revert slots. induction args as [|a args IH]; intros slots H AG; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH slots H2 AG)].
  destruct a; try exact H1. destruct H1 as (slack & F1 & L1 & P1 & [(b & Hb & R1 & R2 & HB)|HI]); exists slack.
  - split; [exact F1|]. split; [exact L1|]. split; [exact P1|]. left. exists b. split; [exact Hb|]. split; [exact R1|]. split; [exact R2|].
    eapply bytes_at_agree; [exact AG| exact HB|]. intros x Hx. exists b. split; [exact Hb|]. rewrite length_app in Hx. cbn [length] in Hx. unfold zb in Hx. rewrite length_map in Hx. unfold zlength in R2. lia.
  - split; [exact F1|]. split; [exact L1|]. split; [exact P1|]. right. exact HI.
Qed.

(* [comment removed for export] *)
Lemma vargsA_vargs : forall (AR' : ARun) (Σ' : rts (@ar_RT AR')) OW LB m' (sp : word) lo D nD f k slots args,
  @BnHeapA.AHEAP AR' Σ' OW LB m' -> mem_inv ctasegs m' -> @BnHeapA.ACEIL AR' <= lo ->
  (forall b, In b (OW ++ LB) -> off_fr f k b) -> SEGTOP_A <= f -> f <= D -> D + nD <= f + fs_size k ->
  vargsA_ok OW LB m' slots args -> vargs_ok (@ar_RT AR') Σ' m' sp lo D nD slots args.
Proof.
  intros AR' Σ' OW LB m' sp lo D nD f k slots args HEAP MI CEIL OFF GF D1 D2. revert slots.
  pose proof (@AH_ceil AR' _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  induction args as [|a args IH]; intros slots H; [destruct slots; exact I|].
  destruct slots as [|w slots]; [exact H|]. destruct H as [H1 H2]. split; [| exact (IH slots H2)].
  destruct a; try exact H1. destruct H1 as (slack & F1 & L1 & P1 & [(b & Hb & R1 & R2 & HB)|(I1 & I2 & RO & ACC)]); exists slack.
  - pose proof (@AH_range_gen AR' _ _ _ _ b HEAP Hb) as (B0 & _ & _ & B3 & B4). pose proof (OFF b Hb) as O. unfold off_fr in O.
    destruct (@AH_acc AR' _ _ _ _ b HEAP Hb) as [_ ACCB].
    pose proof (@AH_rng AR' _ _ _ _ (bv_unsigned sp) b (bv_unsigned w) (zlength s + 1) HEAP Hb R1 ltac:(unfold zlength in *; lia)) as [RC _].
    split; [exact HB|]. split; [exact F1|]. split; [exact L1|]. split; [exact P1|].
    unfold USTACK_TOP, BnHeapA.ACEIL in *. unfold zlength in *.
    split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
    split; [| exact RC]. eapply acc_sub; [exact ACCB| lia| lia].
  - split; [apply (ro_bytes_at ctasegs m' _ _ MI); [lia| | exact RO]; rewrite length_app; cbn [length]; unfold zb; rewrite length_map; unfold zlength, SEGTOP_A in *; lia|].
    split; [exact F1|]. split; [exact L1|]. split; [exact P1|]. unfold SEGTOP_A, USTACK_TOP, BnHeapA.ACEIL in *. unfold zlength in *.
    split; [lia|]. split; [lia|]. split; [left; lia|]. split; [lia|].
    split; [exact (ACC AR' Σ' m' HEAP)|]. right; right; right. unfold SEGTOP_A. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_mid_update : forall (m m' : mem) S (hd tl : list cell) (nmid : nat) (jm : list byte) (v : Z) (P : Z -> Prop),
  rw_cells ctasegs m S (hd ++ CB nmid jm :: tl) ->
  agree_on (fun a => P a /\ ~ (S + Z.of_nat (cells_size hd) <= a < S + Z.of_nat (cells_size hd) + Z.of_nat nmid)) m m' ->
  (forall a, S <= a < S + Z.of_nat (cells_size (hd ++ CB nmid jm :: tl)) -> P a) ->
  bytes_at ctasegs m' (S + Z.of_nat (cells_size hd)) (repeat (Z_to_bv 8 v) nmid) ->
  wr_at ctasegs m' (S + Z.of_nat (cells_size hd)) (Z.of_nat nmid) ->
  rw_cells ctasegs m' S (hd ++ CB nmid (repeat (Z_to_bv 8 v) nmid) :: tl).
Proof.
  intros m m' S hd tl nmid jm v P H AG HP HB HW.
  pose proof (rw_cells_app_l m S hd _ H) as H1.
  pose proof (rw_cells_skip m S (hd ++ [CB nmid jm]) tl _ ltac:(rewrite <- app_assoc; exact H) eq_refl) as H3.
  rewrite cells_size_app in H3. cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  apply rw_cells_app_join.
  - eapply rw_cells_agree; [exact AG| exact H1|]. intros a Ha. split; [apply HP; rewrite cells_size_app; cbn [cells_size csize]; lia| lia].
  - change (CB nmid (repeat (Z_to_bv 8 v) nmid) :: tl) with ([CB nmid (repeat (Z_to_bv 8 v) nmid)] ++ tl). apply rw_cells_app_join.
    + split; [split; [cbn; split; [rewrite repeat_length; reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]|].
      cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HW.
    + cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. rewrite Nat2Z.inj_add, Z.add_assoc in H3. eapply rw_cells_agree; [exact AG| exact H3|].
      intros a Ha. split; [apply HP; rewrite cells_size_app; cbn [cells_size csize]; lia| lia].
Qed.

(* [comment removed for export] *)
Definition vsn_postA (AR' : ARun) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts (@ar_RT AR')) (OW LB : list block) (lo D : Z) (o : list Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength o)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ @BnHeapA.AHEAP AR' Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => (aclient_addr (OW ++ LB) (bv_unsigned sp) a \/ @fr_addr AR' a) /\ ~ (D <= a < D + (zlength o + 1))) m m'
    /\ bytes_at ctasegs m' D (zb o ++ [Z_to_bv 8 0]).

(* [comment removed for export] *)
Lemma vsnprintf_cpsA : forall (AR' : ARun) (PFC' : printf_contracts (@ar_RT AR'))
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR')) (OW LB : list block) (lo D nD A VA f : Z) (k : nat)
    (fmt : list Z) (slots : list word) (args : list parg) (o : list Z),
  @BnHeapA.AHEAP AR' Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> @BnHeapA.ACEIL AR' <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In (f, k) (@ar_FR AR') -> (forall b, In b (OW ++ LB) -> off_fr f k b) -> f <= D -> D + nD <= f + fs_size k - 8 ->
  acc ctasegs m D nD ->
  vfmtA_ok A fmt args o -> zlength o <= nD - 1 -> 1 <= nD -> nD < 2^31 ->
  va_area m VA slots -> bv_unsigned sp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 -> vargsA_ok OW LB m slots args ->
  a0 = wz D -> a1 = wz nD -> a2 = wz A -> a3 = wz VA ->
  cps ctasegs (ASTA (@ar_RT AR') Σ (@ar_PMc AR') (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz e_vsnprintf) fc None m (seg_rom ctasegs))))
      (ASTA (@ar_RT AR') Σ (@ar_PMc AR') (vsn_postA AR' ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo D o m)).
Proof.
  intros until o. intros HEAP ST CEIL LO SPT SP16 MI -> Hf OFF D1 D2 ACC VF OLEN N1 N2 VAA VA1 VA2 VARGS -> -> -> ->.
  unfold MallocRep.wz in *.
  pose proof (@AH_ceil AR' _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (@AH_frames AR' _ _ _ _ HEAP) as EFR.
  destruct (@AH_fr_geo AR' _ _ _ _ f k HEAP Hf) as (G1 & G2 & G3 & G4 & G5). unfold SEGTOP_A in G4.
  destruct (@AH_fr_wr AR' _ _ _ _ f k HEAP Hf) as [WF _].
  eapply cps_conseq; [ eapply (rc_vsnprintf _ PFC' Σ (@ar_PMc AR')) with (D := D) (n := nD) (A := A) (VA := VA) (fmt := fmt) (slots := slots) (args := args) (o := o) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact (@ar_PMc_fdfs AR').
  - exact (@ar_PMc_ms AR').
  - exact (vfmtA_vfmt AR' Σ OW LB m A fmt args o VF HEAP MI).
  - exact VAA.
  - exact VA1.
  - exact VA2.
  - left. unfold BnHeapA.ACEIL, RT_STACK in *. lia.
  - apply vargs_ok_okx. eapply (vargsA_vargs AR' Σ OW LB m sp lo D nD f k); [exact HEAP| exact MI| exact CEIL| exact OFF| unfold SEGTOP_A; exact G4| exact D1| lia| exact VARGS].
  - exact N1.
  - exact N2.
  - exact OLEN.
  - lia.
  - unfold BnHeapA.ACEIL, USTACK_TOP in *. lia.
  - right. unfold SEGTOP_A. lia.
  - split; [| split].
    + intros _. split; [exact ACC|]. right; left. exists f, k. rewrite EFR. split; [exact Hf| lia].
    + intros i Hi. right; right; right; left. rewrite EFR. exists f, k. split; [exact Hf| lia].
    + destruct WF as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros i Hi. replace (D + i) with (f + (D - f + i)) by lia. apply W3. lia.
  - exact (@AH_art AR' _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply (@call_okA AR'); [exact HEAP | exact ST | exact CEIL | exact LO | unfold USTACK_TOP; lia | exact SP16].
  - intros c Hc. eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EFR in PRES.
    assert (AGX : agree_on (fun a => (aclient_addr (OW ++ LB) (bv_unsigned sp) a \/ @fr_addr AR' a) /\ ~ (D <= a < D + (zlength o + 1))) m m2).
    { intros a Ha [[Hc|[Hc|Hc]] Hd]; apply PRES; unfold wa; rewrite unsigned_lit by lia;
        [exact (@AH_aclient AR' _ _ _ _ _ _ HEAP Hc) | exact Hd | right; right; right; left; exact Hc | exact Hd | right; right; right; right; exact Hc | exact Hd]. }
    unfold vsn_postA, MallocRep.wz. do 16 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply (@AH_same_ex AR'); [exact HEAP| exact ART2| exact WM2| rewrite (@AH_frames AR' _ _ _ _ HEAP); exact PRES| unfold SHLO, SHHI; lia]. }
    split; [exact WM2|]. split; [exact AGX|]. exact BZ.
Qed.

(* [comment removed for export] *)
Definition bio_vprintf_null_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (out pv nw n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres_ex LB OW (bv_unsigned sp) [(out, out + BIO_SIZE)]%Z m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv (nw + n)).

Section WithPFC.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Lemma BIO_vprintf_null_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (pb : bptr) (out pv nw A VA : Z)
    (fmt : list Z) (slots : list word) (args : list parg) (o : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BIO_VPRINTF_NULL_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (length FR) < FRAMES_MAX)%nat -> 2 <= rt_credit RT Σ ->
  In (pb, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
  vfmtA_ok A fmt args o -> 0 < zlength o < 512 ->
  va_area m VA slots -> bv_unsigned sp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 -> vargsA_ok OW LB m slots args ->
  a0 = wz out -> a1 = wz A -> a2 = wz VA ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_VPRINTF) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_vprintf_null_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB out pv nw (zlength o) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until o. intros HEAP ST CEIL LO SPT SP16 MI TP FLEN CRED HBIN HO NW0 VF OLEN VAA VA1 VA2 VARGS -> -> ->.
  unfold BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BVPF_FRAME, BWI_FRAME, RT_STACK, BIO_VPRINTF, BIO_SIZE, MallocRep.wz in *.
  remember (zlength o) as n eqn:En.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT, VA2.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (AH_offsh _ _ _ _ _ HEAP HBIN') as OFFO. cbn [blk_addr blk_size fst snd] in OFFO. unfold SHLO, SHHI in OFFO.
  unfold bio_null_cells, bio_cells, MallocRep.wz in HO.
  (* [comment removed for export] *)
  eapply (bvpf_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold BVPF_FRAME, RT_STACK; clear - LO; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI | exact TP | clear - FLEN; lia | clear - CRED; lia |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold BVPF_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 4) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 4) with 1024 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 128 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)) as DP.
    assert (DQ : f / 8 + 128 <= 2 ^ 44).
    { assert (DR : f / 8 < 2 ^ 44 - 128); [apply Z.div_lt_upper_bound; [clear; lia|]; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; clear - G3 D3; lia | clear - DR; lia]. }
    clear - DP DQ; lia. }
  assert (ESH12 : bv_unsigned (Z_to_bv 64 (shad f + 12)) = shad f + 12) by (apply unsigned_lit; clear - SHR; lia).
  pose proof (FRESH _ HBIN') as OFFB. unfold off_fr in OFFB. cbn [blk_addr blk_size fst snd] in OFFB. change (fs_size 4) with 1024 in OFFB.
  assert (BLK : forall a lo' hi', in_block (OW ++ LB) a -> (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                 (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')).
  { intros a lo' hi' (b & Hb & Hr) Hlh. split; [left; right; right; exists b; split; [exact Hb| exact Hr]|].
    pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 4) with 1024 in O.
    pose proof (AH_offsh _ _ _ _ _ HEAP Hb) as OS. unfold SHLO, SHHI in OS. clear - Hr Hlh O OS SHR. lia. }
  assert (BLKW : forall W m1 m2, munch W m1 m2 -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                 agree_on (in_block (OW ++ LB)) m1 m2).
  { intros W m1 m2 MU HW. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. clear MU. intros a Ha.
    induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [outside fst snd] in H1 |- *.
    split; [exact (proj2 (BLK a lo' hi' Ha H1))| exact (IH H2)]. }
  assert (ACL : forall a lo' hi', aclient_addr (OW ++ LB) (bv_unsigned sp) a -> (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                 (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')).
  { intros a lo' hi' [Hs|[Hst|Hb]] Hlh.
    - split; [left; left; clear - Hs SPAH; lia| clear - Hs Hlh SHR G3 CEIL LO D2; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia].
    - split; [left; right; left; exact Hst|]. destruct Hst as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
      clear - Hin Hr Hlh G4 SHR. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    - exact (BLK a lo' hi' Hb Hlh). }
  assert (ACLW : forall W m1 m2, munch W m1 m2 -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                 agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m1 m2).
  { intros W m1 m2 MU HW. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. clear MU. intros a Ha.
    induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [outside fst snd] in H1 |- *.
    split; [exact (proj2 (ACL a lo' hi' Ha H1))| exact (IH H2)]. }
  apply (rw_cells_agree _ _ _ _ _ AGF) in HO; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply (bytes_at_agree _ _ _ _ _ AGF) in VAA; [| intros a Ha; rewrite u64s_length in Ha; left; unfold USTACK_TOP; clear - Ha VA1 VA2; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m m3 slots args H (agree_on_mono _ _ _ _ AGF ltac:(intros a Ha; right; right; exact Ha))) in VARGS.
  pose proof (munch_refl [(spa, spa)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  assert (OFFL : forall b, In b LB -> off_fr f 4 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 248) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  intros msb (v0 & v1 & v2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & Fb & fcb & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ4 & WR4).
  rewrite ?ESPA in *. unfold BVPF_SS1_RA, MallocRep.wz. rewrite (ret_pc_even 0x23aee0) by (clear; lia).
  (* [comment removed for export] *)
  assert (STK4 : forall x, spa <= x < 140737488355328 -> (aclient_addr (OW ++ LB) spa x \/ @fr_addr (push AR f 4) x) /\ ~ (shad f + 12 <= x < shad f + 12 + 64)).
  { intros x Hx. split; [left; left; unfold USTACK_TOP; exact Hx| clear - Hx SHR D2 CEIL LO SPAL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]. }
  apply (rw_cells_agree _ _ _ _ _ AG4) in HO; [| intros a Ha; cbn in Ha; split; [left; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]| clear - Ha OFFO SHR; lia]].
  apply (bytes_at_agree _ _ _ _ _ AG4) in VAA; [| intros a Ha; rewrite u64s_length in Ha; apply STK4; clear - Ha VA1 VA2 SPAH; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m3 m4 slots args H (agree_on_mono _ _ _ _ AG4 ltac:(intros a Ha; apply BLK; [exact Ha| left; clear; lia]))) in VARGS.
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; clear - Ha; lia]| clear - Ha SHR G5; lia]].
  unfold bvpf_shadow_pro in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242)]
           116 jst [] [64; 1; 1; 1; 1; 1; 1; 1; 1; 44]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 64 ?jm :: ?tl) =>
    apply (shadow_mid_update m3 m4 (shad f) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] tl 64 jm 248 (fun a => aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a)) in FRS;
    [| cbn [cells_size csize Nat.add]; exact AG4
     | intros a Ha; cbn [cells_size csize Nat.add app] in Ha; right; right; exists f, 4%nat; split; [left; reflexivity| rewrite shad_fr_end; change (fs_size 4 / 8) with 128; clear - Ha; lia]
     | cbn [cells_size csize Nat.add]; exact BZ4 | cbn [cells_size csize Nat.add]; exact WR4 ] end.
  cbn [app] in FRS.
  pose proof (munch_refl [(f + 32, f + 40); (f + 64, f + 72); (shad f + 8, shad f + 9); (shad f + 76, shad f + 84)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4'.
  clear MU3 WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. do 8 sbstep.
  step. sbstep.
  (* [comment removed for export] *)
  step. step. step.
  name_mem m5.
  match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
  assert (FRW5 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(f + 32, f + 40); (f + 64, f + 72); (shad f + 8, shad f + 9); (shad f + 76, shad f + 84)]%Z).
  { change (fs_size 4) with 1024. clear.
    constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; lia|]. constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; lia|].
    constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; lia|]. constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; lia| constructor]. }
  assert (HEAP5 : @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m5).
  { eapply (@AH_frame_fr (push AR f 4) Σ1 OW LB m4 m5 _ f 4%nat (or_introl eq_refl) HEAP4 MU5 WM5 FRW5 OFFL). }
  apply (fun H => vargsA_ok_agree OW LB m4 m5 slots args H (BLKW _ m4 m5 MU5 ltac:(clear; repeat constructor; cbn [fst snd]; lia))) in VARGS.
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 0) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  intros msc (v0' & v1' & v2' & w0' & w1' & w2' & w3' & w4' & w5' & w6' & w7' & v3' & v4' & v5' & v6' & Fc & fcc & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ6 & WR6).
  rewrite ?ESPA in *. unfold BVPF_SS2_RA, MallocRep.wz. rewrite (ret_pc_even 0x23af18) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG6) in HO; [| intros a Ha; cbn in Ha; split; [left; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]| clear - Ha OFFO SHR; lia]].
  apply (bytes_at_agree _ _ _ _ _ AG6) in VAA; [| intros a Ha; rewrite u64s_length in Ha; apply STK4; clear - Ha VA1 VA2 SPAH; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m5 m6 slots args H (agree_on_mono _ _ _ _ AG6 ltac:(intros a Ha; apply BLK; [exact Ha| left; clear; lia]))) in VARGS.
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; clear - Ha; lia]| clear - Ha SHR G5; lia]].
  lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 64 ?jm :: ?tl) =>
    apply (shadow_mid_update m5 m6 (shad f) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] tl 64 jm 0 (fun a => aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a)) in FRS;
    [| cbn [cells_size csize Nat.add]; exact AG6
     | intros a Ha; cbn [cells_size csize Nat.add app] in Ha; right; right; exists f, 4%nat; split; [left; reflexivity| rewrite shad_fr_end; change (fs_size 4 / 8) with 128; clear - Ha; lia]
     | cbn [cells_size csize Nat.add]; exact BZ6 | cbn [cells_size csize Nat.add]; exact WR6 ] end.
  cbn [app] in FRS.
  pose proof (munch_refl [(f + 64, f + 72)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6'.
  try clear MU4; try clear WM4'. clear WM5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step.
  name_mem m7.
  match goal with H : munch _ m6 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m6 m7 |- _ => rename H into WM7 end.
  assert (FRW7 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(f + 64, f + 72)]%Z).
  { constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; clear; lia| constructor]. }
  assert (HEAP7 : @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m7).
  { eapply (@AH_frame_fr (push AR f 4) Σ1 OW LB m6 m7 _ f 4%nat (or_introl eq_refl) HEAP6 MU7 WM7 FRW7 OFFL). }
  apply (fun H => vargsA_ok_agree OW LB m6 m7 slots args H (BLKW _ m6 m7 MU7 ltac:(clear; repeat constructor; cbn [fst snd]; lia))) in VARGS.
  (* [comment removed for export] *)
  assert (ACCB : acc ctasegs m7 (f + 96) 512).
  { eapply (acc_of_shadow_cells m7 (shad f) _ 12 (f + 96) 512 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
      | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity]. }
  apply evt_done. eapply cps_step_same.
  { eapply (vsnprintf_cpsA (push AR f 4) PFC) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (D := f + 96) (nD := 512) (A := A) (VA := VA) (fmt := fmt) (slots := slots) (args := args) (o := o);
      try reflexivity; rewrite ?ESPA;
      [exact HEAP7| assumption| exact CEIL| unfold RT_STACK in *; clear - LO SPAL; lia| unfold USTACK_TOP; clear - SPT SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia
      | assumption| cbn [ar_FR push amb]; left; reflexivity| exact FRESH| clear; lia| change (fs_size 4) with 1024; clear; lia| exact ACCB| exact VF
      | rewrite <- En; clear - OLEN; lia| clear; lia| exact VAA| clear - VA1 SPAH SPAL; lia| unfold USTACK_TOP; clear - VA2; lia| exact VARGS]. }
  intros msd (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fd & fcd & m8 & -> & MI8 & ST8 & HEAP8 & WM8 & AG8 & BZ8).
  rewrite <- ?En in *. rewrite ?ESPA in *. unfold MallocRep.wz. rewrite (ret_pc_even 0x23af34) by (clear; lia).
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG8) in HO; [| intros a Ha; cbn in Ha; apply BLK; [exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]| right; clear - OLEN; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply STK4; clear - Ha GSZ SPT SPAH; lia| clear - Ha G3 CEIL LO SPAL GSZ OLEN; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply STK4; clear - Ha SPT SPAH; lia| clear - Ha G3 CEIL LO SPAL SPAH OLEN; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  clear VAA FRF FRS ACCB.
  pose proof (munch_refl []%Z m8) as MU8. pose proof (wmono_refl ctasegs m8) as WM8'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. if_cases Hqn; zify_cond Hqn; [exfalso; clear - Hqn OLEN; lia|]. clear Hqn.
  step. step. if_cases Hqm; zify_cond Hqm; [| exfalso; clear - Hqm OLEN; lia]. clear Hqm.
  step. step. step.
  (* [comment removed for export] *)
  apply evt_done. eapply cps_step_rt.
  { pose proof (@BIO_write_null_cpsA (push AR f 4)) as HP. cbn [ar_RT ar_PMc ar_FR push amb] in HP.
    eapply HP with (lo := lo) (OW := OW) (LB := LB) (pb := pb) (out := out) (pv := pv) (nw := nw) (dlen := n); clear HP; rewrite ?ESPA;
      [exact HEAP8| exact ST8| exact CEIL| unfold BIO_WRITE_NULL_STACK, BWI_FRAME, RT_STACK; clear - LO SPAL; lia| unfold USTACK_TOP; clear - SPT SPAH; lia
      | clear - SPA32; Z.div_mod_to_equations; lia| exact MI8| reflexivity| cbn [length]; exact FLEN| rewrite CR1; clear - CRED; lia| exact HBIN| exact HO| exact NW0
      | reflexivity| reflexivity| clear - OLEN; lia]. }
  clear MU8 WM8'. intros Σ2 mse PO EL2. cbv beta in PO.
  destruct PO as (y0' & y1' & y2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & y3' & y4' & y5' & y6' & Fe & fce & m9 & -> & MI9 & ST9 & APX9 & HEAP9 & EL9 & CR9 & HB9).
  unfold MallocRep.wz in *. rewrite (ret_pc_even 0x23afac) by (clear; lia). rewrite ?ESPA in *.
  unfold apres_ex in APX9. cbn [outside fst snd] in APX9.
  assert (STW9 : forall a, spa <= a < 140737488355328 -> aclient_addr (OW ++ LB) spa a /\ (~ (out <= a < out + 128) /\ True)).
  { intros a Ha. split; [left; exact Ha|]. split; [clear - Ha BB3 D3 CEIL LO SPAL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia| exact I]. }
  apply (rw_cells_agree _ _ _ _ _ APX9) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW9; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ APX9) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW9; clear - Ha SPT SPAH; lia].
  clear HO. unfold bio_null_cells, bio_cells, MallocRep.wz in HB9.
  pose proof (munch_refl []%Z m9) as MU9. pose proof (wmono_refl ctasegs m9) as WM9'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step.
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 248) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  clear MU9 WM9'. intros msg (v0'' & v1'' & v2'' & w0'' & w1'' & w2'' & w3'' & w4'' & w5'' & w6'' & w7'' & v3'' & v4'' & v5'' & v6'' & Fg & fcg & m10 & -> & MI10 & ST10 & HEAP10 & WM10 & AG10 & BZ10 & WR10).
  rewrite ?ESPA in *. unfold BVPF_SS3_RA, MallocRep.wz. rewrite (ret_pc_even 0x23afbc) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG10) in HB9; [| intros a Ha; cbn in Ha; apply BLK; [exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]| left; clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG10) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG10) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  (* [comment removed for export] *)
  destruct (@AH_fr_wr (push AR f 4) _ _ _ _ f 4%nat HEAP10 (or_introl eq_refl)) as [_ WS10]. change (fs_size 4) with 1024 in WS10.
  destruct (wr_at_rw_CB m10 (shad f) _ WS10 ltac:(clear; lia)) as (js10 & FRS10). change (Z.to_nat (1024 / 8)) with 128%nat in FRS10.
  apply (rw_cells_split_CB ctasegs _ _ [] 128 _ [] [8; 1; 119]%nat) in FRS10; [| reflexivity]. cbn [mk_CB_cells app] in FRS10.
  pose proof (munch_refl [(shad f + 8, shad f + 9)]%Z m10) as MU10. pose proof (wmono_refl ctasegs m10) as WM10'.
  apply cps_from_evt'.
  sbstep.
  name_mem m11.
  match goal with H : munch _ m10 m11 |- _ => rename H into MU11 end. match goal with H : wmono ctasegs m10 m11 |- _ => rename H into WM11 end.
  assert (FRW11 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(shad f + 8, shad f + 9)]%Z).
  { constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; clear; lia| constructor]. }
  assert (HEAP11 : @BnHeapA.AHEAP (push AR f 4) Σ2 OW LB m11).
  { eapply (@AH_frame_fr (push AR f 4) Σ2 OW LB m10 m11 _ f 4%nat (or_introl eq_refl) HEAP10 MU11 WM11 FRW11 OFFL). }
  (* [comment removed for export] *)
  apply evt_done.
  eapply (bvpf_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []); rewrite ?ESPA;
    [exact HEAP11 | exact OFFL | assumption | exact CEIL | clear - LO SPAL; lia | unfold RT_STACK; clear - LO SPAL; lia | exact SPA32 | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | assumption | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' F3 fc3 HEAP' CR' EL' ST' MI' AG'.
  apply (rw_cells_agree _ _ _ _ _ AG') in HB9; [| intros a Ha; cbn in Ha; right; right; exists (pb, out, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL9, EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_vprintf_null_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { (* [comment removed for export] *)
    unfold apres_ex. cbn [outside fst snd].
    assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    assert (STEPA : forall (mA mB : mem) lo' hi', agree_on (fun a => (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')) mA mB ->
                    (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                    agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ (~ (out <= a < out + 128) /\ True)) mA mB).
    { intros mA mB lo' hi' AGx Hlh. eapply agree_on_mono; [exact AGx|]. intros a [Ha _]. exact (ACL a lo' hi' Ha Hlh). }
    assert (STEPW : forall (mA mB : mem) W, munch W mA mB -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                    agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ (~ (out <= a < out + 128) /\ True)) mA mB).
    { intros mA mB W MU HW. eapply agree_on_mono; [exact (ACLW W mA mB MU HW)|]. intros a [Ha _]. exact Ha. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply (STEPA m3 m4); [exact AG4| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m4 m5); [exact MU5| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_trans; [eapply (STEPA m5 m6); [exact AG6| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m6 m7); [exact MU7| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_trans; [eapply (STEPA m7 m8); [exact AG8| right; clear - OLEN; lia]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact APX9|]; intros a [Ha Hx]; split; [eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia| exact Hx]|].
    eapply agree_on_trans; [eapply (STEPA m9 m10); [exact AG10| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m10 m11); [exact MU11| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL9, EL1; reflexivity|]. split; [rewrite CR'; clear - CR9 CR1; cbn [ar_RT push amb] in *; lia|].
  unfold bio_null_cells, bio_cells, MallocRep.wz. exact HB9.
Qed.
End WithPFC.

End WithRT.
