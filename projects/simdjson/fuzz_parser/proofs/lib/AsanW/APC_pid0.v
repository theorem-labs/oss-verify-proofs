(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface I_asan_memset AU_rt AH_memcpy0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit AU_parts_iface AU_steptac Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import ShadowTac APC_kit APC_kit2 APC_kit3 APC_kit4 APC_docalloc APC_setcap APC_setdepth APC_active APC_create APC_dtor APC_memcmp APC_s12iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_mpres.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition APID : Z := 0x95d34.
Definition APID_STACK : Z := 112 + APARSE_STACK.

(* [comment removed for export] *)


Lemma ablock_range_lin : forall A n, ablock_range A n -> 6705152 <= A /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.
Proof. intros A n (B & H1 & H2 & H3). pose proof (ablk_lin _ _ B) as (X1 & _). unfold AIMG_HI in X1. repeat split; lia. Qed.

(* [comment removed for export] *)
Lemma unpoisoned_two : forall m X, X mod 8 = 0 -> 0 <= X -> X + 16 <= 2^47 ->
  rw_cells asegs m (Z.shiftr X 3 + 2147450880) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (Z.shiftr (X + 8) 3 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  unpoisoned m X (X + 16).
Proof.
  intros m X H8 H0 H47 C0 C1. rewrite !Z.shiftr_div_pow2 in C0, C1 by lia. change (2 ^ 3) with 8 in C0, C1.
  apply byte_of_c1 in C0; [| Z.div_mod_to_equations; lia]. apply byte_of_c1 in C1; [| Z.div_mod_to_equations; lia].
  split; [lia|]. split; [lia|]. intros G G0 G1 G2.
  assert (E : G = X / 8 \/ G = (X + 8) / 8) by (Z.div_mod_to_equations; lia).
  exists (Z_to_bv 8 0). split; [| left; apply sval_zero].
  unfold ASHOFF. destruct E as [-> | ->]; rewrite Z.add_comm; assumption.
Qed.

(* [comment removed for export] *)
Lemma implMA_retb : forall {A B} RNG (a : A) (f : A -> MA B) s Q ms, implMA RNG (f a) s Q ms -> implMA RNG (mbind (mret a) f) s Q ms.
Proof.
  intros A B RNG a f s Q ms H.
  eapply (implMA_bind RNG (mret a) f s (fun a' s' R' ms' => a' = a /\ s' = s /\ R' = RNG /\ ms' = ms)).
  - apply implMA_ret. apply evtF_done. auto.
  - intros a' s' R' ms' (-> & -> & -> & ->). exact H.
Qed.
Lemma implMA_map_some : forall {A B} RNG (m : MA A) (k : option A -> MA B) s Q ms (Q1 : A -> APS -> footprint -> machine_state -> Prop),
  implMA RNG m s Q1 ms -> (forall a s' R' ms', Q1 a s' R' ms' -> implMA R' (k (Some a)) s' Q ms') ->
  implMA RNG (mbind (mbind m (fun a => mret (Some a))) k) s Q ms.
Proof.
  intros A B RNG m k s Q ms Q1 H HK.
  eapply (implMA_bind RNG _ k s (fun lb s' R' ms' => exists a, lb = Some a /\ Q1 a s' R' ms')).
  - eapply implMA_bind; [exact H|]. intros a s' R' ms' HQ. apply implMA_ret. apply evtF_done. exists a. split; [reflexivity| exact HQ].
  - intros lb s' R' ms' (a & -> & HQ). exact (HK a s' R' ms' HQ).
Qed.

(* [comment removed for export] *)
Lemma unpoisoned_bom : forall m, rt_bom_sh m -> unpoisoned m 0x22ee0 0x22ee3.
Proof.
  intros m H. unfold rt_bom_sh, ABOM in H.
  destruct (rw_cells_cut asegs _ _ _ 4 H) as [_ H4]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H4.
  destruct (rw_cells_cut asegs _ _ _ 1 H4) as [H5 _]. cbn [firstn skipn] in H5.
  change (shad 0x22ec0 + Z.of_nat 4) with 2147468764 in H5. apply byte_of_c1 in H5; [| lia].
  split; [lia|]. split; [lia|]. intros G G0 G1 G2. assert (G = 0x45dc) by lia. subst G.
  exists (Z_to_bv 8 4). split; [unfold ASHOFF; exact H5|]. right. rewrite sval_lit by lia. cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma mc_pre_i : forall RNG sp m lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 K,
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - K -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_flags m -> rt_real_mc m ->
  length b1 = length b2 -> n = Z.of_nat (length b1) -> 1 <= n <= 64 ->
  bytes_at asegs m S1 b1 -> bytes_at asegs m S2 b2 ->
  (S1 + n <= lo \/ bv_unsigned sp <= S1) -> (S2 + n <= lo \/ bv_unsigned sp <= S2) ->
  app_blk S1 (S1 + n) -> app_blk S2 (S2 + n) -> unpoisoned m S1 (S1 + n) -> unpoisoned m S2 (S2 + n) ->
  (RLO1 <= S1 /\ S1 + n <= RHI1 /\ RLO1 mod 64 = 0 /\ RHI1 mod 64 = 0 /\ 0 <= RLO1 /\ RHI1 <= KEND) ->
  (RLO2 <= S2 /\ S2 + n <= RHI2 /\ RLO2 mod 64 = 0 /\ RHI2 mod 64 = 0 /\ 0 <= RLO2 /\ RHI2 <= KEND) ->
  wr_at asegs m (shad RLO1) (shad RHI1 - shad RLO1) -> wr_at asegs m (shad RLO2) (shad RHI2 - shad RLO2) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S1 n -> rng RNG S2 n ->
  rng RNG (shad RLO1) (shad RHI1 - shad RLO1) -> rng RNG (shad RLO2) (shad RHI2 - shad RLO2) ->
  mc_pre RNG sp m lo S1 S2 n b1 b2 RLO1 RHI1 RLO2 RHI2 K.
Proof. intros. unfold mc_pre. repeat (split; [assumption|]). assumption. Qed.

(* [comment removed for export] *)
Lemma aimpl_post_cells : forall m AIM p1 p2 pad ASI cap AOC AIA, rw_cells asegs m AIM (aimpl_cells p1 p2 pad ASI cap AOC AIA) ->
  rw_cells asegs m AIM [C8 (Z_to_bv 64 AVTAB_DOM)] /\ rw_cells asegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)]
  /\ rw_cells asegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)].
Proof.
  intros m AIM p1 p2 pad ASI cap AOC AIA H. unfold aimpl_cells in H.
  destruct (rw_cells_cut asegs _ _ _ 1 H) as [H0 H1]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1.
  destruct (rw_cells_cut asegs _ _ _ 2 H1) as [_ H2]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H2.
  destruct (rw_cells_cut asegs _ _ _ 1 H2) as [H3 H4]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H3, H4.
  destruct (rw_cells_cut asegs _ _ _ 6 H4) as [_ H5]. cbn [firstn skipn cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H5.
  destruct (rw_cells_cut asegs _ _ _ 2 H5) as [H6 _]. cbn [firstn skipn] in H6.
  split; [exact H0|]. split.
  - replace (AIM + 16) with (AIM + 8 + 8) by lia. exact H3.
  - replace (AIM + 56) with (AIM + 8 + 8 + 8 + 32) by lia. exact H6.
Qed.

(* [comment removed for export] *)
Lemma strip_bom_shape : forall data, strip_bom data = data \/ exists a b c, data = a :: b :: c :: strip_bom data.
Proof.
  intros [|a [|b [|c r]]]; try (left; reflexivity). cbn [strip_bom].
  destruct ((a =? 239) && (b =? 187) && (c =? 191)); [right; exists a, b, c; reflexivity| left; reflexivity].
Qed.
Lemma Forall_strip_bom : forall (Pr : Z -> Prop) data, Forall Pr data -> Forall Pr (strip_bom data).
Proof.
  intros Pr data H. destruct (strip_bom_shape data) as [E|(a & b & c & E)]; [rewrite E; exact H|].
  rewrite E in H. inversion H as [|? ? _ F1]. inversion F1 as [|? ? _ F2]. inversion F2 as [|? ? _ F3]. exact F3.
Qed.
Lemma zlength_strip_bom : forall data, zlength (strip_bom data) = zlength data \/ zlength (strip_bom data) = zlength data - 3.
Proof.
  intros data. destruct (strip_bom_shape data) as [E|(a & b & c & E)]; [left; rewrite E; reflexivity|].
  right. rewrite E at 2. unfold zlength. cbn [length]. lia.
Qed.
Lemma strip_bom_3 : forall a b c r, strip_bom (a :: b :: c :: r) = if (a =? 239) && (b =? 187) && (c =? 191) then r else a :: b :: c :: r.
Proof. reflexivity. Qed.
Lemma list3 : forall (l : list Z), (3 <= length l)%nat -> exists a b c r, l = a :: b :: c :: r.
Proof. intros [|a [|b [|c r]]] H; cbn in H; try lia. exists a, b, c, r. reflexivity. Qed.
Lemma strip_bom_short : forall data, (length data < 3)%nat -> strip_bom data = data.
Proof. intros [|a [|b [|c r]]] H; cbn in H; try lia; reflexivity. Qed.
(* [comment removed for export] *)
Lemma copy_s1bufA : forall m A data bs z,
  rw_cells asegs m A [CB (Z.to_nat (zlength data)) bs] -> rw_cells asegs m (A + zlength data) [CB 64 (repeat z 64)] ->
  bs = map (Z_to_bv 8) data -> z = Z_to_bv 8 0 -> bytes_at asegs m A (s1buf data).
Proof.
  intros m A data bs z [[_ H1] _] [[_ H2] _] E Ez. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  unfold s1buf. rewrite map_app, map_repeat. rewrite <- E, <- Ez.
  apply bytes_at_app_join; [exact H1|]. subst bs. rewrite length_map. unfold zlength in H2. exact H2.
Qed.
Lemma buf_stripA : forall m A data, bytes_at asegs m A (s1buf data) ->
  bytes_at asegs m (A + (zlength data - zlength (strip_bom data))) (s1buf (strip_bom data)).
Proof.
  intros m A data H. destruct (strip_bom_shape data) as [E|(a & b & c & E)].
  - rewrite E. replace (A + (zlength data - zlength data)) with A by lia. exact H.
  - set (r := strip_bom data) in *. rewrite E in H.
    replace (s1buf (a :: b :: c :: r)) with ([Z_to_bv 8 a; Z_to_bv 8 b; Z_to_bv 8 c] ++ s1buf r) in H by reflexivity.
    apply bytes_at_app_split in H as [_ H]. cbn [length] in H.
    replace (zlength data - zlength r) with 3 by (rewrite E; unfold zlength; cbn [length]; lia). exact H.
Qed.
Lemma nodup7A : forall {T : Type} (x1 x2 x3 x4 x5 x6 x7 : T), List.NoDup [x1; x2; x3; x4; x5; x6; x7] ->
  x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x1 <> x5 /\ x1 <> x6 /\ x1 <> x7 /\ x2 <> x3 /\ x2 <> x4 /\ x2 <> x5 /\ x2 <> x6 /\ x2 <> x7
  /\ x3 <> x4 /\ x3 <> x5 /\ x3 <> x6 /\ x3 <> x7 /\ x4 <> x5 /\ x4 <> x6 /\ x4 <> x7 /\ x5 <> x6 /\ x5 <> x7 /\ x6 <> x7.
Proof.
  intros T x1 x2 x3 x4 x5 x6 x7 N. apply NoDup_cons_iff in N as [N1 N]. apply NoDup_cons_iff in N as [N2 N]. apply NoDup_cons_iff in N as [N3 N].
  apply NoDup_cons_iff in N as [N4 N]. apply NoDup_cons_iff in N as [N5 N]. apply NoDup_cons_iff in N as [N6 _].
  cbn [In] in N1, N2, N3, N4, N5, N6.
  repeat split; intro E; subst;
    first [ apply N1; solve [repeat (first [left; reflexivity| right])] | apply N2; solve [repeat (first [left; reflexivity| right])]
          | apply N3; solve [repeat (first [left; reflexivity| right])] | apply N4; solve [repeat (first [left; reflexivity| right])]
          | apply N5; solve [repeat (first [left; reflexivity| right])] | apply N6; solve [repeat (first [left; reflexivity| right])] ].
Qed.
(* [comment removed for export] *)
Lemma nodup7_permA : forall {T : Type} (x1 x2 x3 x4 x5 x6 x7 : T) rest, List.NoDup (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) ->
  List.NoDup [x5; x4; x1; x6; x7; x3; x2].
Proof.
  intros T x1 x2 x3 x4 x5 x6 x7 rest N.
  assert (N7 : List.NoDup [x1; x2; x3; x4; x5; x6; x7]) by (apply (NoDup_app_remove_r _ rest); exact N).
  destruct (nodup7A _ _ _ _ _ _ _ N7) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21).
  repeat constructor; cbn [In]; intros H; repeat destruct H as [H|H]; subst; tauto.
Qed.



Section S.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

(* [comment removed for export] *)
Definition apid_blocks (len : Z) (r : AsanCtrl.aptr * AsanCtrl.aptr * (AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr) * option AsanCtrl.aptr)
    (SBA TPA AIM ASI AOC AIA ACP : Z) : list ablock :=
  let '(psb, ptp, (pim, psi, poc, pia), lb) := r in
  acopy_blk lb ACP (COPY_BYTES len) ++ asix_blks pia poc psi pim ptp psb AIA AOC ASI AIM TPA SBA ISARR_BYTES OC_BYTES (SIDX_BYTES len) IMPL_BYTES (TAPE_BYTES len) (SB_BYTES len).

(* [comment removed for export] *)
Lemma stk_slot3 : forall m R cs1 cs2 cs3, rw_cells asegs m R cs1 -> rw_cells asegs m (R + 16) cs2 -> rw_cells asegs m (R + 20) cs3 ->
  cells_size cs1 = 16%nat -> cells_size cs2 = 4%nat -> cells_size cs3 = 4%nat -> stk asegs m R (R + 24).
Proof.
  intros m R cs1 cs2 cs3 H1 H2 H3 E1 E2 E3.
  pose proof (stk_of_rw_cells asegs _ _ _ H1) as S1. pose proof (stk_of_rw_cells asegs _ _ _ H2) as S2. pose proof (stk_of_rw_cells asegs _ _ _ H3) as S3.
  rewrite E1 in S1. rewrite E2 in S2. rewrite E3 in S3. change (Z.of_nat 16) with 16 in S1. change (Z.of_nat 4) with 4 in S2, S3.
  replace (R + 16 + 4) with (R + 20) in S2 by lia. replace (R + 20 + 4) with (R + 24) in S3 by lia.
  eapply stk_merge; [eapply stk_merge; [exact S1| exact S2| lia]| exact S3| lia].
Qed.
Lemma stk_slot4 : forall m R cs1 cs2 cs3 cs4, rw_cells asegs m R cs1 -> rw_cells asegs m (R + 8) cs2 -> rw_cells asegs m (R + 16) cs3 ->
  rw_cells asegs m (R + 20) cs4 -> cells_size cs1 = 8%nat -> cells_size cs2 = 8%nat -> cells_size cs3 = 4%nat -> cells_size cs4 = 4%nat ->
  stk asegs m R (R + 24).
Proof.
  intros m R cs1 cs2 cs3 cs4 H1 H2 H3 H4 E1 E2 E3 E4.
  pose proof (stk_of_rw_cells asegs _ _ _ H1) as S1. pose proof (stk_of_rw_cells asegs _ _ _ H2) as S2.
  pose proof (stk_of_rw_cells asegs _ _ _ H3) as S3. pose proof (stk_of_rw_cells asegs _ _ _ H4) as S4.
  rewrite E1 in S1. rewrite E2 in S2. rewrite E3 in S3. rewrite E4 in S4. change (Z.of_nat 8) with 8 in S1, S2. change (Z.of_nat 4) with 4 in S3, S4.
  replace (R + 8 + 8) with (R + 16) in S2 by lia. replace (R + 16 + 4) with (R + 20) in S3 by lia. replace (R + 20 + 4) with (R + 24) in S4 by lia.
  eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [exact S1| exact S2| lia]| exact S3| lia]| exact S4| lia].
Qed.

Definition apid_post (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : APS) (LB : list ablock) (len lo P R : Z) (m : amem)
    (r : AsanCtrl.aptr * AsanCtrl.aptr * (AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr * AsanCtrl.aptr) * option AsanCtrl.aptr)
    (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ frm0 fc'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ stk asegs m' R (R + 24)      (* [comment removed for export] *)
    /\ aheap_pres_W CI LB (bv_unsigned sp) ([(P, P + 80); (R, R + 24)] ++ client_wr) m m'
    /\ aps_rest s' = aps_rest s
    /\ client_static1 m'
    /\ exists SBA TPA AIM ASI AOC AIA ACP,
         AHEAP AI L RNG' (aps_m s') (apid_blocks len r SBA TPA AIM ASI AOC AIA ACP ++ LB) m'
         /\ rw_cells asegs m' (P + 8) [C8 (Z_to_bv 64 AIM)] /\ rw_cells asegs m' (P + 24) [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)]
         /\ rw_cells asegs m' (P + 64) [C8 (Z_to_bv 64 (acopy_addr (snd r) ACP))]
         /\ rw_cells asegs m' AIM [C8 (Z_to_bv 64 AVTAB_DOM)] /\ rw_cells asegs m' (AIM + 16) [C8 (Z_to_bv 64 ASI)]
         /\ rw_cells asegs m' (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)].

Definition apid_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (lo : Z) (rstk : region) (data : list Z) (D P R : Z) (jr : list byte) (trR : list Z),
    AHEAP AI L RNG (aps_m s) LB m ->
    (forall b, In b LB -> (exists p A n, b = HB p A n) \/ (exists cls FA FN, b = mkABlock (ABFake cls) FA FN /\ cls <> 5 /\ cls <> 4)) ->
    payload_atA LB D data ->
    bytes_at asegs m D (map (Z_to_bv 8) data) -> Forall (fun c => 0 <= c < 256) data -> D mod 16 = 0 -> zlength data < 2^26 ->
    client_img m -> client_sh m -> client_static s LB m ->
    (* [comment removed for export] *)
    rw_cells asegs m (P + 8) [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m (P + 24) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m (P + 48) [C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m (P + 64) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m R [CB 24 jr] ->
    (exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= P /\ P + 80 <= FA + FN /\ ablk FA (FA + FN)) ->
    P + 80 <= R -> R mod 8 = 0 -> P mod 8 = 0 ->
    rw_cells asegs m (shx P) [CB 10 (repeat (Z_to_bv 8 0) 10)] -> rw_cells asegs m (shx R) [CB 3 (repeat (Z_to_bv 8 0) 3)] ->
    rng RNG R 24 -> rng RNG (shx R) (shx (R + 24) - shx R) -> rng RNG P 80 -> rng RNG (shx P) (shx (P + 80) - shx P) ->
    (* [comment removed for export] *)
    bv_unsigned sp + 16 <= R -> R + 24 <= r_hi rstk ->
    (* [comment removed for export] *)
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - APID_STACK ->
    rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk -> rrng RNG rstk ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    mem_inv asegs m -> frm0 fc ->
    tp = Z_to_bv 64 ATP ->
    HU L ->
    (* [comment removed for export] *)
    uchain m (al_top L) AFREE_PC (bv_unsigned sp - 112) R (Nat.pred UDEPTH) trR -> (length trR <= 27)%nat ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
    aps_ok L s -> AFRESH (aps_m s) -> dk (aps_m s) < DWMAX ->
    a0 = Z_to_bv 64 R -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 (P + 24) -> a3 = Z_to_bv 64 D -> a4 = Z_to_bv 64 (zlength data) ->
    a5 = Z_to_bv 64 1 ->
    implMA RNG (HarnessP.parse_into_doc amalloc_M afree_M (new_handlerA AAllocAsan) data) s
          (apid_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (zlength data) lo P R m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 APID) fc None m (seg_rom asegs)).


(* [comment removed for export] *)
Definition apid_W (P R : Z) : list (Z * Z) := [(P, P + 80); (R, R + 24)] ++ client_wr.

(* [comment removed for export] *)
Definition wfar2 (iv : Z * Z) : Prop := 0x642200 <= fst iv /\ (snd iv <= KLS \/ 0x800c4a00 <= fst iv).

Section PresW.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.
  (* [comment removed for export] *)
  Lemma pres_W_of_x : forall LB LB' SP SP' W X n m m', aheap_pres_x CI LB' SP' X n m m' -> SP' <= SP -> (forall b, In b LB -> In b LB') ->
    (forall a, aclient_addr CI LB SP a -> outside W a -> ~ (X <= a < X + n)) -> aheap_pres_W CI LB SP W m m'.
  Proof.
    intros LB LB' SP SP' W X n m m' H HS HL HX a Ha Hc Ho. apply H; [exact Ha| | exact (HX a Hc Ho)].
    eapply aclient_addr_mono_sp; [eapply aclient_addr_mono_lb; [exact Hc| exact HL]| exact HS].
  Qed.
  Lemma magree_of_pres_W : forall LB SP W m m', aheap_pres_W CI LB SP W m m' ->
    magree asegs (fun a => aclient_addr CI LB SP a /\ outside W a) m m'.
  Proof. intros LB SP W m m' H a Ha [Hc Ho]. exact (H a Ha Hc Ho). Qed.
  Lemma outside_wfar2 : forall W a, Forall wfar2 W -> (a < 0x642200 \/ KLS <= a < 0x800c4a00) -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a FW Ha; cbn [outside]; [exact I|].
    inversion FW as [|? ? F1 FW']; subst. unfold wfar2 in F1. cbn [fst snd] in F1. split; [unfold KLS in *; lia| exact (IH a FW' Ha)].
  Qed.
  Lemma client_img_W : forall L RNG st LB LB' SP W m m', client_img m -> aheap_pres_W CI LB SP W m m' -> Forall wfar2 W ->
    AHEAP AI L RNG st LB' m' -> mem_inv asegs m' -> client_img m'.
  Proof.
    intros L RNG st LB LB' SP W m m' IG PW FW AH MI. eapply (client_img_magree AI _ L RNG st LB' m m' IG); [exact (magree_of_pres_W _ _ _ _ _ PW)| | exact AH| exact MI].
    intros a Ha. split; [exact (client_img_addr AI IMG_CI LB SP a Ha)|]. apply outside_wfar2; [exact FW|].
    destruct Ha as [Ha|[Ha|Ha]]; [left; lia| left; lia|].
    apply client_x_addr_num in Ha. unfold AREAL_MC, AFMIN, ABOM, ACTAB, shad, ASHOFF, KLS in *.
    rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2 ^ 3) with 8 in Ha. cbn in Ha. lia.
  Qed.
  Lemma client_sh_W : forall LB SP W m m', client_sh m -> aheap_pres_W CI LB SP W m m' -> Forall wfar2 W -> client_sh m'.
  Proof.
    intros LB SP W m m' CS PW FW. eapply (client_sh_magree _ m m' CS (magree_of_pres_W _ _ _ _ _ PW)).
    intros Y HY. split; [exact (client_sh_addr AI IMG_CI LB SP Y HY)|]. apply outside_wfar2; [exact FW|].
    pose proof (client_sh_addr_bounds Y HY) as B. right. exact B.
  Qed.
  Lemma rclean_W : forall LB SP W m m' r, rclean m r -> aheap_pres_W CI LB SP W m m' -> ATOP <= r_rlo r ->
    (forall a, shad (r_rlo r) <= a < shad (r_rhi r) -> outside W a) -> rclean m' r.
  Proof.
    intros LB SP W m m' r [(U & HL & WR & AB) LT] PW RA HO. pose proof HL as (H1 & H2 & H3 & H4 & H5 & H6).
    unfold KEND in H6. pose proof atop_range as AR.
    assert (SB : forall s, shad (r_rlo r) <= s < shad (r_rhi r) -> 0 <= s < 2^64 /\ aclient_addr CI LB SP s).
    { intros s Hs. split; [rewrite !shad_div in Hs; unfold ASHOFF in *; Z.div_mod_to_equations; lia|].
      eapply (hull_sh_client AI LB SP (r_rlo r) (r_rhi r) s); [lia| Z.div_mod_to_equations; lia| lia| exact Hs]. }
    split; [| exact LT]. split; [| split; [exact HL| split; [| exact AB]]].
    - eapply unpoisoned_agree; [exact U|]. intros s Hs.
      assert (Hs' : shad (r_rlo r) <= s < shad (r_rhi r)).
      { rewrite !shad_div in Hs |- *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
      destruct (SB s Hs') as (SR & SC). exact (proj1 (PW s SR SC (HO s Hs'))).
    - eapply wr_at_magree; [exact (magree_of_pres_W _ _ _ _ _ PW)| exact WR|]. intros a Ha.
      assert (Ha' : shad (r_rlo r) <= a < shad (r_rhi r)) by lia.
      destruct (SB a Ha') as (_ & SC). exact (conj SC (HO a Ha')).
  Qed.

  (* [comment removed for export] *)
  Lemma aclient_range_cr : forall LB SP A n, existsb (fun iv => (fst iv <=? A) && (A + n <=? snd iv)) client_ranges = true ->
    aclient_range CI LB SP A n.
  Proof.
    intros LB SP A n H. apply existsb_exists in H as (iv & Hin & Hb). apply andb_prop in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. left; right; left. exists iv. split; [apply IMG_CI; exact Hin| lia].
  Qed.
  Lemma aclient_range_crsh : forall LB SP A n,
    existsb (fun iv => (fst iv <=? 8 * (A - ASHOFF)) && (8 * (A + n - ASHOFF) <=? snd iv)) client_ranges = true ->
    aclient_range CI LB SP A n.
  Proof.
    intros LB SP A n H. apply existsb_exists in H as (iv & Hin & Hb). apply andb_prop in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. eapply (aclient_range_img_sh AI LB SP A n iv); [apply IMG_CI; exact Hin| lia| lia].
  Qed.
End PresW.
End S.
End CANSEC1.

(* [comment removed for export] *)
Section CANSECsh. Context {rc : runConstT}.
(* [comment removed for export] *)
Lemma aclient_range_stack_sh : forall (CI : list (Z * Z)) LB SP X, ATOP <= X -> X + 8 <= 2^47 -> X mod 8 = 0 ->
  aclient_range CI LB SP (Z.shiftr X 3 + 2147450880) 1.
Proof.
  intros CI LB SP X H1 H2 H3. right. right. left. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by (pose proof atop_range; lia).
  change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.
End CANSECsh.

Ltac acrA INF IMGCI :=
  first [ apply aclient_range_stack; cbn; lia
        | eapply aclient_range_fake; [exact INF| cbn; lia| cbn; lia]
        | eapply aclient_range_fake_sh; [exact INF| lia| lia| Z.div_mod_to_equations; lia| lia]
        | apply aclient_range_stack_sh; [lia| lia| Z.div_mod_to_equations; lia]
        | (right; left; eexists; split; [eassumption| cbn; lia])
        | (left; right; left; eexists; split; [apply IMGCI; cbn; repeat (first [left; reflexivity| right]) | cbn; lia])
        | (apply (aclient_range_cr _ IMGCI); vm_compute; reflexivity)
        | (apply (aclient_range_crsh _ IMGCI); vm_compute; reflexivity) ].
(* [comment removed for export] *)
Ltac trxA HPX INF IMGCI :=
  lazymatch type of HPX with aheap_pres_x _ ?L ?SP ?X ?n ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply aheap_pres_x_rw_cells; [exact HPX| exact H| acrA INF IMGCI| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.

(* [comment removed for export] *)
Ltac acrF INF IMGCI :=
  lazymatch goal with
  | |- aclient_range _ _ _ (bv_unsigned _ + _) _ => apply aclient_range_stack; cbn; lia
  | |- aclient_range _ _ _ (Z.shiftr _ 3 + _) _ => eapply aclient_range_fake_sh; [exact INF| lia| lia| Z.div_mod_to_equations; lia| lia]
  | |- aclient_range _ _ _ ?A _ =>
      first [ is_var A; match goal with Hin : In (HB _ A _) _ |- _ => right; left; eexists; split; [exact Hin| cbn; lia] end
            | eapply aclient_range_fake; [exact INF| cbn; lia| cbn; lia]
            | acrA INF IMGCI ]
  end.
Ltac trxF HPX INF IMGCI :=
  lazymatch type of HPX with aheap_pres_x _ ?L ?SP ?X ?n ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply aheap_pres_x_rw_cells; [exact HPX| exact H| acrF INF IMGCI| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.

(* [comment removed for export] *)
Ltac acrC INF IMGCI PRN :=
  lazymatch goal with
  | |- aclient_range _ _ _ (bv_unsigned _ + _) _ => apply aclient_range_stack; cbn; PRN (); lia
  | |- aclient_range _ _ _ (Z.shiftr _ 3 + _) _ =>
      first [ eapply aclient_range_fake_sh; [exact INF| PRN (); lia| PRN (); lia| PRN (); Z.div_mod_to_equations; lia| PRN (); lia]
            | apply aclient_range_stack_sh; [PRN (); lia| PRN (); lia| PRN (); Z.div_mod_to_equations; lia] ]
  | |- aclient_range _ _ _ ?A _ =>
      first [ lazymatch A with ?B + _ => is_var B; match goal with Hin : In (HB _ B _) _ |- _ => right; left; eexists; split; [exact Hin| cbn; PRN (); lia] end end
            | is_var A; match goal with Hin : In (HB _ A _) _ |- _ => right; left; eexists; split; [exact Hin| cbn; PRN (); lia] end
            | eapply aclient_range_fake; [exact INF| cbn; PRN (); lia| cbn; PRN (); lia]
            | (apply aclient_range_stack; cbn; PRN (); lia)
            | acrA INF IMGCI ]
  end.
Ltac trxC HPX INF IMGCI PRN :=
  lazymatch type of HPX with aheap_pres_x _ ?L ?SP ?X ?n ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply aheap_pres_x_rw_cells; [exact HPX| exact H| acrC INF IMGCI PRN| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; PRN (); lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.
Ltac trpC HPR INF IMGCI PRN :=
  lazymatch type of HPR with aheap_pres _ ?L ?SP ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs) by (eapply aheap_pres_rw_cells; [exact HPR| exact H| acrC INF IMGCI PRN]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.
(* [comment removed for export] *)
Ltac trmC MU WM PRN :=
  lazymatch type of MU with munch ?W ?mo ?mn =>
  repeat match goal with
  | H : rw_cells asegs mo ?A ?cs |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : rw_cells asegs mn A cs)
                by (eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; PRN (); lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  | H : stk asegs mo ?lo ?hi |- _ =>
      let H' := fresh "T" in
      first [ assert (H' : stk asegs mn lo hi) by (eapply stk_transport_disjoint; [exact H| exact MU| exact WM| cbn [disjoint_from]; PRN (); lia]);
              clear H; rename H' into H
            | lazymatch type of H with ?T => change (skippedB T) in H end ]
  | H : wr_at asegs mo ?A ?n |- _ =>
      let H' := fresh "T" in assert (H' : wr_at asegs mn A n) by (eapply wr_at_transport; [exact H| exact WM]); clear H; rename H' into H
  end end; repeat match goal with H : skippedB _ |- _ => unfold skippedB in H end.

(* [comment removed for export] *)
Ltac callp PRN :=
  lazymatch goal with
  | |- mem_inv _ _ => eassumption
  | |- stk _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- wr_at _ _ _ _ => eassumption
  | |- rng ?R ?X ?n => first [ eassumption | match goal with H : rng R ?a ?k |- _ => eapply rng_sub'; [exact H| PRN (); lia] end ]
  | |- ?G => first [ eassumption | (PRN (); lia) ]
  end.

(* [comment removed for export] *)
Ltac drop_mem mo := repeat match goal with H : context [mo] |- _ => lazymatch type of H with amem => fail | _ => clear H end end; try clear mo.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Ltac2 keep_only (keep : ident list) : unit :=
  let hs := Control.hyps () in
  let cl := List.fold_right (fun h acc => let (id, body, ty) := h in
      if List.exist (fun k => Ident.equal k id) keep then acc
      else match body with
           | Some _ => acc
           | None => if Constr.equal (Constr.type ty) 'Prop then id :: acc else acc
           end) hs [] in
  Std.clear cl.
Ltac prnA := ltac2:(Control.enter (fun () => keep_only [@LOA; @LOS; @LEN0; @DL; @CAPR; @FK2; @FKB3; @FKB2; @FK1; @FKH; @RP; @RSPR; @R47; @PR0; @R8; @P8; @RSP; @STOP; @LY3; @bFr; @bFhi; @bFlo;
  @SB; @SB0; @SB1; @SB2; @SB3; @SB4; @SB5; @SB6; @SB7; @SB8; @SB9;
  @BRM1; @BRM2; @BRM3; @BRM4; @BRI1; @BRI2; @BRI3; @BRI4; @BRO1; @BRO2; @BRO3; @BRO4; @BRA1; @BRA2; @BRA3; @BRA4;
  @BRS1; @BRS2; @BRS3; @BRS4; @BRT1; @BRT2; @BRT3; @BRT4; @BRC1; @BRC2; @BRC3; @BRC4; @bCr; @bChi; @bClo; @DJM; @DJF; @DJP; @DJMF])).

(* [comment removed for export] *)
Definition hidA (P : Prop) : Prop := P.
Ltac2 rec is_arith (t : constr) : bool :=
  lazy_match! t with
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | @eq Z _ _ => true | @eq nat _ _ => true | Peano.le _ _ => true | Peano.lt _ _ => true
  | ?a /\ ?b => Bool.or (is_arith a) (is_arith b)
  | ?a \/ ?b => Bool.or (is_arith a) (is_arith b)
  | ~ ?a => is_arith a
  | _ => false
  end.
Ltac2 hide_arith (keep : ident list) : unit :=
  List.iter (fun h => let (id, body, ty) := h in
    match body with
    | Some _ => ()
    | None =>
        if List.exist (fun k => Ident.equal k id) keep then ()
        else if is_arith ty then ltac1:(h t |- change (hidA t) in h) (Ltac1.of_ident id) (Ltac1.of_constr ty) else ()
    end) (Control.hyps ()).
Ltac unhide_arith := repeat match goal with H : hidA _ |- _ => unfold hidA in H end.

#[global] Set Default Proof Mode "Classic".

