(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_activewA Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition impG (sp0 usp sp' f lo : Z) : Prop :=
  0x6e0000 <= f /\ f mod 64 = 0 /\ f + 2048 <= sp0 - STACK_WIN /\ SHB <= shad f /\ shad f + 256 + 1 <= sp0 - STACK_WIN
  /\ (f + 2048 <= shad f \/ shad f + 256 <= f)
  /\ sp0 - STACK_WIN <= lo /\ lo + FUZZ_STACK <= usp /\ usp + 16 <= USTACK_TOP /\ usp - 336 <= sp' <= usp - 320 /\ sp' mod 32 = 0
  /\ 0x7fff80000000 <= sp0 /\ sp0 <= USTACK_TOP.

Lemma impG_facts : forall sp0 usp sp' f lo, impG sp0 usp sp' f lo ->
  0 < f /\ f + 2048 <= lo /\ 0 <= shad f /\ shad f + 256 <= lo /\ shad f + 156 <= lo /\ 0x6e0000 <= lo /\ 0x6a9000 <= lo /\ lo <= sp' - 64 /\ lo <= sp'
  /\ sp' + 216 <= usp - 104 /\ usp < 2^63 /\ sp' + 216 < 2^63 /\ 0x6e0000 <= sp' /\ f mod 8 = 0.
Proof.
  intros sp0 usp sp' f lo (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  unfold FUZZ_STACK, USTACK_TOP, STACK_WIN, SHB in *. repeat split; try lia. all: Z.div_mod_to_equations; lia.
Qed.

Definition slot0A (m : mem) (I : Z) : Prop :=
  rw_cells bsegs m (I + 16) [C8 (wz 0)] /\ rw_cells bsegs m (I + 32) [C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m (I + 72) [C8 (wz 0)]
  /\ rw_cells bsegs m (I + 112) (out_shortA z8 (repeat z8 23)).

Lemma le8_zero_z24 : cells_bytes [C8 (wz 0); C8 (wz 0); C8 (wz 0)] = z24.
Proof. vm_compute. reflexivity. Qed.

Lemma impl0A_slot0A : forall (m : mem) I w j9 j25 j65 j108, rw_cells bsegs m I (impl0A w j9 j25 j65 j108) -> slot0A m I.
Proof.
  intros m I w j9 j25 j65 j108 H. unfold impl0A, implA_cells in H.
  lazymatch type of H with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: nil) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: nil)
      with ([c0; c1; c2] ++ [c3] ++ [c4; c5; c6] ++ [c7] ++ [c8; c9; c10] ++ [c11] ++ [c12] ++ [c13]) in H end.
  apply rw_cells_app in H. destruct H as [_ H]. apply rw_cells_app in H. destruct H as [H16 H]. apply rw_cells_app in H. destruct H as [_ H].
  apply rw_cells_app in H. destruct H as [H32 H]. apply rw_cells_app in H. destruct H as [_ H]. apply rw_cells_app in H. destruct H as [H72 H].
  apply rw_cells_app in H. destruct H as [_ H112]. cbn [cells_size csize Nat.add app] in H16, H32, H72, H112.
  lazymatch type of H16 with rw_cells _ _ ?a _ => replace a with (I + 16) in H16 by lia end.
  lazymatch type of H32 with rw_cells _ _ ?a _ => replace a with (I + 32) in H32 by lia end.
  lazymatch type of H72 with rw_cells _ _ ?a _ => replace a with (I + 72) in H72 by lia end.
  lazymatch type of H112 with rw_cells _ _ ?a _ => replace a with (I + 112) in H112 by lia end.
  split; [exact H16|]. split; [| split].
  - apply (rw_cells_split_CB bsegs _ _ [] 24 z24 [] [8; 8; 8]%nat) in H32; [| reflexivity]. cbn [mk_CB_cells app] in H32.
    lazymatch type of H32 with rw_cells _ _ _ (?a :: ?b :: ?c :: nil) => change (a :: b :: c :: nil) with ([a; b] ++ [c]) in H32 end.
    apply rw_cells_app in H32. destruct H32 as [H32 _].
    eapply rw_cells_recastA; [exact H32| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
  - apply (rw_cells_split_CB bsegs _ _ [] 36 z36 [] [8; 28]%nat) in H72; [| reflexivity]. cbn [mk_CB_cells app] in H72.
    lazymatch type of H72 with rw_cells _ _ _ (?a :: ?b :: nil) => change (a :: b :: nil) with ([a] ++ [b]) in H72 end.
    apply rw_cells_app in H72. destruct H72 as [H72 _].
    eapply rw_cells_recastA; [exact H72| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
  - unfold out_shortA. eapply rw_cells_recastA; [exact H112| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Lemma slot0A_agree : forall (m m' : mem) I, slot0A m I -> agree_on (fun x => I + 16 <= x < I + 136) m m' -> slot0A m' I.
Proof.
  intros m m' I (H1 & H2 & H3 & H4) AG. unfold slot0A, out_shortA in *.
  repeat split;
    first [ apply (rw_cells_agree_nw bsegs m m' _ _ H1) | apply (rw_cells_agree_nw bsegs m m' _ _ H2) | apply (rw_cells_agree_nw bsegs m m' _ _ H3) | apply (rw_cells_agree_nw bsegs m m' _ _ H4) ];
    intros a Ha; apply AG; cbn [cells_size csize Nat.add length] in Ha; lia.
Qed.

Definition tailB (m : mem) (usp sp' f n d A8 : Z) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  (exists (ne : Z) (j0 j8 j160 jr : list byte), (ne = 0 \/ ne = 1) /\ rw_cells bsegs m sp' (imp_localsK j0 j8 f (wz n) d ne j160) /\ rw_cells bsegs m (sp' + 192) [CB 24 jr])
  /\ stk bsegs m (sp' + 216) (usp - 104) /\ rw_cells bsegs m (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)
  /\ (exists h3, rw_cells bsegs m f (fz_hdr (C8 (wz IMP_MAGIC0)) (C8 (wz IMP_HDR_DESC_A)) (C8 (wz e_fuzz)) h3))
  /\ rw_cells bsegs m (shad f) (map C1 imp_sh_pro)
  /\ imp_libA (Some A8) m /\ aex6A m.

Definition tailZ (usp sp' f A8 : Z) (x : Z) : Prop :=
  (sp' <= x < usp) \/ (f <= x < f + 32) \/ (shad f <= x < shad f + 156) \/ imp_lib_rng (Some A8) x \/ in_ranges IMP_AEX_W x.

Lemma aex6A_agree : forall m m', aex6A m -> agree_on (in_ranges IMP_AEX_W) m m' -> aex6A m'.
Proof.
  intros m m' [(p1 & p2 & H1) H2] AG. unfold IMP_AEX_W in AG. split.
  - exists p1, p2. apply (rw_cells_agree_nw bsegs m m' _ _ H1). intros a Ha. apply AG. exists AEX, (AEX + 80). split; [left; reflexivity|].
    unfold aex_tbl in Ha. cbn [cells_size csize Nat.add] in Ha. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ H2). intros a Ha. apply AG. exists AEX_A0, (AEX_A0 + 48). split; [right; left; reflexivity|].
    unfold aex_args in Ha. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.

Lemma cells_size_map_C1' : forall l : list byte, cells_size (map C1 l) = length l.
Proof. induction l as [|b l IH]; [reflexivity| cbn; rewrite IH; reflexivity]. Qed.

Lemma tailB_agree : forall m m' usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11,
  tailB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 -> sp' + 216 <= usp - 104 ->
  agree_on (tailZ usp sp' f A8) m m' -> tailB m' usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.
Proof.
  intros until cs11. intros ((ne & j0 & j8 & j160 & jr & NE & L1 & L2) & STp & SV & (h3 & HD) & SH & LB & AX) LU AG. unfold tailZ in AG.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - exists ne, j0, j8, j160, jr. split; [exact NE|]. split.
    + apply (rw_cells_agree_nw bsegs m m' _ _ L1). intros a Ha. apply AG. rewrite imp_localsK_size in Ha. left. lia.
    + apply (rw_cells_agree_nw bsegs m m' _ _ L2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. left. lia.
  - apply (stk_agree_nw bsegs m m' _ _ STp). intros a Ha. apply AG. cbv beta in Ha. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ SV). intros a Ha. apply AG. rewrite imp_savedA_size in Ha. left. lia.
  - exists h3. apply (rw_cells_agree_nw bsegs m m' _ _ HD). intros a Ha. apply AG. unfold fz_hdr in Ha. cbn [cells_size csize Nat.add] in Ha. right; left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ SH). intros a Ha. apply AG. rewrite cells_size_map_C1' in Ha. unfold imp_sh_pro in Ha. rewrite imp_sh_length in Ha. do 2 right. left. lia.
  - apply (imp_libA_agree (Some A8) m m' LB). intros a Ha. apply AG. do 3 right. left. exact Ha.
  - apply (aex6A_agree m m' AX). intros a Ha. apply AG. do 4 right. exact Ha.
Qed.

Lemma tailZ_aclient : forall (live : list (Z * Z)) usp sp' f A8 x,
  0 < f -> 0 <= shad f -> In (A8, 8) live -> usp <= USTACK_TOP ->
  tailZ usp sp' f A8 x -> aclient live [(f, 5%nat)] sp' x.
Proof.
  intros live usp sp' f A8 x F0 SH0 HIN UT H. unfold tailZ in H. unfold aclient.
  destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; right; right; left. exists f, 5%nat. split; [left; reflexivity| change (fs_size 5) with 2048; lia].
  - right; right; right; right. exists f, 5%nat. split; [left; reflexivity|]. unfold shad, SHB in *. change (fs_size 5) with 2048. Z.div_mod_to_equations; lia.
  - destruct (imp_lib_rng_cases (Some A8) x H) as [[CS _]|(B & E & R)]; [right; left; exact CS|].
    injection E as <-. right; right; left. exists A8, 8. split; [exact HIN| lia].
  - right; left. destruct H as (l & h & Hin & R). unfold IMP_AEX_W in Hin. aex_lits. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia.
Qed.
