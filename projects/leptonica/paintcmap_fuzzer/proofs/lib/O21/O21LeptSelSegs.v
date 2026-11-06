(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac MmapSim SeqExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21LeptStderr O21LeptBase O21LeptBox O21LeptPixCopy O21LeptSelLoop O21_code_1364c_14000 O21_code_14000_15000 O21_code_15000_16000 O21_code_16000_17000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition svr13 (regs : bvmap 5 word) (i : nat) : word :=
  match i with 8 => getr regs 8 | 9 => getr regs 9 | 18 => getr regs 18 | 19 => getr regs 19 | 20 => getr regs 20
  | 21 => getr regs 21 | 22 => getr regs 22 | 23 => getr regs 23 | 24 => getr regs 24 | 25 => getr regs 25 | 26 => getr regs 26 | _ => getr regs 27 end%nat.
Definition frame13 (s : Z) (ret : word) (sv : nat -> word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, sv 8%nat); ((s - 24)%Z, sv 9%nat); ((s - 32)%Z, sv 18%nat); ((s - 40)%Z, sv 19%nat); ((s - 48)%Z, sv 20%nat);
   ((s - 56)%Z, sv 21%nat); ((s - 64)%Z, sv 22%nat); ((s - 72)%Z, sv 23%nat); ((s - 80)%Z, sv 24%nat); ((s - 88)%Z, sv 25%nat);
   ((s - 96)%Z, sv 26%nat); ((s - 104)%Z, sv 27%nat)].

Ltac zva F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).

Section SelSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL21} {P16 : O21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Definition FR13 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
       (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
       (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
       (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
       (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
       (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
       (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
       (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).

  Lemma cells_FR13 : forall m s ret regs, (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR13 m s ret regs) (frame13 s ret (svr13 regs)).
  Proof. intros m s ret regs Hs Hs64. unfold frame13, FR13, svr13. cbn [cellsZ]. repeat split; rdn_solve. Qed.

  Lemma frame13_bounds : forall s ret sv, (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    Forall (fun av => s - 104 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z (frame13 s ret sv).
  Proof. intros s ret sv Hs Hs64. unfold frame13. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

  Lemma cells13_frm : forall C s' m m' s ret sv, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 104)%Z -> (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cellsZ m (frame13 s ret sv) -> cellsZ m' (frame13 s ret sv).
  Proof.
    intros C s' m m' s ret sv CK F Hlo Hs' Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F Hlo); [| exact CE].
    eapply Forall_impl; [| apply (frame13_bounds s ret sv Hs Hs64)]. intros av [A B]. lia.
  Qed.

  Lemma cells13_out : forall m m' (lo hi : Z) s ret sv, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 104 \/ s <= lo)%Z -> (144 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cellsZ m (frame13 s ret sv) -> cellsZ m' (frame13 s ret sv).
  Proof.
    intros m m' lo hi s ret sv OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [| exact CE].
    unfold frame13. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
  Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ss_P : forall regs m (s : Z) (ret : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x1615c : word) m rom) (mkst regs' (0x16194 : word) (FR13 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = ret
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1. unfold FR13. eexists. split.
    - zv F_16058 D_16058 (Z_to_bv 64 (s - 144)).
      stepST F_1605c D_1605c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16060 D_16060 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16064 D_16064 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_16068 D_16068 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1606c D_1606c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_16070 D_16070 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_16074 D_16074 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_16078 D_16078 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_1607c D_1607c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_16080 D_16080 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_16084 D_16084 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_16088 D_16088 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_1608c D_1608c (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_etail : forall regs m (s : Z) (ret : word) (sv : nat -> word) (msg : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x10d41 ->
    exists regs',
      msteps SEGS (mkst regs (0x162e8 : word) m rom) (mkst regs' (0x13db4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10d41 /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv msg Hs Hs64 CE H2 H10 H11. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - sn F_161e4 D_161e4.
      stepLD8 F_161e8 D_161e8 ret. stepLD8 F_161ec D_161ec (sv 8%nat). stepLD8 F_161f0 D_161f0 (sv 9%nat).
      stepLD8 F_161f4 D_161f4 (sv 18%nat). stepLD8 F_161f8 D_161f8 (sv 19%nat). stepLD8 F_161fc D_161fc (sv 20%nat).
      stepLD8 F_16200 D_16200 (sv 21%nat). stepLD8 F_16204 D_16204 (sv 22%nat). stepLD8 F_16208 D_16208 (sv 23%nat).
      stepLD8 F_1620c D_1620c (sv 24%nat). stepLD8 F_16210 D_16210 (sv 25%nat). stepLD8 F_16214 D_16214 (sv 26%nat).
      stepLD8 F_16218 D_16218 (sv 27%nat).
      zv F_1621c D_1621c (Z_to_bv 64 s). sn F_16220 D_16220.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word) (a0v : word),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frame13 s ret sv) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = a0v ->
    exists regs',
      msteps SEGS (mkst regs (0x16568 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = a0v
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat /\ getr regs' 20 = sv 20%nat
      /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat /\ getr regs' 24 = sv 24%nat /\ getr regs' 25 = sv 25%nat
      /\ getr regs' 26 = sv 26%nat /\ getr regs' 27 = sv 27%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret sv a0v Hs Hs64 Hret CE H2 H10. unfold frame13 in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & _).
    eexists. split.
    - stepLD8 F_16464 D_16464 ret. stepLD8 F_16468 D_16468 (sv 8%nat). stepLD8 F_1646c D_1646c (sv 9%nat).
      stepLD8 F_16470 D_16470 (sv 18%nat). stepLD8 F_16474 D_16474 (sv 19%nat). stepLD8 F_16478 D_16478 (sv 20%nat).
      stepLD8 F_1647c D_1647c (sv 21%nat). stepLD8 F_16480 D_16480 (sv 22%nat). stepLD8 F_16484 D_16484 (sv 23%nat).
      stepLD8 F_16488 D_16488 (sv 24%nat). stepLD8 F_1648c D_1648c (sv 25%nat). stepLD8 F_16490 D_16490 (sv 26%nat).
      stepLD8 F_16494 D_16494 (sv 27%nat).
      zv F_16498 D_16498 (Z_to_bv 64 s). stepret F_1649c D_1649c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_ehead : forall (pc msg : Z) regs m (s : Z),
    In (pc, msg) [(0x1624c, 0x10298); (0x16274, 0x108f0); (0x1629c, 0x10368); (0x162c4, 0x10891)]%Z ->
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x162e8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x10d41
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros pc msg regs m s Hin Rg Rs H2. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as Epc Emsg; subst pc msg.
    - eexists. split.
      + replace (Z_to_bv 64 0x1624c) with (0x1624c : word) by (apply bv_eq; reflexivity).
        sn F_16148 D_16148.
        stepLD F_1614c D_1614c (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_16150 D_16150 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_16154 D_16154. stepb_ft F_16158 D_16158 ltac:(condZ).
        sn F_1615c D_1615c. sn F_16160 D_16160. sn F_16164 D_16164. sn F_16168 D_16168. sn F_1616c D_1616c.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x16274) with (0x16274 : word) by (apply bv_eq; reflexivity).
        sn F_16170 D_16170.
        stepLD F_16174 D_16174 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_16178 D_16178 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_1617c D_1617c. stepb_ft F_16180 D_16180 ltac:(condZ).
        sn F_16184 D_16184. sn F_16188 D_16188. sn F_1618c D_1618c. sn F_16190 D_16190. sn F_16194 D_16194.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x1629c) with (0x1629c : word) by (apply bv_eq; reflexivity).
        sn F_16198 D_16198.
        stepLD F_1619c D_1619c (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_161a0 D_161a0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_161a4 D_161a4. stepb_ft F_161a8 D_161a8 ltac:(condZ).
        sn F_161ac D_161ac. sn F_161b0 D_161b0. sn F_161b4 D_161b4. sn F_161b8 D_161b8. sn F_161bc D_161bc.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - eexists. split.
      + replace (Z_to_bv 64 0x162c4) with (0x162c4 : word) by (apply bv_eq; reflexivity).
        sn F_161c0 D_161c0.
        stepLD F_161c4 D_161c4 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_161c8 D_161c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_161cc D_161cc. stepb_ft F_161d0 D_161d0 ltac:(condZ).
        sn F_161d4 D_161d4. sn F_161d8 D_161d8. sn F_161dc D_161dc. sn F_161e0 D_161e0.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_A0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16194 : word) m rom) (mkst regs' (Z_to_bv 64 0x1624c) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_16090 D_16090 ltac:(condZ).
      replace (0x1624c : word) with (Z_to_bv 64 0x1624c) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_A : forall regs m (pixd bx : Z) (vd : pixv),
    (1 <= pixd)%Z -> PIXat m pixd vd -> (0 <= bx < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 bx -> getr regs 12 = Z_to_bv 64 2 ->
    getr regs 13 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 255 -> getr regs 15 = Z_to_bv 64 100 ->
    exists regs',
      msteps SEGS (mkst regs (0x16194 : word) m rom) (mkst regs' (0x161b4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_cmap vd) /\ getr regs' 20 = Z_to_bv 64 100 /\ getr regs' 21 = Z_to_bv 64 255 /\ getr regs' 22 = Z_to_bv 64 255
      /\ getr regs' 8 = Z_to_bv 64 2 /\ getr regs' 18 = Z_to_bv 64 bx /\ getr regs' 19 = Z_to_bv 64 pixd /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [1; 8; 10; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m pixd bx vd Hp PX Hbx H10 H11 H12 H13 H14 H15. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    pose proof (PIX_rd_cmap SEGS _ _ _ PX) as Cc.
    eexists. split.
    - stepb_ft F_16090 D_16090 ltac:(condZ).
      sn F_16094 D_16094. sn F_16098 D_16098. sn F_1609c D_1609c. sn F_160a0 D_160a0. sn F_160a4 D_160a4. sn F_160a8 D_160a8.
      sn F_160ac D_160ac.
      stepb_ft F_151ac D_151ac ltac:(condZ).
      stepLD F_151b0 D_151b0 (Z_to_le_bytes 8 (p_cmap vd)) (Z_to_bv 64 (p_cmap vd)) ltac:(addr_norm; exact Cc) ltac:(apply lez8; lia).
      stepret F_151b4 D_151b4 (0x161b4 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x161b4 : word) m rom) (mkst regs' (Z_to_bv 64 0x16274) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_160b0 D_160b0 ltac:(condZ).
      replace (0x16274 : word) with (Z_to_bv 64 0x16274) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_Bd : forall regs m (pixd cd : Z) (vd : pixv),
    (1 <= pixd)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> (cd < 2 ^ 64)%Z -> (8 < p_d vd)%Z ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x161b4 : word) m rom) (mkst regs' (Z_to_bv 64 0x162c4) m rom)
      /\ regs_agree (fun r => In r [1; 10; 11; 23]%list) regs regs'.
  Proof.
    intros regs m pixd cd vd Hp PX Hcd Hcd64 Hd H10 H19. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - stepb_ft F_160b0 D_160b0 ltac:(condZ).
      sn F_160b4 D_160b4. sn F_160b8 D_160b8. sn F_160bc D_160bc.
      stepb_ft F_1512c D_1512c ltac:(condZ).
      stepLD F_15130 D_15130 (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15134 D_15134 (0x161c4 : word) ltac:(bveq).
      sn F_160c0 D_160c0. stepb_tk F_160c4 D_160c4 ltac:(condZ).
      replace (0x162c4 : word) with (Z_to_bv 64 0x162c4) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_Bn : forall regs m (pixd cd : Z) (vd : pixv) (cv : cmapv),
    (1 <= pixd)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> CMAPat m cd cv -> (p_d vd = 1 \/ p_d vd = 2 \/ p_d vd = 4 \/ p_d vd = 8)%Z -> (c_n cv <= 2)%Z ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 2 ->
    exists regs', msteps SEGS (mkst regs (0x161b4 : word) m rom) (mkst regs' (Z_to_bv 64 0x1629c) m rom)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 23]%list) regs regs'.
  Proof.
    intros regs m pixd cd vd cv Hp PX Hcd CM Hd Hn H10 H19 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn.
    eexists. split.
    - stepb_ft F_160b0 D_160b0 ltac:(condZ).
      sn F_160b4 D_160b4. sn F_160b8 D_160b8. sn F_160bc D_160bc.
      stepb_ft F_1512c D_1512c ltac:(condZ).
      stepLD F_15130 D_15130 (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15134 D_15134 (0x161c4 : word) ltac:(bveq).
      sn F_160c0 D_160c0. stepb_ft F_160c4 D_160c4 ltac:(condZ).
      sn F_160c8 D_160c8. sn F_160cc D_160cc. sn F_160d0 D_160d0. sn F_160d4 D_160d4.
      stepb_ft F_160d8 D_160d8 ltac:(pin; rewrite (depth_mask_278 (p_d vd) Hd); reflexivity).
      sn F_160dc D_160dc. sn F_160e0 D_160e0.
      stepb_ft F_1598c D_1598c ltac:(condZ).
      stepLD F_15990 D_15990 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_15994 D_15994 (0x161e8 : word) ltac:(bveq).
      stepb_tk F_160e4 D_160e4 ltac:(condZ).
      replace (0x1629c : word) with (Z_to_bv 64 0x1629c) by (apply bv_eq; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_B : forall regs m (s pixd cd : Z) (vd : pixv) (cv : cmapv),
    (1 <= pixd)%Z -> PIXat m pixd vd -> (1 <= cd)%Z -> CMAPat m cd cv -> (p_d vd = 1 \/ p_d vd = 2 \/ p_d vd = 4 \/ p_d vd = 8)%Z -> (2 < c_n cv)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 cd -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 2 ->
    getr regs 20 = Z_to_bv 64 100 -> getr regs 21 = Z_to_bv 64 255 -> getr regs 22 = Z_to_bv 64 255 ->
    exists regs', msteps SEGS (mkst regs (0x161b4 : word) m rom) (mkst regs' (0x159cc : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x16208
      /\ getr regs' 10 = Z_to_bv 64 cd /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 255 /\ getr regs' 13 = Z_to_bv 64 100 /\ getr regs' 14 = Z_to_bv 64 (s - 132)
      /\ getr regs' 9 = Z_to_bv 64 (p_d vd) /\ getr regs' 23 = Z_to_bv 64 cd /\ getr regs' 24 = Z_to_bv 64 (c_n cv)
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 23; 24]%list) regs regs'.
  Proof.
    intros regs m s pixd cd vd cv Hp PX Hcd CM Hd Hn H2 H10 H19 H8 H20 H21 H22. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn.
    eexists. split.
    - stepb_ft F_160b0 D_160b0 ltac:(condZ).
      sn F_160b4 D_160b4. sn F_160b8 D_160b8. sn F_160bc D_160bc.
      stepb_ft F_1512c D_1512c ltac:(condZ).
      stepLD F_15130 D_15130 (Z_to_le_bytes 4 (p_d vd)) (Z_to_bv 64 (p_d vd)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vd)) by lia.
      stepret F_15134 D_15134 (0x161c4 : word) ltac:(bveq).
      sn F_160c0 D_160c0. stepb_ft F_160c4 D_160c4 ltac:(condZ).
      sn F_160c8 D_160c8. sn F_160cc D_160cc. sn F_160d0 D_160d0. sn F_160d4 D_160d4.
      stepb_ft F_160d8 D_160d8 ltac:(pin; rewrite (depth_mask_278 (p_d vd) Hd); reflexivity).
      sn F_160dc D_160dc. sn F_160e0 D_160e0.
      stepb_ft F_1598c D_1598c ltac:(condZ).
      stepLD F_15990 D_15990 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepret F_15994 D_15994 (0x161e8 : word) ltac:(bveq).
      stepb_ft F_160e4 D_160e4 ltac:(condZ).
      sn F_160e8 D_160e8. zv F_160ec D_160ec (Z_to_bv 64 (s - 132)). sn F_160f0 D_160f0. sn F_160f4 D_160f4. sn F_160f8 D_160f8. sn F_160fc D_160fc.
      sn F_16100 D_16100.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_of : forall m (a : word) b, m a = Some b -> rdn SEGS m a 1 = Some [b].
  Proof. intros m a b E. cbn [rdn]. rewrite E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma gi_loop : forall c regs m (arr p n i : Z) (ret : word),
    (1 <= arr)%Z -> (arr + 4 * n < 2 ^ 64)%Z -> (0 <= i)%Z -> (Z.of_nat (S c) = n - i)%Z -> (1 <= p)%Z -> (p + 4 <= 2 ^ 64)%Z ->
    (forall a : word, (arr <= u a < arr + 4 * n)%Z -> m a <> None) ->
    store_ok SEGS m (Z_to_bv 64 p) 4 = true -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 17 = Z_to_bv 64 (arr + 1 + 4 * i) -> getr regs 16 = Z_to_bv 64 i -> getr regs 15 = Z_to_bv 64 (n - i) ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x15a08 : word) m rom) (mkst regs' ret m' rom)
      /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = m)
           \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < n)%Z /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
      /\ regs_agree (fun r => In r [5; 10; 15; 16; 17]%list) regs regs'.
  Proof.
    induction c as [|c IH]; intros regs m arr p n i ret Harr Harr64 Hi Hc Hp Hp64 DEF SOK H1 Hret H17 H16 H15 H10 H14 H11 H12 H13.
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i + 1))) as [b2|] eqn:E2; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i + 1)) ltac:(rewrite u_Z2bv by lia; lia) E2)].
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i))) as [b1|] eqn:E1; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i)) ltac:(rewrite u_Z2bv by lia; lia) E1)].
    all: destruct (m (Z_to_bv 64 (arr + 1 + 4 * i - 1))) as [b0|] eqn:E0; [| exfalso; exact (DEF (Z_to_bv 64 (arr + 1 + 4 * i - 1)) ltac:(rewrite u_Z2bv by lia; lia) E0)].
    all: pose proof (rdn1_of m _ _ E2) as R2; pose proof (rdn1_of m _ _ E1) as R1; pose proof (rdn1_of m _ _ E0) as R0.
    all: pose proof (u_byte64 b2) as U2; pose proof (u_byte64 b1) as U1; pose proof (u_byte64 b0) as U0.
    - (* [comment removed for export] *)
      destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b2))) eqn:Hc2;
        [destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b1))) eqn:Hc1;
           [destruct (c_eq (Z_to_bv 64 100) (Z_to_bv 64 (bv_unsigned b0))) eqn:Hc0 |] |].
      + (* [comment removed for export] *)
        eexists. eexists. split; [| split; [right; split; [| exists i; split; [lia | reflexivity]] |]].
        * stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
          stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
          stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15910 D_15910 ltac:(pin; exact Hc1).
          stepLBU F_15914 D_15914 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_ft F_15918 D_15918 ltac:(pin; exact Hc0).
          sn F_1591c D_1591c.
          stepST F_15920 D_15920 (Z_to_bv 64 p) (Z_to_bv 64 i) ltac:(store_ok_peel; exact SOK).
          stepret F_15924 D_15924 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. reflexivity.
        * solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
          stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
          stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15910 D_15910 ltac:(pin; exact Hc1).
          stepLBU F_15914 D_15914 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_tk F_15918 D_15918 ltac:(pin; exact Hc0).
          zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15900 D_15900 ltac:(condZ).
          stepret F_15954 D_15954 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
          stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
          stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_tk F_15910 D_15910 ltac:(pin; exact Hc1).
          zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15900 D_15900 ltac:(condZ).
          stepret F_15954 D_15954 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * solve_regs_agree.
      + eexists. exists m. split; [| split; [left; split; [| reflexivity] |]].
        * stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
          stepb_tk F_15908 D_15908 ltac:(pin; exact Hc2).
          zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
          stepb_tk F_15900 D_15900 ltac:(condZ).
          stepret F_15954 D_15954 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. pin. reflexivity.
        * solve_regs_agree.
    - (* [comment removed for export] *)
      assert (STEP : forall r1, getr r1 17 = Z_to_bv 64 (arr + 1 + 4 * (i + 1)) -> getr r1 16 = Z_to_bv 64 (i + 1) -> getr r1 15 = Z_to_bv 64 (n - i - 1) ->
                getr r1 1 = ret -> regs_agree (fun r => In r [5; 15; 16; 17]%list) regs r1 ->
                msteps SEGS (mkst regs (0x15a08 : word) m rom) (mkst r1 (0x15a08 : word) m rom) ->
                exists regs' m',
                  msteps SEGS (mkst regs (0x15a08 : word) m rom) (mkst regs' ret m' rom)
                  /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = m)
                       \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < n)%Z /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
                  /\ regs_agree (fun r => In r [5; 10; 15; 16; 17]%list) regs regs').
      { intros r1 Q17 Q16 Q15 Q1 AG1 S1.
        destruct (IH r1 m arr p n (i + 1)%Z ret Harr Harr64 ltac:(lia) ltac:(lia) Hp Hp64 DEF SOK Q1 Hret Q17 Q16 ltac:(rewrite Q15; f_equal; lia)
                    ltac:(rewrite (AG1 10) by notin_list; exact H10) ltac:(rewrite (AG1 14) by notin_list; exact H14)
                    ltac:(rewrite (AG1 11) by notin_list; exact H11) ltac:(rewrite (AG1 12) by notin_list; exact H12) ltac:(rewrite (AG1 13) by notin_list; exact H13))
          as (r2 & m2 & S2 & RES & AG2).
        exists r2, m2. split; [| split; [exact RES|]].
        - eapply msteps_trans; [exact S1|]. exact S2.
        - eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2]. }
      destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b2))) eqn:Hc2;
        [destruct (c_eq (Z_to_bv 64 255) (Z_to_bv 64 (bv_unsigned b1))) eqn:Hc1;
           [destruct (c_eq (Z_to_bv 64 100) (Z_to_bv 64 (bv_unsigned b0))) eqn:Hc0 |] |].
      + (* [comment removed for export] *)
        eexists. eexists. split; [| split; [right; split; [| exists i; split; [lia | reflexivity]] |]].
        * stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
          stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
          stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
          stepb_ft F_15910 D_15910 ltac:(pin; exact Hc1).
          stepLBU F_15914 D_15914 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
          stepb_ft F_15918 D_15918 ltac:(pin; exact Hc0).
          sn F_1591c D_1591c.
          stepST F_15920 D_15920 (Z_to_bv 64 p) (Z_to_bv 64 i) ltac:(store_ok_peel; exact SOK).
          stepret F_15924 D_15924 ret ltac:(pin; reflexivity).
          apply mst_refl.
        * gres. reflexivity.
        * solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | ]).
        7:{ stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
            stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
            stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
            stepb_ft F_15910 D_15910 ltac:(pin; exact Hc1).
            stepLBU F_15914 D_15914 b0 ltac:(rdn_addr (arr + 1 + 4 * i - 1)%Z; exact R0).
            stepb_tk F_15918 D_15918 ltac:(pin; exact Hc0).
            zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15900 D_15900 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | ]).
        7:{ stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
            stepb_ft F_15908 D_15908 ltac:(pin; exact Hc2).
            stepLBU F_1590c D_1590c b1 ltac:(rdn_addr (arr + 1 + 4 * i)%Z; exact R1).
            stepb_tk F_15910 D_15910 ltac:(pin; exact Hc1).
            zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15900 D_15900 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. solve_regs_agree.
      + unshelve (eapply STEP; [ | | | | | ]).
        7:{ stepLBU F_15904 D_15904 b2 ltac:(rdn_addr (arr + 1 + 4 * i + 1)%Z; exact R2).
            stepb_tk F_15908 D_15908 ltac:(pin; exact Hc2).
            zv F_158f4 D_158f4 (Z_to_bv 64 (i + 1)). zv F_158f8 D_158f8 (Z_to_bv 64 (n - i - 1)). zv F_158fc D_158fc (Z_to_bv 64 (arr + 1 + 4 * (i + 1))).
            stepb_ft F_15900 D_15900 ltac:(condZ).
            apply mst_refl. }
        all: gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma gi_W : forall regs m (cd p : Z) (cv : cmapv) (ret : word),
    (1 <= cd)%Z -> CMAPat m cd cv -> (1 <= c_n cv)%Z -> (1 <= c_arr cv)%Z -> (c_arr cv + 4 * c_n cv < 2 ^ 64)%Z ->
    (1 <= p)%Z -> (p + 4 <= 2 ^ 64)%Z -> (cd + 24 <= p \/ p + 4 <= cd)%Z -> (c_arr cv + 4 * c_n cv <= p \/ p + 4 <= c_arr cv)%Z ->
    (forall a : word, (c_arr cv <= u a < c_arr cv + 4 * c_n cv)%Z -> m a <> None) ->
    store_ok SEGS m (Z_to_bv 64 p) 4 = true -> getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 14 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs' m',
      msteps SEGS (mkst regs (0x159cc : word) m rom) (mkst regs' ret m' rom)
      /\ ( (getr regs' 10 = Z_to_bv 64 1 /\ m' = wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0)))
           \/ (getr regs' 10 = Z_to_bv 64 0 /\ exists i', (0 <= i' < c_n cv)%Z /\
                 m' = wbytes (wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 i'))) )
      /\ regs_agree (fun r => In r [5; 10; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m cd p cv ret Hcd CM Hn Harr Harr64 Hp Hp64 DJc DJa DEF SOK H1 Hret H10 H14 H11 H12 H13.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_arr _ CWF) as Ra.
    set (m1 := wbytes m (Z_to_bv 64 p) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    assert (CM1 : CMAPat m1 cd cv) by (subst m1; apply CMAPat_out; [exact CM | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
    pose proof (CMAP_rd_n SEGS _ _ _ CM1) as Cn. pose proof (CMAP_rd_arr SEGS _ _ _ CM1) as Ca.
    assert (S1 : exists r1, msteps SEGS (mkst regs (0x159cc : word) m rom) (mkst r1 (0x15a08 : word) m1 rom)
                            /\ getr r1 17 = Z_to_bv 64 (c_arr cv + 1 + 4 * 0) /\ getr r1 16 = Z_to_bv 64 0 /\ getr r1 15 = Z_to_bv 64 (c_n cv - 0)
                            /\ getr r1 10 = Z_to_bv 64 1 /\ getr r1 1 = ret
                            /\ regs_agree (fun r => In r [10; 15; 16; 17]%list) regs r1).
    { eexists. split.
      - stepb_ft F_158c8 D_158c8 ltac:(condZ).
        subst m1. stepST F_158cc D_158cc (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOK).
        stepb_ft F_158d0 D_158d0 ltac:(condZ).
        sn F_158d4 D_158d4.
        stepLD F_158d8 D_158d8 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
        rewrite (v_lw_small (c_n cv)) by lia.
        sn F_158dc D_158dc.
        stepb_ft F_158e0 D_158e0 ltac:(condZ).
        sn F_158e4 D_158e4.
        stepLD F_158e8 D_158e8 (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Ca) ltac:(apply lez8; lia).
        zv F_158ec D_158ec (Z_to_bv 64 (c_arr cv + 1 + 4 * 0)).
        sn F_158f0 D_158f0.
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity; try (f_equal; lia). solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q17 & Q16 & Q15 & Q10 & Q1 & AG1).
    assert (DEF1 : forall a : word, (c_arr cv <= u a < c_arr cv + 4 * c_n cv)%Z -> m1 a <> None) by (intros a Ha; subst m1; apply wbytes_grows; exact (DEF a Ha)).
    assert (SOK1 : store_ok SEGS m1 (Z_to_bv 64 p) 4 = true).
    { subst m1. eapply store_ok_mono; [apply wbytes_grows | exact SOK]. }
    destruct (gi_loop (Z.to_nat (c_n cv - 1)) r1 m1 (c_arr cv) p (c_n cv) 0 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hp Hp64 DEF1 SOK1 Q1 Hret Q17 Q16 Q15 Q10
                ltac:(rewrite (AG1 14) by notin_list; exact H14) ltac:(rewrite (AG1 11) by notin_list; exact H11)
                ltac:(rewrite (AG1 12) by notin_list; exact H12) ltac:(rewrite (AG1 13) by notin_list; exact H13))
      as (r2 & m2 & S2 & RES & AG2).
    exists r2, m2. split; [| split; [exact RES|]].
    - eapply msteps_trans; [exact S1|]. exact S2.
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma ac_ok : forall regs m (cd : Z) (cv : cmapv) (ret : word),
    (1 <= cd)%Z -> CMAPat m cd cv -> (c_n cv < c_nalloc cv)%Z -> (1 <= c_arr cv)%Z -> (c_arr cv + 4 * c_nalloc cv < 2 ^ 64)%Z ->
    (cd + 24 <= c_arr cv \/ c_arr cv + 4 * c_nalloc cv <= cd)%Z ->
    store_ok SEGS m (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) 4 = true -> store_ok SEGS m (Z_to_bv 64 cd) 24 = true ->
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 cd -> getr regs 11 = Z_to_bv 64 255 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 100 ->
    exists regs',
      msteps SEGS (mkst regs (0x154ac : word) m rom)
                  (mkst regs' ret
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 100))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 1)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 255))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 2)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 255))])
                        (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 3)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 18446744073709551615))])
                        (Z_to_bv 64 (cd + 16)) (word_to_le_bytes 4 (Z_to_bv 64 (c_n cv + 1)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m cd cv ret Hcd CM Hn Harr Harr64 DJ SOKa SOKc H1 Hret H10 H11 H12 H13.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_nalloc _ CWF) as Rna. pose proof (cf_arr _ CWF) as Ra.
    pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn. pose proof (CMAP_rd_nalloc SEGS _ _ _ CM) as Cna. pose proof (CMAP_rd_arr SEGS _ _ _ CM) as Ca.
    eexists. split.
    - stepb_ft F_153a8 D_153a8 ltac:(condZ).
      stepLD F_153ac D_153ac (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact Cna) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepLD F_153b0 D_153b0 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_ft F_153b4 D_153b4 ltac:(condZ).
      sn F_153b8 D_153b8. sn F_153bc D_153bc.
      stepLD F_153c0 D_153c0 (Z_to_le_bytes 8 (c_arr cv)) (Z_to_bv 64 (c_arr cv)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Ca) ltac:(apply lez8; lia).
      zvs F_153c4 D_153c4 (Z_to_bv 64 (4 * c_n cv)).
      zva F_153c8 D_153c8 (Z_to_bv 64 (c_arr cv + 4 * c_n cv)).
      sn F_153cc D_153cc.
      zva F_153d0 D_153d0 (Z_to_bv 64 (c_n cv + 1)).
      stepST F_153d4 D_153d4 (Z_to_bv 64 (c_arr cv + 4 * c_n cv)) (Z_to_bv 64 100) ltac:(sok_in SOKa).
      stepST F_153d8 D_153d8 (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 1)) (Z_to_bv 64 255) ltac:(sok_in SOKa).
      stepST F_153dc D_153dc (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 2)) (Z_to_bv 64 255) ltac:(sok_in SOKa).
      stepST F_153e0 D_153e0 (Z_to_bv 64 (c_arr cv + 4 * c_n cv + 3)) (Z_to_bv 64 18446744073709551615) ltac:(sok_in SOKa).
      stepST F_153e4 D_153e4 (Z_to_bv 64 (cd + 16)) (Z_to_bv 64 (c_n cv + 1)) ltac:(sok_in SOKc).
      stepret F_153e8 D_153e8 ret ltac:(pin; reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ac_full : forall regs m (cd : Z) (cv : cmapv),
    (1 <= cd)%Z -> CMAPat m cd cv -> (c_nalloc cv <= c_n cv)%Z ->
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 cd ->
    exists regs',
      msteps SEGS (mkst regs (0x154ac : word) m rom) (mkst regs' (0x13db4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10b69 /\ getr regs' 11 = Z_to_bv 64 0x10abb /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 1 = getr regs 1 /\ getr regs' 2 = getr regs 2
      /\ regs_agree (fun r => In r [10; 11; 12; 14; 15]%list) regs regs'.
  Proof.
    intros regs m cd cv Hcd CM Hn Rg Rs H10.
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_n _ CWF) as Rn. pose proof (cf_nalloc _ CWF) as Rna.
    pose proof (CMAP_rd_n SEGS _ _ _ CM) as Cn. pose proof (CMAP_rd_nalloc SEGS _ _ _ CM) as Cna.
    eexists. split.
    - stepb_ft F_153a8 D_153a8 ltac:(condZ).
      stepLD F_153ac D_153ac (Z_to_le_bytes 4 (c_nalloc cv)) (Z_to_bv 64 (c_nalloc cv)) ltac:(addr_norm; exact Cna) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_nalloc cv)) by lia.
      stepLD F_153b0 D_153b0 (Z_to_le_bytes 4 (c_n cv)) (Z_to_bv 64 (c_n cv)) ltac:(addr_norm; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small (c_n cv)) by lia.
      stepb_tk F_153b4 D_153b4 ltac:(condZ).
      sn F_15418 D_15418.
      stepLD F_1541c D_1541c (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15420 D_15420 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15424 D_15424. stepb_ft F_15428 D_15428 ltac:(condZ).
      sn F_1542c D_1542c. sn F_15430 D_15430. sn F_15434 D_15434. sn F_15438 D_15438. sn F_1543c D_1543c. sn F_15440 D_15440.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_C0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x16208 : word) m rom) (mkst regs' (0x1632c : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_16104 D_16104 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_C1 : forall regs m (cd : Z),
    getr regs 10 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 cd ->
    getr regs 20 = Z_to_bv 64 100 -> getr regs 21 = Z_to_bv 64 255 -> getr regs 22 = Z_to_bv 64 255 ->
    exists regs', msteps SEGS (mkst regs (0x16208 : word) m rom) (mkst regs' (0x154ac : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x16220 /\ getr regs' 10 = Z_to_bv 64 cd /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 255 /\ getr regs' 13 = Z_to_bv 64 100
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m cd H10 H23 H20 H21 H22. eexists. split.
    - stepb_ft F_16104 D_16104 ltac:(condZ).
      sn F_16108 D_16108. sn F_1610c D_1610c. sn F_16110 D_16110. sn F_16114 D_16114. sn F_16118 D_16118.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_D0 : forall regs m (s n : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= n < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 24 = Z_to_bv 64 n ->
    exists regs', msteps SEGS (mkst regs (0x16220 : word) m rom) (mkst regs' (0x1632c : word) (wbytes m (Z_to_bv 64 (s - 132)) (word_to_le_bytes 4 (Z_to_bv 64 n))) rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m s n Hs Hs64 Hn SOK H2 H10 H24. eexists. split.
    - stepb_tk F_1611c D_1611c ltac:(condZ).
      stepST F_16224 D_16224 (Z_to_bv 64 (s - 132)) (Z_to_bv 64 n) ltac:(sok_in SOK).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_D1 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x20520) 8 = Some (Z_to_le_bytes 8 0x21590) -> rdn SEGS m (Z_to_bv 64 0x21590) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs', msteps SEGS (mkst regs (0x16220 : word) m rom) (mkst regs' (0x13db4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 1 = Z_to_bv 64 0x16560
      /\ getr regs' 10 = Z_to_bv 64 0x10c63 /\ getr regs' 11 = Z_to_bv 64 0x10d41 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_ft F_1611c D_1611c ltac:(condZ).
      sn F_16120 D_16120.
      stepLD F_16124 D_16124 (Z_to_le_bytes 8 0x21590) (Z_to_bv 64 0x21590) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_16128 D_16128 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_1612c D_1612c. stepb_ft F_16130 D_16130 ltac:(condZ).
      sn F_16134 D_16134. sn F_16138 D_16138. sn F_1613c D_1613c. sn F_16140 D_16140. sn F_16144 D_16144.
      sn F_16454 D_16454. sn F_16458 D_16458.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_J : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x16560 : word) m rom) (mkst regs' (0x16568 : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_1645c D_1645c; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma ss_dims : forall regs m (s pixd : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> PIXat m pixd vd -> (pixd + 64 <= s - 144)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x1632c : word) m rom)
      (mkst regs' (0x16340 : word)
         (wbytes (wbytes (wbytes (wbytes m
            (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
            (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
            (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vd))))
            (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 (p_h vd)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hs Hs64 Hp PX DJ SOK H2 H19. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh.
    pose proof (PIX_rd_w SEGS _ _ _ PX) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch.
    eexists. split.
    - zv F_16228 D_16228 (Z_to_bv 64 (s - 108)). zv F_1622c D_1622c (Z_to_bv 64 (s - 112)). sn F_16230 D_16230. sn F_16234 D_16234.
      sn F_16238 D_16238.
      stepb_ft F_14950 D_14950 ltac:(condZ).
      stepST F_14954 D_14954 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14958 D_14958 ltac:(condZ).
      stepST F_1495c D_1495c (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_14960 D_14960 ltac:(condZ).
      stepb_ft F_14968 D_14968 ltac:(condZ).
      stepb_ft F_1496c D_1496c ltac:(condZ).
      stepLD F_14970 D_14970 (Z_to_le_bytes 4 (p_w vd)) (Z_to_bv 64 (p_w vd)) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vd)) by lia.
      stepST F_14974 D_14974 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 (p_w vd)) ltac:(sok_in SOK).
      stepb_ft F_14978 D_14978 ltac:(condZ).
      stepLD F_1497c D_1497c (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; repeat rdn_peel1; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vd)) by lia.
      stepST F_14980 D_14980 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 (p_h vd)) ltac:(sok_in SOK).
      sn F_14984 D_14984.
      stepb_tk F_14988 D_14988 ltac:(condZ).
      sn F_14994 D_14994.
      stepret F_14998 D_14998 (0x16340 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_F : forall regs m (s bx : Z),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= bx)%Z -> (bx < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 18 = Z_to_bv 64 bx ->
    exists regs', msteps SEGS (mkst regs (0x16340 : word) m rom) (mkst regs' (0x142b8 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1635c /\ getr regs' 10 = Z_to_bv 64 bx
      /\ getr regs' 11 = Z_to_bv 64 (s - 116) /\ getr regs' 12 = Z_to_bv 64 (s - 120) /\ getr regs' 13 = Z_to_bv 64 (s - 124) /\ getr regs' 14 = Z_to_bv 64 (s - 128)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m s bx Hs Hs64 Hbx Hbx64 H2 H18. eexists. split.
    - stepb_ft F_1623c D_1623c ltac:(condZ).
      zv F_16240 D_16240 (Z_to_bv 64 (s - 116)). zv F_16244 D_16244 (Z_to_bv 64 (s - 120)). zv F_16248 D_16248 (Z_to_bv 64 (s - 124)). zv F_1624c D_1624c (Z_to_bv 64 (s - 128)).
      sn F_16250 D_16250. sn F_16254 D_16254.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_G : forall regs m (s pixd x1 y1 bw bh : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> PIXat m pixd vd ->
    (0 <= x1)%Z -> (0 <= y1)%Z -> (1 <= bw)%Z -> (1 <= bh)%Z -> (x1 + bw < 2 ^ 31)%Z -> (y1 + bh < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 x1) -> rdn SEGS m (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 y1) ->
    rdn SEGS m (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 bw) -> rdn SEGS m (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 bh) ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x1635c : word) m rom) (mkst regs' (0x163a4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 18 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 20 = Z_to_bv 64 (x1 + bw - 1) /\ getr regs' 21 = Z_to_bv 64 (y1 + bh - 1) /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 18; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixd x1 y1 bw bh vd Hs Hs64 Hp PX Hx1 Hy1 Hbw Hbh Hx Hy Rx1 Ry1 Rbw Rbh H2 H19.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. pose proof (wf_data _ WF) as Rd.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepLD F_16258 D_16258 (Z_to_le_bytes 4 x1) (Z_to_bv 64 x1) ltac:(addr_norm; exact Rx1) ltac:(apply lez4; lia). rewrite (v_lw_small x1) by lia.
      stepLD F_1625c D_1625c (Z_to_le_bytes 4 bw) (Z_to_bv 64 bw) ltac:(addr_norm; exact Rbw) ltac:(apply lez4; lia). rewrite (v_lw_small bw) by lia.
      stepLD F_16260 D_16260 (Z_to_le_bytes 4 y1) (Z_to_bv 64 y1) ltac:(addr_norm; exact Ry1) ltac:(apply lez4; lia). rewrite (v_lw_small y1) by lia.
      stepLD F_16264 D_16264 (Z_to_le_bytes 4 bh) (Z_to_bv 64 bh) ltac:(addr_norm; exact Rbh) ltac:(apply lez4; lia). rewrite (v_lw_small bh) by lia.
      zva F_16268 D_16268 (Z_to_bv 64 (x1 + bw)). zva F_1626c D_1626c (Z_to_bv 64 (y1 + bh)).
      sn F_16270 D_16270. fixv (Z_to_bv 64 (x1 + bw - 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_16274 D_16274. fixv (Z_to_bv 64 (y1 + bh - 1)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_16278 D_16278.
      sn F_1628c D_1628c. sn F_16290 D_16290.
      stepb_ft F_1516c D_1516c ltac:(condZ).
      stepLD F_15170 D_15170 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      stepret F_15174 D_15174 (0x16398 : word) ltac:(bveq).
      sn F_16294 D_16294. sn F_16298 D_16298. sn F_1629c D_1629c.
      stepb_ft F_1470c D_1470c ltac:(condZ).
      stepLD F_14710 D_14710 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_14714 D_14714 (0x163a4 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ss_F0 : forall regs m (s pixd w h : Z) (vd : pixv),
    (144 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> PIXat m pixd vd -> (pixd + 64 <= s - 144)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
    store_ok SEGS m (Z_to_bv 64 (s - 144)) 144 = true ->
    getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 18 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x16340 : word) m rom)
      (mkst regs' (0x163a4 : word)
         (wbytes (wbytes m (Z_to_bv 64 (s - 120)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 116)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 144) /\ getr regs' 10 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 18 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 20 = Z_to_bv 64 w /\ getr regs' 21 = Z_to_bv 64 h /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 18; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixd w h vd Hs Hs64 Hp PX DJ Hw Hh Rw Rh SOK H2 H18 H19.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rd.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_tk F_1623c D_1623c ltac:(condZ).
      stepLD F_1627c D_1627c (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply lez4; lia). rewrite (v_lw_small w) by lia.
      stepLD F_16280 D_16280 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply lez4; lia). rewrite (v_lw_small h) by lia.
      stepST F_16284 D_16284 (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepST F_16288 D_16288 (Z_to_bv 64 (s - 116)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1628c D_1628c. sn F_16290 D_16290.
      stepb_ft F_1516c D_1516c ltac:(condZ).
      stepLD F_15170 D_15170 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; repeat rdn_peel1; exact Cdata) ltac:(apply lez8; lia).
      stepret F_15174 D_15174 (0x16398 : word) ltac:(bveq).
      sn F_16294 D_16294. sn F_16298 D_16298. sn F_1629c D_1629c.
      stepb_ft F_1470c D_1470c ltac:(condZ).
      stepLD F_14710 D_14710 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; repeat rdn_peel1; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_14714 D_14714 (0x163a4 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End SelSegs.
