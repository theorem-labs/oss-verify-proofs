(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21LeptStderr V21LeptBase V21LeptUb.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21CL7a.
Import V21CL7a.V21LeptErr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21_code_136d4_14000 V21_code_14000_15000 V21_code_17000_18000 V21_code_18000_19000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition box_bytes (x y w h rc : Z) : list byte :=
  Z_to_le_bytes 4 x ++ Z_to_le_bytes 4 y ++ Z_to_le_bytes 4 w ++ Z_to_le_bytes 4 h ++ Z_to_le_bytes 4 rc.
Definition BOXat (m : word -> option byte) (b : Z) (x y w h rc : Z) : Prop :=
  (1 <= b)%Z /\ (b + 20 < 2 ^ 64)%Z /\ bytes_at m b (box_bytes x y w h rc).

Lemma box_bytes_len : forall x y w h rc, length (box_bytes x y w h rc) = 20%nat.
Proof. intros. unfold box_bytes. rewrite !length_app, !length_Z_to_le_bytes. reflexivity. Qed.

Lemma BOXat_defined : forall m b x y w h rc (a : word), BOXat m b x y w h rc -> (b <= bv_unsigned a < b + 20)%Z -> m a <> None.
Proof.
  intros m b x y w h rc a (Hb & Hb64 & B) Ha.
  pose proof (B (bv_unsigned a - b)%Z ltac:(rewrite box_bytes_len; lia)) as E.
  replace (Z_to_bv 64 (b + (bv_unsigned a - b))) with a in E by (apply bv_eq; rewrite u_Z2bv by lia; lia).
  rewrite E. discriminate.
Qed.

Lemma BOXat_frame : forall m m' b x y w h rc, BOXat m b x y w h rc ->
  (forall a : word, (b <= bv_unsigned a < b + 20)%Z -> m' a = m a) -> BOXat m' b x y w h rc.
Proof.
  intros m m' b x y w h rc (Hb & Hb64 & B) E. split; [exact Hb|]. split; [exact Hb64|].
  apply (bytes_at_frame m m' b _ B); [| lia | rewrite box_bytes_len; cbn; lia]. intros a Ha. rewrite box_bytes_len in Ha. apply E. cbn in Ha. lia.
Qed.

Lemma BOX_rd_rc : forall m b x y w h rc, BOXat m b x y w h rc -> rdn SEGS m (Z_to_bv 64 (b + 16)) 4 = Some (Z_to_le_bytes 4 rc).
Proof.
  intros m b x y w h rc (Hb & Hb64 & B).
  exact (bytes_at_field SEGS m b (box_bytes x y w h rc) 16 4 ltac:(lia) ltac:(rewrite box_bytes_len; lia) ltac:(rewrite box_bytes_len; cbn; lia) B).
Qed.
Lemma BOX_rd_x : forall m b x y w h rc, BOXat m b x y w h rc -> rdn SEGS m (Z_to_bv 64 b) 4 = Some (Z_to_le_bytes 4 x).
Proof.
  intros m b x y w h rc (Hb & Hb64 & B).
  pose proof (bytes_at_field SEGS m b (box_bytes x y w h rc) 0 4 ltac:(lia) ltac:(rewrite box_bytes_len; lia) ltac:(rewrite box_bytes_len; cbn; lia) B) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.
Lemma BOX_rd_y : forall m b x y w h rc, BOXat m b x y w h rc -> rdn SEGS m (Z_to_bv 64 (b + 4)) 4 = Some (Z_to_le_bytes 4 y).
Proof.
  intros m b x y w h rc (Hb & Hb64 & B).
  exact (bytes_at_field SEGS m b (box_bytes x y w h rc) 4 4 ltac:(lia) ltac:(rewrite box_bytes_len; lia) ltac:(rewrite box_bytes_len; cbn; lia) B).
Qed.
Lemma BOX_rd_w : forall m b x y w h rc, BOXat m b x y w h rc -> rdn SEGS m (Z_to_bv 64 (b + 8)) 4 = Some (Z_to_le_bytes 4 w).
Proof.
  intros m b x y w h rc (Hb & Hb64 & B).
  exact (bytes_at_field SEGS m b (box_bytes x y w h rc) 8 4 ltac:(lia) ltac:(rewrite box_bytes_len; lia) ltac:(rewrite box_bytes_len; cbn; lia) B).
Qed.
Lemma BOX_rd_h : forall m b x y w h rc, BOXat m b x y w h rc -> rdn SEGS m (Z_to_bv 64 (b + 12)) 4 = Some (Z_to_le_bytes 4 h).
Proof.
  intros m b x y w h rc (Hb & Hb64 & B).
  exact (bytes_at_field SEGS m b (box_bytes x y w h rc) 12 4 ltac:(lia) ltac:(rewrite box_bytes_len; lia) ltac:(rewrite box_bytes_len; cbn; lia) B).
Qed.

(* [comment removed for export] *)
Lemma BOXat_zero : forall m b, (1 <= b)%Z -> (b + 20 < 2 ^ 64)%Z ->
  (forall i, (0 <= i < 20)%Z -> m (Z_to_bv 64 (b + i)) = Some (Z_to_bv 8 0)) -> BOXat m b 0 0 0 0 0.
Proof.
  intros m b Hb Hb64 Z0. split; [lia|]. split; [lia|].
  change (box_bytes 0 0 0 0 0) with (repeat (Z_to_bv 8 0) 20). apply bytes_at_zeros. exact Z0.
Qed.

Local Ltac bwr HP off z :=
  lazymatch type of HP with BOXat ?m ?b ?x ?y ?w ?h ?rc =>
  destruct HP as (?Hp & ?Hn & ?HB);
  split; [lia|]; split; [lia|];
  let H := fresh in
  pose proof (bytes_at_wbytes_in m b (box_bytes x y w h rc) off (Z_to_le_bytes 4 z) HB ltac:(lia) ltac:(rewrite box_bytes_len; cbn; lia)
                ltac:(rewrite box_bytes_len, length_Z_to_le_bytes; cbn; lia)) as H;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H; rewrite ?Z.add_0_r in H;
  rewrite w2b_Z by lia; exact H end.

Lemma BOX_wr_x : forall m b x y w h rc z, BOXat m b x y w h rc -> (0 <= z < 2 ^ 31)%Z ->
  BOXat (wbytes m (Z_to_bv 64 b) (word_to_le_bytes 4 (Z_to_bv 64 z))) b z y w h rc.
Proof. intros m b x y w h rc z HP Hz. bwr HP 0%nat z. Qed.
Lemma BOX_wr_y : forall m b x y w h rc z, BOXat m b x y w h rc -> (0 <= z < 2 ^ 31)%Z ->
  BOXat (wbytes m (Z_to_bv 64 (b + 4)) (word_to_le_bytes 4 (Z_to_bv 64 z))) b x z w h rc.
Proof. intros m b x y w h rc z HP Hz. bwr HP 4%nat z. Qed.
Lemma BOX_wr_w : forall m b x y w h rc z, BOXat m b x y w h rc -> (0 <= z < 2 ^ 31)%Z ->
  BOXat (wbytes m (Z_to_bv 64 (b + 8)) (word_to_le_bytes 4 (Z_to_bv 64 z))) b x y z h rc.
Proof. intros m b x y w h rc z HP Hz. bwr HP 8%nat z. Qed.
Lemma BOX_wr_h : forall m b x y w h rc z, BOXat m b x y w h rc -> (0 <= z < 2 ^ 31)%Z ->
  BOXat (wbytes m (Z_to_bv 64 (b + 12)) (word_to_le_bytes 4 (Z_to_bv 64 z))) b x y w z rc.
Proof. intros m b x y w h rc z HP Hz. bwr HP 12%nat z. Qed.
Lemma BOX_wr_rc : forall m b x y w h rc z, BOXat m b x y w h rc -> (0 <= z < 2 ^ 31)%Z ->
  BOXat (wbytes m (Z_to_bv 64 (b + 16)) (word_to_le_bytes 4 (Z_to_bv 64 z))) b x y w h z.
Proof. intros m b x y w h rc z HP Hz. bwr HP 16%nat z. Qed.

Section Box.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FR5 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  (* [comment removed for export] *)
  Lemma bc_A : forall regs m (s : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    getr regs 10 = Z_to_bv 64 278 -> getr regs 11 = Z_to_bv 64 35 -> getr regs 12 = Z_to_bv 64 122 -> getr regs 13 = Z_to_bv 64 50 ->
    exists regs',
      msteps SEGS (mkst regs (0x14158 : word) m rom) (mkst regs' (0x181d4 : word) (FR5 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x141b4
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 20
      /\ getr regs' 8 = Z_to_bv 64 50 /\ getr regs' 9 = Z_to_bv 64 122 /\ getr regs' 18 = Z_to_bv 64 35 /\ getr regs' 19 = Z_to_bv 64 278
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10 H11 H12 H13. unfold FR5. eexists. split.
    - zv F_14054 D_14054 (Z_to_bv 64 (s - 48)).
      stepST F_14058 D_14058 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1405c D_1405c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14060 D_14060 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_14064 D_14064 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_14068 D_14068 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      sn F_1406c D_1406c. stepat F_14070 D_14070 (Z_to_bv 64 122) ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
      stepb_ft F_14074 D_14074 ltac:(condZ).
      sn F_14078 D_14078. sn F_1407c D_1407c. sn F_14080 D_14080.
      stepb_tk F_14084 D_14084 ltac:(condZ).
      stepb_tk F_14094 D_14094 ltac:(condZ).
      sn F_140a4 D_140a4. sn F_140a8 D_140a8. sn F_140ac D_140ac.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bc_B : forall regs m (s bx : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= bx)%Z -> (bx + 20 < 2 ^ 64)%Z -> (bx mod 16 = 0)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 bx) 20 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    (bx + 20 <= s - 48 \/ s <= bx)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 bx ->
    getr regs 8 = Z_to_bv 64 50 -> getr regs 9 = Z_to_bv 64 122 -> getr regs 18 = Z_to_bv 64 35 -> getr regs 19 = Z_to_bv 64 278 ->
    exists regs',
      msteps SEGS (mkst regs (0x141b4 : word) m rom)
                  (mkst regs' ret
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 bx) (word_to_le_bytes 4 (Z_to_bv 64 278)))
                        (Z_to_bv 64 (bx + 4)) (word_to_le_bytes 4 (Z_to_bv 64 35)))
                        (Z_to_bv 64 (bx + 8)) (word_to_le_bytes 4 (Z_to_bv 64 122)))
                        (Z_to_bv 64 (bx + 12)) (word_to_le_bytes 4 (Z_to_bv 64 50)))
                        (Z_to_bv 64 (bx + 16)) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 bx
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s bx ret s0v s1v s2v s3v Hs Hs64 Hbx Hbx64 Hal16 Hret SOK R8 R16 R24 R32 R40 DJ H2 H10 H8 H9 H18 H19.
    assert (AL4 : (bx mod 4 = 0)%Z) by (apply al16_mod4; exact Hal16).
    eexists. split.
    - stepb_ft F_140b0 D_140b0 ltac:(condZ).
      guard4 F_140b4 D_140b4 AL4. stepb_ft F_140b8 D_140b8 ltac:(condZ). (* [comment removed for export] *)
      sn F_140bc D_140bc.
      stepST F_140c0 D_140c0 (Z_to_bv 64 bx) (Z_to_bv 64 278) ltac:(sok_in SOK).
      stepST F_140c4 D_140c4 (Z_to_bv 64 (bx + 4)) (Z_to_bv 64 35) ltac:(sok_in SOK).
      stepb_ft F_140c8 D_140c8 ltac:(condZ).
      stepST F_140cc D_140cc (Z_to_bv 64 (bx + 8)) (Z_to_bv 64 122) ltac:(sok_in SOK).
      stepb_ft F_140d0 D_140d0 ltac:(condZ).
      stepST F_140d4 D_140d4 (Z_to_bv 64 (bx + 12)) (Z_to_bv 64 50) ltac:(sok_in SOK).
      stepfence F_140d8 D_140d8.
      sn F_140dc D_140dc.
      stepST F_140e0 D_140e0 (Z_to_bv 64 (bx + 16)) (Z_to_bv 64 1) ltac:(sok_in SOK).
      stepfence F_140e4 D_140e4.
      sn F_140e8 D_140e8.
      stepLD8 F_14184 D_14184 ret. stepLD8 F_14188 D_14188 s0v. stepLD8 F_1418c D_1418c s1v.
      stepLD8 F_14190 D_14190 s2v. stepLD8 F_14194 D_14194 s3v.
      zv F_14198 D_14198 (Z_to_bv 64 s). stepret F_1419c D_1419c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  Lemma bd_null : forall regs m (pp : Z) (ret : word),
    (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs', msteps SEGS (mkst regs (0x142d4 : word) m rom) (mkst regs' ret m rom)
      /\ regs_agree (fun r => In r [11]%list) regs regs'.
  Proof.
    intros regs m pp ret Hpp Hpp64 ALpp Hret Rpp H1 H10. eexists. split.
    - stepb_ft F_141d0 D_141d0 ltac:(condZ).
      guard8 F_141d4 D_141d4 ALpp. stepb_ft F_141d8 D_141d8 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_141dc D_141dc (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Rpp) ltac:(apply lez8; lia).
      stepb_tk F_141e0 D_141e0 ltac:(condZ).
      stepret F_14258 D_14258 ret ltac:(pin; reflexivity). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_A : forall regs m (s pp bx : Z) (x y w h : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> (bx mod 16 = 0)%Z -> (4096 <= bx)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true -> store_ok SEGS m (Z_to_bv 64 bx) 20 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 bx) -> BOXat m bx x y w h 1 ->
    (bx + 20 <= s - 16 \/ s <= bx)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x142d4 : word) m rom)
                  (mkst regs' (0x1830c : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (bx + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x1431c /\ getr regs' 10 = Z_to_bv 64 bx /\ getr regs' 8 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pp bx x y w h ret Hs Hs64 Hpp Hpp64 ALpp Hal Hbx SOK SOKb Rpp BX DJ H2 H1 H10. pose proof BX as (Hb1 & Hb64 & _).
    assert (AL4 : (bx mod 4 = 0)%Z) by (apply al16_mod4; exact Hal).
    eexists. split.
    - stepb_ft F_141d0 D_141d0 ltac:(condZ).
      guard8 F_141d4 D_141d4 ALpp. stepb_ft F_141d8 D_141d8 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_141dc D_141dc (Z_to_le_bytes 8 bx) (Z_to_bv 64 bx) ltac:(addr_norm; exact Rpp) ltac:(apply lez8; lia).
      stepb_ft F_141e0 D_141e0 ltac:(condZ).
      guard4 F_141e4 D_141e4 AL4. stepb_ft F_141e8 D_141e8 ltac:(condZ). (* [comment removed for export] *)
      zv F_141ec D_141ec (Z_to_bv 64 (bx + 16)).
      sn F_141f0 D_141f0.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_141f4 eq_refl D_141f4);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; exact (BOX_rd_rc m bx x y w h 1 BX)
          | apply lez4; lia
          | gres; sok_in SOKb ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_141f8 D_141f8.
      stepb_ft F_141fc D_141fc ltac:(condZ).
      zv F_14200 D_14200 (Z_to_bv 64 (s - 16)).
      stepST F_14204 D_14204 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14208 D_14208 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      sn F_1420c D_1420c. sn F_14210 D_14210. sn F_14214 D_14214.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bd_C : forall regs m (s pp : Z) (ret s0v : word),
    (16 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1431c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 10 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v Hs Hpp Hpp64 Hret R8 R16 SOKp H2 H8. eexists. split.
    - sn F_14218 D_14218.
      stepLD8 F_1421c D_1421c ret. stepLD8 F_14220 D_14220 s0v.
      zv F_14224 D_14224 (Z_to_bv 64 s).
      stepST F_14228 D_14228 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(store_ok_peel; exact SOKp).
      sn F_1422c D_1422c.
      stepret F_14258 D_14258 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bg_seg : forall regs m (bx x y w h px py pw ph : Z) (ret : word),
    (0 <= x < 2 ^ 31)%Z -> (0 <= y < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z ->
    BOXat m bx x y w h 1 -> (4096 <= bx)%Z -> (bx mod 16 = 0)%Z -> (ph mod 4 = 0)%Z ->
    (1 <= ph)%Z -> (ph + 4 = pw)%Z -> (pw + 4 = py)%Z -> (py + 4 = px)%Z -> (px + 4 <= 2 ^ 64)%Z ->
    (bx + 20 <= ph \/ px + 4 <= bx)%Z ->
    store_ok SEGS m (Z_to_bv 64 ph) 16 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 bx -> getr regs 11 = Z_to_bv 64 px -> getr regs 12 = Z_to_bv 64 py ->
    getr regs 13 = Z_to_bv 64 pw -> getr regs 14 = Z_to_bv 64 ph ->
    exists regs',
      msteps SEGS (mkst regs (0x14364 : word) m rom)
                  (mkst regs' ret
                     (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 px) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 py) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 pw) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 ph) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                        (Z_to_bv 64 px) (word_to_le_bytes 4 (Z_to_bv 64 x)))
                        (Z_to_bv 64 py) (word_to_le_bytes 4 (Z_to_bv 64 y)))
                        (Z_to_bv 64 pw) (word_to_le_bytes 4 (Z_to_bv 64 w)))
                        (Z_to_bv 64 ph) (word_to_le_bytes 4 (Z_to_bv 64 h))) rom)
      /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 15]%list) regs regs'.
  Proof.
    intros regs m bx x y w h px py pw ph ret Hx Hy Hw Hh BX Hbx ALbx ALph Hph E1 E2 E3 Hpx DJ SOK Hret H1 H10 H11 H12 H13 H14.
    pose proof BX as (Hb1 & Hb64 & B).
    assert (ALpw : (pw mod 4 = 0)%Z) by (rewrite <- E1; apply al4_plus_mod4; [exact ALph | reflexivity]).
    assert (ALpy : (py mod 4 = 0)%Z) by (rewrite <- E2; apply al4_plus_mod4; [exact ALpw | reflexivity]).
    assert (ALpx : (px mod 4 = 0)%Z) by (rewrite <- E3; apply al4_plus_mod4; [exact ALpy | reflexivity]).
    assert (ALb4 : (bx mod 4 = 0)%Z) by (apply al16_mod4; exact ALbx).
    pose proof (Z_lor_range64 bx px ltac:(lia) ltac:(lia)) as ORr1. pose proof (Z_lor_range64 bx py ltac:(lia) ltac:(lia)) as ORr2.
    pose proof (Z_lor_range64 bx pw ltac:(lia) ltac:(lia)) as ORr3. pose proof (Z_lor_range64 bx ph ltac:(lia) ltac:(lia)) as ORr4.
    pose proof (lor_mod4_0 bx px ltac:(lia) ltac:(lia) ALb4 ALpx) as OR1.
    pose proof (lor_mod4_0 bx py ltac:(lia) ltac:(lia) ALb4 ALpy) as OR2.
    pose proof (lor_mod4_0 bx pw ltac:(lia) ltac:(lia) ALb4 ALpw) as OR3.
    pose proof (lor_mod4_0 bx ph ltac:(lia) ltac:(lia) ALb4 ALph) as OR4.
    pose proof (BOX_rd_x m bx x y w h 1 BX) as Rx. pose proof (BOX_rd_y m bx x y w h 1 BX) as Ry.
    pose proof (BOX_rd_w m bx x y w h 1 BX) as Rw. pose proof (BOX_rd_h m bx x y w h 1 BX) as Rh.
    eexists. split.
    - stepb_ft F_14260 D_14260 ltac:(condZ).
      guard4 F_14264 D_14264 ALpx. stepb_ft F_14268 D_14268 ltac:(condZ). (* [comment removed for export] *)
      stepST F_1426c D_1426c (Z_to_bv 64 px) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14270 D_14270 ltac:(condZ).
      guard4 F_14274 D_14274 ALpy. stepb_ft F_14278 D_14278 ltac:(condZ). (* [comment removed for export] *)
      stepST F_1427c D_1427c (Z_to_bv 64 py) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14280 D_14280 ltac:(condZ).
      guard4 F_14284 D_14284 ALpw. stepb_ft F_14288 D_14288 ltac:(condZ). (* [comment removed for export] *)
      stepST F_1428c D_1428c (Z_to_bv 64 pw) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_14290 D_14290 ltac:(condZ).
      guard4 F_14294 D_14294 ALph. stepb_ft F_14298 D_14298 ltac:(condZ). (* [comment removed for export] *)
      stepST F_1429c D_1429c (Z_to_bv 64 ph) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_142a0 D_142a0 ltac:(condZ).
      stepb_ft F_142a4 D_142a4 ltac:(condZ).
      orv F_142a8 D_142a8 bx px. guard4 F_142ac D_142ac OR1. stepb_ft F_142b0 D_142b0 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_142b4 D_142b4 (Z_to_le_bytes 4 x) (Z_to_bv 64 x) ltac:(addr_norm; repeat rdn_peel1; exact Rx) ltac:(apply lez4; lia).
      rewrite (v_lw_small x) by lia.
      stepST F_142b8 D_142b8 (Z_to_bv 64 px) (Z_to_bv 64 x) ltac:(sok_in SOK).
      stepb_ft F_142bc D_142bc ltac:(condZ).
      orv F_142c0 D_142c0 bx py. guard4 F_142c4 D_142c4 OR2. stepb_ft F_142c8 D_142c8 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_142cc D_142cc (Z_to_le_bytes 4 y) (Z_to_bv 64 y) ltac:(addr_norm; repeat rdn_peel1; exact Ry) ltac:(apply lez4; lia).
      rewrite (v_lw_small y) by lia.
      stepST F_142d0 D_142d0 (Z_to_bv 64 py) (Z_to_bv 64 y) ltac:(sok_in SOK).
      stepb_ft F_142d4 D_142d4 ltac:(condZ).
      orv F_142d8 D_142d8 bx pw. guard4 F_142dc D_142dc OR3. stepb_ft F_142e0 D_142e0 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_142e4 D_142e4 (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(addr_norm; repeat rdn_peel1; exact Rw) ltac:(apply lez4; lia).
      rewrite (v_lw_small w) by lia.
      stepST F_142e8 D_142e8 (Z_to_bv 64 pw) (Z_to_bv 64 w) ltac:(sok_in SOK).
      stepb_ft F_142ec D_142ec ltac:(condZ).
      orv F_142f0 D_142f0 bx ph. guard4 F_142f4 D_142f4 OR4. stepb_ft F_142f8 D_142f8 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_142fc D_142fc (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; repeat rdn_peel1; exact Rh) ltac:(apply lez4; lia).
      rewrite (v_lw_small h) by lia.
      stepST F_14300 D_14300 (Z_to_bv 64 ph) (Z_to_bv 64 h) ltac:(sok_in SOK).
      sn F_14304 D_14304.
      stepret F_14308 D_14308 ret ltac:(pin; reflexivity). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_boxCreate : str16 0x1034c 9. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition box_new (C : lctx) (A A' : AS) (m' : word -> option byte) (bx : Z) : Prop :=
  (4096 <= bx)%Z /\ (bx + 32 <= alloc_top (c_vm C))%Z /\ (bx mod 16 = 0)%Z /\
  live A (Z_to_bv 64 bx) = None /\ live (c_A0 C) (Z_to_bv 64 bx) = None /\ live A' (Z_to_bv 64 bx) = Some 20%Z /\
  (forall q, q <> Z_to_bv 64 bx -> live A' q = live A q) /\
  BOXat m' bx 278 35 122 50 1.

Theorem boxCreate_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x32220 ->
  getr regs 10 = Z_to_bv 64 278 -> getr regs 11 = Z_to_bv 64 35 -> getr regs 12 = Z_to_bv 64 122 -> getr regs 13 = Z_to_bv 64 50 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_box <= kR)%Z -> (RB_box <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists bx : Z, getr regs' 10 = Z_to_bv 64 bx /\ box_new C A A' m' bx) ) ->
     aroom A' vm' (kR - RK_box) (bR - RB_box) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14158 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_le (1 * 20)) as HAM.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  destruct (bc_A al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR5 m s ret regs) in *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x181d4 : word) with (Z_to_bv 64 0x181d4) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 20 kR bR (Z_to_bv 64 0x141b4) (s - 48) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(unfold RK_box in Hrk; lia) ltac:(unfold RB_box in Hrb; lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0x141b4) with (0x141b4 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (E8a : getr r2 8 = Z_to_bv 64 50) by (csr; reflexivity).
  assert (E9a : getr r2 9 = Z_to_bv 64 122) by (csr; reflexivity).
  assert (E18a : getr r2 18 = Z_to_bv 64 35) by (csr; reflexivity).
  assert (E19a : getr r2 19 = Z_to_bv 64 278) by (csr; reflexivity).
  (* [comment removed for export] *)
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 48) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. unfold FR5. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 48) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. unfold FR5. rdn_solve. }
  assert (R24 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 48) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. unfold FR5. rdn_solve. }
  assert (R32 : rdn SEGS m1 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))).
  { rewrite (FRM_rdn16 C (s - 48) M1 m1 (s - 32) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. unfold FR5. rdn_solve. }
  assert (R40 : rdn SEGS m1 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))).
  { rewrite (FRM_rdn16 C (s - 48) M1 m1 (s - 40) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. unfold FR5. rdn_solve. }
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  (* [comment removed for export] *)
    assert (Hbx : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
    { pose proof (u64_range res). unfold round16 in TOP. change ((1 * 20 + 15) / 16)%Z with 2%Z in TOP. lia. }
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
    set (bx := u res) in *. clearbody bx.
    rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    destruct (blk_range C A1 m1 _ (Z_to_bv 64 bx) 20 CK HWa L1 ltac:(lia)) as [Gbx _]. rewrite u_Z2bv in Gbx by lia.
    assert (BX0 : BOXat m1 bx 0 0 0 0 0).
    { apply BOXat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
    assert (SOKb : store_ok SEGS m1 (Z_to_bv 64 bx) 20 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (BOXat_defined m1 bx 0 0 0 0 0 x BX0 ltac:(lia) E). }
    destruct (bc_B al_rom r2 m1 s bx ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL16 Hret
                SOKb R8 R16 R24 R32 R40 ltac:(lia) E2a Hres E8a E9a E18a E19a)
      as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M2 := wbytes (wbytes (wbytes (wbytes (wbytes m1 _ _) _ _) _ _) _ _) _ _).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
    { subst M2.
      do 5 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 bx) _ 20); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      split; [exact HWa | exact PMa']. }
    destruct WP2 as [HW2 PM2].
    apply (HK A1 M2 vm1 r3).
    + exact HW2.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?V19; reflexivity.
    + exact PM2.
    + right. exists bx. split; [exact V10|].
      unfold box_new. split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [exact L0|]. split; [exact L00|]. split; [exact L1|]. split; [exact LEQ|].
      subst M2. replace (Z_to_bv 64 bx) with (Z_to_bv 64 bx) by reflexivity.
      eapply BOX_wr_rc; [|lia]. eapply BOX_wr_h; [|lia]. eapply BOX_wr_w; [|lia]. eapply BOX_wr_y; [|lia]. eapply BOX_wr_x; [exact BX0|lia].
    + room_tac.
Qed.

(* [comment removed for export] *)
Theorem boxDestroy_null_W : forall C A m md regs (pp : Z) (ret : word) (S : TSet),
  W C A m md -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall regs', cs_kept regs regs' -> realizes SEGS (mkCfg (mkst regs' ret m al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x142d4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs pp ret S HW Hpp Hpp64 ALpp H1 Hret H10 Rpp HK.
  destruct (bd_null al_rom regs m pp ret Hpp Hpp64 ALpp Hret Rpp H1 H10) as (r1 & RUN1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply HK. apply cs_kept_intro; csr; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem boxDestroy_W : forall C A m md regs (s pp bx : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 16 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x32220 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 bx) ->
  BOXat m bx 278 35 122 50 1 -> live A (Z_to_bv 64 bx) = Some 20%Z -> live (c_A0 C) (Z_to_bv 64 bx) = None ->
  (forall A' m' vm' regs', W C A' (wbytes m' (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 bx) = None -> (forall q, q <> Z_to_bv 64 bx -> live A' q = live A q) ->
     POSTM C A' s m m' ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret (wbytes m' (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x142d4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp bx ret S CK HW H2 Hs16 Hlo Hpp Hpphi ALpp H1 Hret H4 H10 Rpp BX Lb L0b HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold ALLOC_STACK in Hlo.
  pose proof BX as (Hb1 & Hb64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 bx) 20 CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lb) as (_ & ALb & _). rewrite u_Z2bv in ALb by lia.
  assert (SOKb : store_ok SEGS m (Z_to_bv 64 bx) 20 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (BOXat_defined m bx _ _ _ _ _ x BX ltac:(lia) E). }
  destruct (bd_A al_rom regs m s pp bx 278 35 122 50 ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp ALb Gb
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) SOKb Rpp BX ltac:(lia) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes m (Z_to_bv 64 (bx + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) (pp + 8) m M0).
  { subst M0. apply (WP_blk C (c_A0 C) A m m md (Z_to_bv 64 bx) _ 20); [exact CK | | exact Lb | exact L0b | exact L0b | exact (W_sub0 _ _ _ _ HW)
      | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HW | apply POSTM_refl]. }
  destruct WP0 as [HW0 PM0].
  set (M1 := wbytes (wbytes M0 _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x1830c : word) with (Z_to_bv 64 0x1830c) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r1 (Z_to_bv 64 bx) (Z_to_bv 64 0x1431c) 20 (s - 16) S CK HW1 Q10 Lb L0b Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x1431c) with (0x1431c : word) by (apply bv_eq; reflexivity).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (bd_C al_rom r2 m1 s pp ret (getr regs 8) ltac:(lia) Hpp ltac:(lia) Hret) as (r3 & RUN3 & V2 & V1 & V8 & V10 & AG3).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1 M0. rdn_solve. }
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1 M0. rdn_solve. }
  { apply (W_sok_win C A1 m1 _ pp 8 CK HWa); [lia | cbn; lia]. }
  { exact E2. } { exact E8. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  (* [comment removed for export] *)
  assert (SUB1 : sub_live A1 A).
  { intros q k Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 bx)) as [->|NE]; [rewrite La in Lq; discriminate|]. rewrite <- (LEQa q NE). exact Lq. }
  assert (PMx : POSTM C A1 s m M1).
  { apply (POSTM_local C A1 A m md M1 s CK HW SUB1). intros a NE.
    destruct (Z_lt_ge_dec (u a) bx) as [B1|B1]; [| destruct (Z_lt_ge_dec (u a) (bx + 20)) as [B2|B2]].
    2:{ right. exists (Z_to_bv 64 bx), 20%Z. rewrite u_Z2bv by lia. split; [exact Lb | split; [exact La | lia]]. }
    all: left; unfold scratch; subst M1 M0.
    all: destruct (Z_lt_ge_dec (u a) (s - 16)); [exfalso; apply NE; rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia; reflexivity|].
    all: destruct (Z_lt_ge_dec (u a) s); [lia|].
    all: exfalso; apply NE; rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia; reflexivity. }
  assert (HW3 : W C A1 (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm1 md)).
  { apply (W_store_win C A1 m1 _ _ _ CK HWa); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (PM3 : POSTM C A1 s m m1) by (eapply POSTM_trans; [exact PMx | eapply POSTM_mono; [| exact PMa]; lia]).
  apply (HK A1 _ vm1 r3); try assumption.
  apply cs_kept_intro; csr; try reflexivity; rewrite ?V8; reflexivity.
Qed.

End Box.
