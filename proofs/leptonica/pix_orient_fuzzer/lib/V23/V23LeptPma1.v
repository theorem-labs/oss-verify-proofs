(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptGrayAT O23LeptSelGP O23LeptPma1 O23LeptPma1G O23LeptSelFMT O23LeptHmtW O23LeptHmtNW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptErr V23LeptCmap2 V23LeptPixCreateT2 V23LeptGrayAT V23LeptSelGP V23LeptPixClone V23_code_morphA_pma1.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Ltac rdz H :=
  addr_norm;
  lazymatch type of H with
  | rdn _ _ (Z_to_bv 64 ?b) _ = _ =>
      lazymatch goal with
      | |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with b by lia; exact H
      end
  end.

Ltac ld8h F D v := stepLD F D (word_to_le_bytes 8 v) v ltac:(addr_norm; rdn_hyp) ltac:(apply bytes_le_to_Z_8).

Ltac lenb := rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.

Definition PC_pma1 : Z := 0xa1b7c.

Lemma pma1_wb_same : forall bs m m' (a x : word), (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z -> m' x = m x) ->
  wbytes m' a bs x = wbytes m a bs x.
Proof.
  intros bs m m' a x Hl Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Lt|Ge].
  - rewrite !wbytes_outside by lia. apply Hx. lia.
  - destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Lt2|Ge2].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. apply Hx. lia.
Qed.

Section Pma1.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma pma1_POSTM_wb2 : forall C A s m m' (a : word) bs, (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  POSTM C A s m m' -> POSTM C A s (wbytes m a bs) (wbytes m' a bs).
Proof.
  intros C A s m m' a bs Hl (F & L). split.
  - intros x X1 X2 X3 X4 X5. apply pma1_wb_same; [exact Hl|]. intros _. exact (F x X1 X2 X3 X4 X5).
  - intros q k i Lq Hi. apply pma1_wb_same; [exact Hl|]. intros _. exact (L q k i Lq Hi).
Qed.

Lemma pma1_POSTM_ext : forall C A s m m', (forall x, m' x = m x) -> POSTM C A s m m'.
Proof. intros C A s m m' E. split; [intros x _ _ _ _ _ | intros q k i _ _]; apply E. Qed.

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pma_A : forall regs m (s pixs sel pp : Z) (v : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= sel < 2 ^ 64)%Z -> (0 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z ->
    (pp mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    PIXat (O23LeptPma1.MA m s ret regs pp) pixs v -> p_d v = 1%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
    getr regs 12 = Z_to_bv 64 sel -> getr regs 13 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0xa1b7c : word) m rom) (mkst regs' (0xa4fd0 : word) (O23LeptPma1.MA m s ret regs pp) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0xa1be0
      /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 44) /\ getr regs' 12 = Z_to_bv 64 (s - 48)
      /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 sel /\ getr regs' 19 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs sel pp v ret Hs Hs64 Hp Hsel Hpp Hpp64 ALpp ALp PX Hd SOK SOKp H2 H1 H10 H11 H12 H13.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. rewrite Hd in Cd.
    unfold O23LeptPma1.MA, O23LeptCmap2.FR5 in *. eexists. split.
    - zv F_a1b7c D_a1b7c (Z_to_bv 64 (s - 48)).
      stepST F_a1b80 D_a1b80 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_a1b84 D_a1b84 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_a1b88 D_a1b88 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_a1b8c D_a1b8c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_a1b90 D_a1b90 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      guard8 F_a1b94 D_a1b94 ALpp. stepb_ft F_a1b98 D_a1b98 ltac:(condZ).
      sn F_a1b9c D_a1b9c.
      stepST F_a1ba0 D_a1ba0 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOKp).
      stepb_ft F_a1ba4 D_a1ba4 ltac:(condZ).
      stepb_ft F_a1ba8 D_a1ba8 ltac:(condZ).
      sn F_a1bac D_a1bac. sn F_a1bb0 D_a1bb0. sn F_a1bb4 D_a1bb4. sn F_a1bb8 D_a1bb8.
      sn F_a1bbc D_a1bbc.
      stepb_ft F_6f114 D_6f114 ltac:(condZ).
      guard8 F_6f118 D_6f118 ALp. stepb_ft F_6f11c D_6f11c ltac:(condZ).
      stepLD F_6f120 D_6f120 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(rdz Cd) ltac:(apply lez4; lia).
      stepret F_6f124 D_6f124 (0xa1bc0 : word) ltac:(first [reflexivity | bveq]).
      zv F_a1bc0 D_a1bc0 (Z_to_bv 64 1).
      stepb_ft F_a1bc4 D_a1bc4 ltac:(condZ).
      zv F_a1bc8 D_a1bc8 (Z_to_bv 64 (s - 44)).
      zv F_a1bcc D_a1bcc (Z_to_bv 64 (s - 48)).
      sn F_a1bd0 D_a1bd0. sn F_a1bd4 D_a1bd4. sn F_a1bd8 D_a1bd8.
      sn F_a1bdc D_a1bdc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pma_C : forall regs m (s pixs sy sx : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (Z_to_le_bytes 4 sx) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0xa1be0 : word) m rom) (mkst regs' (0x6e078 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa1d10 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s pixs sy sx Hs Hs64 Hsy Hsx Ry Rx H2 H8 H9. eexists. split.
    - stepLD F_a1be0 D_a1be0 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(rdz Ry) ltac:(apply lez4; lia).
      stepb_ft F_a1be4 D_a1be4 ltac:(rewrite ?SumWalkTac.v_lw_small by lia; condZ).
      stepLD F_a1be8 D_a1be8 (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(rdz Rx) ltac:(apply lez4; lia).
      stepb_ft F_a1bec D_a1bec ltac:(rewrite ?SumWalkTac.v_lw_small by lia; condZ).
      stepb_tk F_a1bf0 D_a1bf0 ltac:(condZ).
      sn F_a1d08 D_a1d08. sn F_a1d0c D_a1d0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pma_D : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0xa1d10 : word) m rom) (mkst regs' (0x6eb08 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa1d20 /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 8; 10]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hd H10 H9. eexists. split.
    - stepb_ft F_a1d10 D_a1d10 ltac:(condZ).
      sn F_a1d14 D_a1d14. sn F_a1d18 D_a1d18. sn F_a1d1c D_a1d1c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pma_E : forall regs m (s pp pixd pixs : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> (0 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z ->
    cells5 (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs))) s ret s0v s1v s2v s3v ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 19 = Z_to_bv 64 pp -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0xa1d20 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pp pixd pixs ret s0v s1v s2v s3v Hs Hs64 Hret Hpp Hpp64 (R1 & R2 & R3 & R4 & R5) SOK H2 H10 H19 H8.
    eexists. split.
    - stepST F_a1d20 D_a1d20 (Z_to_bv 64 pp) (Z_to_bv 64 pixs) ltac:(sok_in SOK).
      sn F_a1d24 D_a1d24.
      ld8h F_a1d28 D_a1d28 ret. ld8h F_a1d2c D_a1d2c s0v. ld8h F_a1d30 D_a1d30 s1v.
      ld8h F_a1d34 D_a1d34 s2v. ld8h F_a1d38 D_a1d38 s3v.
      zv F_a1d3c D_a1d3c (Z_to_bv 64 s).
      stepret F_a1d40 D_a1d40 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pma_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa1d10 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa1d00 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x1b54a /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_a1d10 D_a1d10 ltac:(condZ).
      sn F_a1d44 D_a1d44.
      stepLD F_a1d48 D_a1d48 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_a1d4c D_a1d4c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_a1d50 D_a1d50. stepb_ft F_a1d54 D_a1d54 ltac:(condZ).
      sn F_a1d58 D_a1d58. sn F_a1d5c D_a1d5c. sn F_a1d60 D_a1d60. sn F_a1d64 D_a1d64. sn F_a1d68 D_a1d68.
      sn F_a1d6c D_a1d6c. sn F_a1cfc D_a1cfc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pma_G : forall regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells5 m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa1d00 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5) H2 H10. eexists. split.
    - sn F_a1d00 D_a1d00. sn F_a1d04 D_a1d04. sn F_a1d24 D_a1d24.
      stepLD8 F_a1d28 D_a1d28 ret. stepLD8 F_a1d2c D_a1d2c s0v. stepLD8 F_a1d30 D_a1d30 s1v.
      stepLD8 F_a1d34 D_a1d34 s2v. stepLD8 F_a1d38 D_a1d38 s3v.
      zv F_a1d3c D_a1d3c (Z_to_bv 64 s).
      stepret F_a1d40 D_a1d40 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_pma1 : str16 0x1b54a 17.
Proof. str16_tac. Qed.     (* [comment removed for export] *)

Lemma rdn_clone_mem_cell : forall m pixs pp, (0 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (0 <= pixs < 2 ^ 64)%Z ->
  rdn SEGS (O23LeptPma1.clone_mem m pixs pp) (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pixs).
Proof.
  intros m pixs pp Hpp Hpp64 Hps. unfold O23LeptPma1.clone_mem.
  rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia).
  rewrite w2b_Z by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem pma1_new_W : forall C A m md regs (s pixs sel pp w h cm datas sy sx cy cx sdata sname : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptPma1.PMA1_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel -> getr regs 13 = Z_to_bv 64 pp ->
  (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> O23LeptPixHdr.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  RECat m sel (sel_flds sy sx cy cx sdata sname) -> live A (Z_to_bv 64 sel) = Some 32%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ (forall q, live A' q = live A q) /\ POSTM C A s (O23LeptPma1.null_mem m pp) m')
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h 1 cd data cv /\
                               POSTM C A s (O23LeptPma1.clone_mem m pixs pp) m') ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1b7c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs sel pp w h cm datas sy sx cy cx sdata sname cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13
    Hpp Hpp8 ALpp PXs HOK Hw Hh Lps L0ps HCM RC Lsel Hsy Hsx kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptPma1.PMA1_STACK, O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (RECat_range _ _ _ RC) as [Hsel0 Hsel32].
  change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hsel32.
  destruct (blk_range C A m md (Z_to_bv 64 sel) 32 CK HW Lsel ltac:(lia)) as [Gsel TOPsel]. rewrite u_Z2bv in Gsel, TOPsel by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lsel) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  set (M1 := O23LeptPma1.MA m s ret regs pp).
  assert (OUT1 : forall x : word, (bv_unsigned x < s - 48)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptPma1.MA, O23LeptCmap2.FR5.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia. reflexivity. }
  assert (PX1 : PIXat M1 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. apply OUT1. lia. }
  destruct (pma_A al_rom regs m s pixs sel pp (O23LeptPixCopyT.hdv w h 1 cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ALpp (al16_mod8 _ ALps) PX1 eq_refl
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A m md pp 8 CK HW ltac:(lia) ltac:(cbn; lia))
              H2 H1 H10 H11 H12 H13)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & Q14 & Q8 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP0 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs)) by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. unfold O23LeptPma1.MA. apply (W_store_win C A _ md); [exact CK | exact HW0 | rewrite u_Z2bv by lia; lia | lenb]. }
  assert (PM1 : POSTM C A s (O23LeptPma1.null_mem m pp) M1).
  { subst M1. unfold O23LeptPma1.MA, O23LeptPma1.null_mem. apply pma1_POSTM_wb2; [lenb | exact PM0]. }
  set (M2 := O23LeptSelGP.SGP2 M1 (s - 44) (s - 48) sy sx).
  assert (OUT2 : forall x : word, ~ (s - 48 <= bv_unsigned x < s - 40)%Z -> M2 x = M1 x).
  { intros x Hx. subst M2. apply O23LeptSelGP.SGP2_out; unfold O23LeptSelGP.cell_ok; lia. }
  assert (RC1 : RECat M1 sel (sel_flds sy sx cy cx sdata sname)).
  { apply (RECat_frame m); [exact RC|]. intros x Hx. change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hx. apply OUT1. lia. }
  destruct (sgp2_run al_rom r1 M1 sel (s - 44) (s - 48) sy sx cy cx sdata sname (Z_to_bv 64 0xa1be0) RC1 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              (W_sok_win C A M1 md (s - 44) 4 CK HW1 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A M1 md (s - 48) 4 CK HW1 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) (al16_mod8 _ ALsel) (sp_slot_al4' s 44 Hs16 eq_refl) (sp_slot_al4' s 48 Hs16 eq_refl)
              Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13 Q14)
    as (r2 & RUN2 & R10 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  replace (Z_to_bv 64 0xa1be0) with (0xa1be0 : word) by (apply bv_eq; reflexivity).
  assert (INC2 : forall a : word, M2 a <> M1 a -> (s - 48 <= bv_unsigned a < s - 40)%Z).
  { intros a NE. destruct (Z_le_gt_dec (s - 48) (bv_unsigned a)); destruct (Z_lt_ge_dec (bv_unsigned a) (s - 40)); try lia;
      exfalso; apply NE; apply OUT2; lia. }
  assert (HW2 : W C A M2 md).
  { apply (W_local C A M1 md M2 s CK HW1 Hhi); [| subst M2; apply O23LeptSelGP.SGP2_grows].
    intros a NE. left. unfold scratch. pose proof (INC2 a NE). lia. }
  assert (PM2 : POSTM C A s M1 M2) by (apply (POSTM_range C A M1 md M2 (s - 48) (s - 40) s CK HW1 OUT2); lia).
  destruct (SGP2_rd M1 (s - 44) (s - 48) sy sx ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(lia) ltac:(lia)) as [Ry Rx].
  destruct (pma_C al_rom r2 M2 s pixs sy sx ltac:(lia) ltac:(lia) Hsy Hsx Ry Rx ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r3 & RUN3 & S1 & S10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN3 |].
  assert (PXs2 : PIXat M2 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite OUT2 by lia. apply OUT1. lia. }
  assert (HCM2 : cm = 0%Z \/ (CMAPat M2 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT2 by lia. apply OUT1. lia. }
  apply (pixCreateTemplate_szT_W C A M2 md r3 (s - 48) pixs w h 1 cm datas cv (Z_to_bv 64 0xa1d10) S CK HW2 ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptGrayAT.PCT_STACK, O23LeptBase.LSF; lia) ltac:(lia)
           S1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) S10 PXs2 HOK Hw Hh Lps HCM2 kR bR Hrm Hrk Hrb).
  intros A1 m4 vm1 r4 HW4 CS4 PM4 OUT4 Hrm1.
  replace (Z_to_bv 64 0xa1d10) with (0xa1d10 : word) by (apply bv_eq; reflexivity).
  assert (CE4 : cells5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE0.
    assert (CE1 : cells5 M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { apply (cells5_out (O23LeptCmap2.FR5 m s ret regs) M1 pp (pp + 8) s); [| lia | lia | lia | exact CE0].
      intros x Hx. subst M1. unfold O23LeptPma1.MA. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
    apply (cells5_frm C (s - 48) M2 m4 s); [exact CK | exact (proj1 PM4) | lia | lia | lia |].
    apply (cells5_out M1 M2 (s - 48) (s - 40) s); [exact OUT2 | lia | lia | lia | exact CE1]. }
  destruct OUT4 as [[Res0 LIVEQ] | (pixd & cd & data & Resd & PT)].
  - destruct (pma_F al_rom r4 m4 (W_sev_got C A1 m4 _ HW4) (W_sev C A1 m4 _ HW4) Res0) as (r5 & RUN5 & V1 & V10 & V11 & V12 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    apply (returnErrorPtr_W C A1 m4 _ r5 (s - 48) 0x126da 0x1b54a 13 17 (Z_to_bv 64 0xa1d00) (Z_to_bv 64 0) S CK HW4 ltac:(csr; reflexivity)
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pma1).
    intros m6 r6 HW6 OUT6 GR6 CS6 A10.
    replace (Z_to_bv 64 0xa1d00) with (0xa1d00 : word) by (apply bv_eq; reflexivity).
    destruct (pma_G al_rom r6 m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret
                (cells5_out m4 m6 (s - 48 - (16 + LSF)) (s - 48) s _ _ _ _ _ OUT6 ltac:(lia) ltac:(lia) ltac:(lia) CE4)
                ltac:(csr; reflexivity) A10) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    apply (HK A1 m6 vm1 r7 HW6).
    + apply cs_kept_intro; csr; try reflexivity.
    + left. split; [exact U10 | split; [exact LIVEQ |]].
      eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [exact PM2 |].
      eapply POSTM_trans; [eapply POSTM_mono; [| exact PM4]; lia |].
      apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ |].
      eapply (POSTM_range C A1 m4 _ m6); [exact CK | exact HW4 | exact OUT6 | unfold LSF; lia | lia | lia].
    + exact Hrm1.
  - pose proof PT as (Gd & TOPd & ALd & Gdat & TOPdat & ALdat & NEdd & L0d & L0dat & LC0d & LC0dat & L1d & L1dat & PXd & CMR).
    assert (NEq : forall q : Z, live A (Z_to_bv 64 q) = None -> Z_to_bv 64 pixs <> Z_to_bv 64 q).
    { intros q Lq E. rewrite E in Lps. congruence. }
    assert (L1ps : live A1 (Z_to_bv 64 pixs) = Some 64%Z).
    { destruct CMR as [(_ & EQ) | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0cd & L0ad & _ & _ & _ & _ & _ & EQ)].
      - rewrite EQ; [exact Lps | apply NEq; exact L0d | apply NEq; exact L0dat].
      - rewrite EQ; [exact Lps | apply NEq; exact L0d | apply NEq; exact L0dat | apply NEq; exact L0cd | apply NEq; exact L0ad]. }
    destruct (pma_D al_rom r4 m4 pixd pixs ltac:(lia) Resd ltac:(csr; reflexivity)) as (r5 & RUN5 & V1 & V8 & V10 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    assert (PXs4 : PIXat m4 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
    { apply (PIXat_frame M2); [exact PXs2|]. intros x Hx. apply (O23LeptCmap2.LIVK_at A M2 m4 pixs 64 x (proj2 PM4) Lps); lia. }
    replace (0x6eb08 : word) with (Z_to_bv 64 PC_pixClone) by (apply bv_eq; reflexivity).
    apply (pixClone_W fx C A1 m4 _ r5 (s - 48) pixs (O23LeptPixCopyT.hdv w h 1 cm datas) (Z_to_bv 64 0xa1d20) S CK HW4 ltac:(csr; reflexivity)
             ltac:(lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity) V10 PXs4 eq_refl L1ps L0ps).
    intros m5 r6 Em5 HW5 CS6 R10'.
    replace (Z_to_bv 64 0xa1d20) with (0xa1d20 : word) by (apply bv_eq; reflexivity).
    assert (DJd : (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z).
    { destruct (blk_apart C A1 m4 _ (Z_to_bv 64 pixs) (Z_to_bv 64 pixd) 64 64 CK HW4 L1ps L1d (NEq pixd L0d) ltac:(lia) ltac:(lia)) as [X|X];
        rewrite !u_Z2bv in X by lia; lia. }
    assert (OUT5 : forall x : word, ~ (pixs + 20 <= bv_unsigned x < pixs + 24)%Z -> m5 x = m4 x).
    { intros x Hx. rewrite Em5. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
    set (m6 := wbytes m5 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
    assert (OUT6 : forall x : word, ~ (pp <= bv_unsigned x < pp + 8)%Z -> m6 x = m5 x).
    { intros x Hx. subst m6. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
    assert (CE6 : cells5 m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { apply (cells5_out m5 m6 pp (pp + 8) s); [exact OUT6 | lia | lia | lia |].
      apply (cells5_out m4 m5 (pixs + 20) (pixs + 24) s); [exact OUT5 | lia | lia | lia | exact CE4]. }
    destruct (pma_E al_rom r6 m5 s pp pixd pixs ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret ltac:(lia) ltac:(lia)
                CE6 (W_sok_win C A1 m5 _ pp 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) R10' ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
    assert (HW6 : W C A1 m6 (with_vmmaps vm1 md)).
    { subst m6. apply (W_store_win C A1 m5 _); [exact CK | exact HW5 | rewrite u_Z2bv by lia; lia | lenb]. }
    apply (HK A1 m6 vm1 r7 HW6).
    + apply cs_kept_intro; csr; try reflexivity.
    + right. exists pixd, cd, data. split; [exact U10 | split].
      * apply (O23LeptPma1.pixt_new_frame C A A1 m4 m6 pixd w h 1 cd data cv PT).
        -- intros x Hx. rewrite OUT6 by lia. apply OUT5. lia.
        -- intros NZ x Hx.
           destruct CMR as [(CD0 & _) | (ad & _ & Gcd & TOPcd & _ & _ & _ & _ & _ & _ & _ & L0cd & _ & _ & _ & L1cd & _ & _ & _)]; [contradiction |].
           assert (DJc : (pixs + 64 <= cd \/ cd + 24 <= pixs)%Z).
           { destruct (blk_apart C A1 m4 _ (Z_to_bv 64 pixs) (Z_to_bv 64 cd) 64 24 CK HW4 L1ps L1cd (NEq cd L0cd) ltac:(lia) ltac:(lia)) as [X|X];
               rewrite !u_Z2bv in X by lia; lia. }
           rewrite OUT6 by lia. apply OUT5. lia.
      * apply (POSTM_trans C A s _ (wbytes (wbytes (O23LeptPma1.null_mem m pp) (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))).
        -- apply pma1_POSTM_ext. intros x. unfold O23LeptPma1.clone_mem, O23LeptPma1.null_mem.
           apply pma1_wb_same; [lenb |]. intros Hx. apply pma1_wb_same; [lenb |]. intros _.
           rewrite wbytes_outside; [reflexivity | lenb | revert Hx; lenb].
        -- subst m6. rewrite Em5. apply pma1_POSTM_wb2; [lenb |]. apply pma1_POSTM_wb2; [lenb |].
           eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [exact PM2 |]. eapply POSTM_mono; [| exact PM4]; lia.
    + exact Hrm1.
Qed.

End Pma1.
