(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_DepotFrame AW_LargeAlloc1 AW_Populate AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma rw_cells_recell : forall m A cs cs', cells_bytes cs = cells_bytes cs' -> cells_wf cs' -> rw_cells asegs m A cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' E WF' [[WF B] W]. split; [split; [exact WF'| rewrite <- E; exact B]|].
  rewrite <- (cells_bytes_length cs' WF'), <- E, (cells_bytes_length cs WF). exact W.
Qed.

(* [comment removed for export] *)
Lemma hdr_word : forall m A st b1, (st = 0 \/ st = 2 \/ st = 3) -> (b1 = 17 \/ b1 = 145 \/ b1 = 65 \/ b1 = 193) ->
  rw_cells asegs m A [C1 (b8 st); C1 (b8 b1); C2 (wz 0)] <-> rw_cells asegs m A [C4 (wz (st + 256 * b1))].
Proof.
  intros m A st b1 HS HB.
  assert (E : cells_bytes [C1 (b8 st); C1 (b8 b1); C2 (wz 0)] = cells_bytes [C4 (wz (st + 256 * b1))]).
  { destruct HS as [->|[->| ->]]; destruct HB as [->|[->|[->| ->]]]; vm_compute;
      repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity. }
  split; intros H.
  - eapply rw_cells_recell; [exact E| cbn; repeat split; reflexivity| exact H].
  - eapply rw_cells_recell; [symmetry; exact E| cbn; repeat split; reflexivity| exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsize_hi_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c : Z) : machine_state -> Prop :=
  fun ms' => exists (a6 a7 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (wz (class_size c)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1992c4) fc None m (seg_rom asegs).

Lemma rsize_hi_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c : Z), 17 <= c <= 30 ->
  evt asegs (rsize_hi_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) (wz c) a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1992a0) fc None m (seg_rom asegs)).
Proof.
  (* [comment removed for export] *)
  intros. unfold wz.
  first [ solve [ do 9 step;
                  match goal with |- context [Z_to_bv 64 (Z.land ?a ?b + ?y)] =>
                    replace (Z_to_bv 64 (Z.land a b + y)) with (Z_to_bv 64 (class_size c)) by (clear - H; zcases c 17 30; apply bv_eq; vm_compute; reflexivity) end;
                  apply evt_done; unfold rsize_hi_post; do 2 eexists; reflexivity ]
        | (* [comment removed for export] *)
          zcases c 17 30;
          (do 9 step; apply evt_done; unfold rsize_hi_post; do 2 eexists;
           match goal with |- MS ?R _ _ _ _ _ _ = _ => idtac end;
           repeat f_equal; apply bv_eq; vm_compute; reflexivity) ].
Qed.

(* [comment removed for export] *)
Lemma v_divuw_val : forall x d, 0 <= x < 2^64 -> 0 < d < 2^31 -> (x mod 2^32) / d < 2^31 ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 d) = Z_to_bv 64 ((x mod 2^32) / d).
Proof.
  intros x d Hx Hd Hq. unfold v_divuw, bv_wrap, bv_swrap, bv_wrap. rewrite !unsigned_lit by lia.
  change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite (Z.mod_small d) by lia. destruct (Z.eqb_spec d 0); [lia|]. f_equal.
  assert (0 <= (x mod 2^32) / d) by (apply Z.div_pos; Z.div_mod_to_equations; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma land_clear2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x - x mod 4.
Proof.
  intros x Hx. change 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot 3)). rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia. rewrite <- Z.ldiff_land. change 3 with (Z.ones 2). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma poisoned_carry : forall W m m' A k v,
  poisoned m A k v -> munch W m m' -> wmono asegs m m' -> disjoint_from W (sh A) (Z.of_nat k) -> poisoned m' A k v.
Proof.
  intros W m m' A k v PZ MU WM D. unfold poisoned in *. eapply SHAD_transport; [exact PZ| exact MU| exact WM|].
  unfold poison_bytes. rewrite repeat_length. exact D.
Qed.
Lemma v_sltu_ge : forall a b, bv_unsigned b <= bv_unsigned a -> v_sltu a b = Z_to_bv 64 0.
Proof. intros a b H. rewrite v_sltu_b2z. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition recycle_prim1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo CA c p mhdr u rz n actx b1 TH : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz AINST) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x199618) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' mhdr [C1 (b8 0); C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)]
    /\ (rz = 16 \/ (32 <= rz /\ rw_cells asegs m' p [C8 (wz 0); C8 (wz mhdr)]))
    /\ poisoned m' u (Z.to_nat (round_up n 8 / 8)) kAsanHeapLeftRedzoneMagic
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW2.

Section RecPrim.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo sb c CA cb p rz n actx b1 idx au mu TSD CTX TH ARI nf mfa : Z).
  Let csz := class_size c.
  Let rbeg := sb + c * 2^32.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let u := p + rz.
  Let mhdr := u - 16.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 112 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz cb. Hypothesis Ha1 : a1 = wz mhdr.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 4096 = 0).
  Hypothesis ARIE : ARI = sb + kSpaceSize.
  (* [comment removed for export] *)
  Hypothesis PE : p = rbeg + idx * csz. Hypothesis IDX : 0 <= idx /\ (idx + 1) * csz <= mu /\ mu <= kFreeArrayOffset - kUserMapSize.
  Hypothesis RZ : rz = 16 \/ 32 <= rz. Hypothesis RZA : hidden (rz mod 16 = 0).
  Hypothesis NR : 1 <= n /\ rz + round_up n 8 <= csz.
  Hypothesis B1 : b1 = 17 \/ b1 = 145 \/ b1 = 65 \/ b1 = 193.
  Hypothesis TPR : 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis CBR : bv_unsigned sp <= cb /\ cb + 8 <= 2^63.
  Hypothesis CBC : rw_cells asegs m cb [C8 (wz CA)].
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)].
  Hypothesis IRI : rw_cells asegs m (AINST + 48) [C8 (wz ARI)].
  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis HDR : rw_cells asegs m mhdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)].
Hypothesis MAG : rz = 16 \/ (32 <= rz /\ rw_cells asegs m p [C8 (wz 0xCC6E96B9CC6E96B9); C8 (wz mhdr)]).
  Hypothesis SHU : poisoned m u (Z.to_nat (round_up n 8 / 8)) kAsanHeapFreeMagic.
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).

  Ltac prep :=
    unfold kNumClasses, kSpaceSize, kPageSize, kFreeArrayOffset, kUserMapSize, AHI_LO, AIMG_TOP, AINST, REGIONINFO_SIZE in *;
    acb;
    change (6976152 + 32) with 6976184 in *; change (6976152 + 48) with 6976200 in *;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR;
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as CST; destruct CST as (CS1 & CS2 & CS3 & CS4); fold csz in CS1, CS2, CS3, CS4;
    assert (GEO : rbeg = sb + c * 4294967296 /\ R = ARI + 128 * c /\ u = p + rz /\ mhdr = u - 16) by (subst rbeg R u mhdr; repeat split; reflexivity);
    destruct GEO as (ERB & ER & EU & EM).

  (* [comment removed for export] *)
  Lemma rp_tail2 : forall (x10 x11 x12 x13 x14 x15 x16 x17 : word) (mY : mem),
    mem_inv asegs mY ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z m mY -> wmono asegs m mY ->
    stk asegs mY lo (bv_unsigned sp + -48) ->
    rw_cells asegs mY (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mY cb [C8 (wz CA)] -> SENV tp TSD CTX TH mY ->
    rw_cells asegs mY (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)] ->
    rw_cells asegs mY mhdr [C1 (b8 0); C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)] ->
    (rz = 16 \/ (32 <= rz /\ rw_cells asegs mY p [C8 (wz 0); C8 (wz mhdr)])) ->
    poisoned mY u (Z.to_nat (round_up n 8 / 8)) kAsanHeapFreeMagic -> stk asegs mY (TH + 2800) (TH + 3168) ->
    evt asegs (recycle_prim1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CA c p mhdr u rz n actx b1 TH)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz cb) (wz mhdr) x10 x11 x12 x13 x14 x15 x16 x17
               (wz p) (wz AINST) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19935c) fc None mY (seg_rom asegs)).
  Proof.
    intros x10 x11 x12 x13 x14 x15 x16 x17 mY MIY MU WM STY FR CBY ENVY ISBY HDRY MAGY SHUY TSTY.
    clear MI ST CBC ENV ISB IRI RI HDR MAG SHU TST. prep. clear Ha0 Ha1.
    assert (ICZ : 0 <= idx * csz) by (clear - IDX CS1; try acb; nia).
    assert (IDX' : idx * csz + csz <= mu) by (clear - IDX; try acb; nia).
    assert (RU8 : n <= round_up n 8 < n + 8 /\ round_up n 8 mod 8 = 0) by (unfold round_up; clear - NR; try acb; Z.div_mod_to_equations; lia).
    assert (PB : sb + c * 4294967296 <= p /\ p + csz <= sb + c * 4294967296 + mu /\ p + csz <= sb + (c + 1) * 4294967296 /\ mhdr + 16 = u /\ p + 16 <= u /\ u + round_up n 8 <= p + csz)
      by (rewrite EM, EU, PE, ERB; clear - IDX IDX' ICZ NR RZ CS1 HC; try acb; repeat split; lia).
    assert (BND : 17594333495296 <= p /\ p + 32 <= aceil /\ 17594333495296 <= mhdr /\ mhdr + 16 <= aceil /\ 17594333495296 <= u /\ u + 8 <= aceil
                  /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ aceil <= lo /\ bv_unsigned sp <= cb /\ cb + 8 <= 2^63)
      by (clear - PB SBR HC CS1 CS3 LO CBR RU8 NR; try acb; repeat split; nia).
    assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR BND HI; try acb; lia).
    region_sides. name_bands.
    assert (SHR : 2148314624 <= sh u /\ sh u + round_up n 8 / 8 + 8 <= 17594333495296) by (unfold sh, ASHADOW_BASE; clear - BND PB RU8 NR HC CS1; try acb; Z.div_mod_to_equations; lia).
    pose proof (I : region_rank (sh u) 1) as RXRsh.
    assert (UAL : u mod 8 = 0).
    { rewrite EU, PE, ERB. destruct RZA as [RZ16]. destruct SBA as [S4K]. clear - RZ16 S4K CS2 HC IDX; try acb. Z.div_mod_to_equations. nia. }
    pose proof ENVY as ENV0. open_senv ENVY.
    unfold wz in *. region_table.
    destruct SHUY as (_ & _ & SHY). unfold poison_bytes in SHY.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z mY) as MUY.
    pose proof (wmono_refl asegs mY) as WMY.
    (* [comment removed for export] *)
    all: do 9 step.
    all: change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0); change (zx32 (Z_to_bv 64 n)) with (zx32 (wz n)); rewrite zx32_wz by (clear - NR CS1 RU8 RZ; try acb; lia); unfold wz.
    all: rewrite (unsigned_lit 0), Z.shiftl_0_l, (unsigned_lit 0), Z.lor_0_l, (unsigned_lit n), (unsigned_lit (n + 7)) by (clear - NR CS1 RU8 RZ; try acb; lia).
    all: change 18446744073709551608 with (2^64 - 2^3); rewrite StrFun.land_align_down by (clear - NR CS1 RU8 RZ; try acb; lia); change (2^3) with 8.
    all: replace (n + 7 - (n + 7) mod 8) with (round_up n 8) by (unfold round_up; clear; Z.div_mod_to_equations; lia).
    all: replace (mhdr + 16) with u by (clear - PB; try acb; lia).
    (* [comment removed for export] *)
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with H : stk _ mq lo _ |- _ =>
      callD (poison_shadow_spec _ (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq lo u (round_up n 8) 250
               (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (round_up n 8 / 8))) MIY ltac:(hci; rewrite E48; exact H) LO ltac:(hci; rewrite E48; clear - HI; try acb; lia)
               eq_refl eq_refl eq_refl) end end.
    all: try eassumption.
    all: try lazymatch goal with
         | |- (AHI_LO <= u /\ _ \/ _) /\ _ => unfold AHI_LO; acb; clear - BND PB RU8 NR UAL CS1 HC; try acb; split; [left; split; nia| repeat split; nia]   (* [comment removed for export] *)
         | |- 0 <= 250 < 256 => clear; lia
         | |- 250 <> 0 \/ _ => left; clear; lia
         | |- Z.of_nat (length _) = _ => rewrite repeat_length; clear - RU8 NR; try acb; Z.div_mod_to_equations; lia
         end.
    all: lazymatch goal with H : poisoned _ u _ 250 |- _ => destruct H as (PO0 & PO8 & PARR); unfold poison_bytes in PARR end.
    (* [comment removed for export] *)
    all: step; callN getcurthreadstats_spec; rewrite ?unsigned_lit by (clear - SPR BND HI; try acb; lia); try eassumption.
    all: try (clear - HI; try acb; lia). all: try (unfold AIMG_TOP; clear - TPR; try acb; lia). all: try (unfold AHI_LO in RNG; acb; clear - RNG; try acb; aunf; lia).
    (* [comment removed for export] *)
    all: lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2840) (TH + 3168) H ltac:(hci; clear; lia)) as [TS1 TS2]; clear H;
      destruct (stk_split asegs _ (TH + 2840) (TH + 2856) (TH + 3168) TS2 ltac:(hci; clear; lia)) as [TS3 TS4]; clear TS2;
      destruct (stk_cells _ _ _ TS3 ltac:(hci; clear; lia)) as [sj SJ]; replace (TH + 2856 - (TH + 2840)) with 16 in SJ by (clear; lia); change (Z.to_nat 16) with 16%nat in SJ;
      apply (rw_cells_split_CB asegs _ _ [] 16 sj [] [8;8]%nat) in SJ; [| reflexivity]; cbn [mk_CB_cells app] in SJ;
      repeat match type of SJ with context [CB ?k (take ?i ?l)] => let J := fresh "jk" in remember (take i l) as J in SJ end;
      repeat match type of SJ with context [CB ?k (drop ?i ?l)] => let J := fresh "jk" in remember (drop i l) as J in SJ end;
      repeat match goal with H' : _ = take _ _ |- _ => clear H' | H' : _ = drop _ _ |- _ => clear H' end
    end.
    all: unfold wz.
    (* [comment removed for export] *)
    all: do 8 step; step; fix_lit_store; step; fix_lit_store.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: step; [if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - BND; try acb; lia); clear - BND; try acb; intros K; lia| clear K]..].
    all: step; step; [if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - BND; try acb; lia); clear - BND PB HC CS3; try acb; intros K; lia| clear K]..].
    all: step; step; [if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - BND; try acb; lia); clear - BND PB HC CS3; try acb; intros K; lia| clear K]..].
    (* [comment removed for export] *)
    all: do 7 step.
    all: rewrite ?(unsigned_lit p), ?(unsigned_lit sb) by (clear - BND; try acb; lia).
    all: rewrite (unsigned_lit (p - sb)) by (clear - BND PB HC; try acb; lia).
    all: rewrite (Z.shiftl_mul_pow2 (p - sb) 27) by (clear; lia).
    all: rewrite (unsigned_lit ((p - sb) * 2^27)) by (clear - BND PB HC CS3; try acb; nia).
    all: rewrite Z.shiftr_div_pow2 by (clear; lia).
    all: replace ((p - sb) * 2^27 / 2^59) with c by (clear - PB HC CS3; try acb; Z.div_mod_to_equations; nia).
    all: do 8 step.
    all: lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (TST' : stk asegs mm (TH + 2800) (TH + 3168))
         by (pose proof (stk_of_rw_cells asegs _ _ _ SJ) as X; cbn [cells_size csize Nat.add] in X; replace (TH + 2840 + Z.of_nat 16) with (TH + 2856) in X by (clear; lia);
             apply (stk_merge asegs _ _ (TH + 2840)); [exact TS1| |clear; lia]; apply (stk_merge asegs _ _ (TH + 2856)); [exact X| exact TS4|clear; lia]) end.
    all: apply evt_done; unfold recycle_prim1_post; do 12 eexists; split; [reflexivity|].
    all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [exact HDRY|].
    all: split; [destruct MAGY as [RZ16 | [RZ32 MAGC]]; [left; exact RZ16 | right; split; [exact RZ32|]];
                 eapply rw_cells_transport; [exact MAGC| exact MUY| exact WMY| cbn [disjoint_from cells_size csize length Nat.add]; region_decide]|].
    all: split; [| exact TST'].
    all: split; [exact PO0| split; [exact PO8| exact PARR]].
  Qed.

  (* [comment removed for export] *)
  Lemma rp_tail : forall (x10 x13 x14 x17 : word) (mY : mem),
    mem_inv asegs mY ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z m mY -> wmono asegs m mY ->
    stk asegs mY lo (bv_unsigned sp + -48) ->
    rw_cells asegs mY (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mY cb [C8 (wz CA)] -> SENV tp TSD CTX TH mY ->
    rw_cells asegs mY (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)] ->
    rw_cells asegs mY mhdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)] ->
    (rz = 16 \/ (32 <= rz /\ rw_cells asegs mY p [C8 (wz 0); C8 (wz mhdr)])) ->
    poisoned mY u (Z.to_nat (round_up n 8 / 8)) kAsanHeapFreeMagic -> stk asegs mY (TH + 2800) (TH + 3168) ->
    evt asegs (recycle_prim1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CA c p mhdr u rz n actx b1 TH)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz cb) (wz mhdr) x10 (wz (sb + 2^37)) (Z_to_bv 64 (-1)) x13 x14 (wz (csz * idx + csz)) (wz ARI) x17
               (wz p) (wz AINST) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199324) fc None mY (seg_rom asegs)).
  Proof.
    intros x10 x13 x14 x17 mY MIY MU WM STY FR CBY ENVY ISBY HDRY MAGY SHUY TSTY.
    clear MI ST CBC ENV ISB IRI RI HDR MAG SHU TST. prep. clear Ha0 Ha1.
    assert (ICZ : 0 <= idx * csz) by (clear - IDX CS1; try acb; nia).
    assert (IDX' : idx * csz + csz <= mu) by (clear - IDX; try acb; nia).
    assert (RU8 : n <= round_up n 8 < n + 8 /\ round_up n 8 mod 8 = 0) by (unfold round_up; clear - NR; try acb; Z.div_mod_to_equations; lia).
    assert (PB : sb + c * 4294967296 <= p /\ p + csz <= sb + c * 4294967296 + mu /\ p + csz <= sb + (c + 1) * 4294967296 /\ mhdr + 16 = u /\ p + 16 <= u /\ u + round_up n 8 <= p + csz)
      by (rewrite EM, EU, PE, ERB; clear - IDX IDX' ICZ NR RZ CS1 HC; try acb; repeat split; lia).
    assert (BND : 17594333495296 <= p /\ p + 32 <= aceil /\ 17594333495296 <= mhdr /\ mhdr + 16 <= aceil /\ 17594333495296 <= u /\ u + 8 <= aceil
                  /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ aceil <= lo /\ bv_unsigned sp <= cb /\ cb + 8 <= 2^63)
      by (clear - PB SBR HC CS1 CS3 LO CBR RU8 NR; try acb; repeat split; nia).
    assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR BND HI; try acb; lia).
    region_sides. name_bands.
    assert (SHR : 2148314624 <= sh u /\ sh u + round_up n 8 / 8 + 8 <= 17594333495296) by (unfold sh, ASHADOW_BASE; clear - BND PB RU8 NR HC CS1; try acb; Z.div_mod_to_equations; lia).
    pose proof (I : region_rank (sh u) 1) as RXRsh.
    assert (MAL : mhdr mod 16 = 0).
    { rewrite EM, EU, PE, ERB. destruct RZA as [RZ16]. destruct SBA as [S4K]. clear - RZ16 S4K CS2 HC IDX; try acb. Z.div_mod_to_equations. nia. }
    pose proof (bv_unsigned_in_range _ (b8 b1)) as B1R.
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    apply (rw_cells_app asegs mY mhdr [C1 (b8 3); C1 (b8 b1); C2 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]) in HDRY.
    destruct HDRY as [HW HT]. cbn [cells_size csize Nat.add] in HT. change (Z.of_nat 4) with 4 in HT.
    apply (proj1 (hdr_word mY mhdr 3 b1 ltac:(hci; clear; lia) B1)) in HW. unfold wz in HW.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    rewrite ?(unsigned_lit mhdr) by (clear - BND; try acb; lia). rewrite land_clear2 by (clear - BND; try acb; lia).
    replace (mhdr - mhdr mod 4) with mhdr by (clear - MAL; try acb; Z.div_mod_to_equations; lia).
    rewrite (Z.shiftl_mul_pow2 mhdr 3), (unsigned_lit (mhdr * 2^3)) by (clear - BND; try acb; lia).
    replace ((mhdr * 2^3) mod 32) with 0 by (clear - MAL; try acb; Z.div_mod_to_equations; lia).
    rewrite !Z.shiftl_0_r. change (bv_swrap 32 255) with 255. change (bv_swrap 32 3) with 3.
    assert (MAL4 : mhdr mod 4 = 0) by (clear - MAL; try acb; Z.div_mod_to_equations; lia). assert (MR : 0 <= mhdr < 2^64) by (clear - BND; try acb; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(mhdr, mhdr + 4)]%Z mY) as MUH. pose proof (wmono_refl asegs mY) as WMH.
    pose proof B1 as B1c. destruct B1c as [EB | [EB | [EB | EB]]]; rewrite EB in HW.
    all: match type of HW with context [Z_to_bv 64 ?v] => let v' := eval vm_compute in v in change v with v' in HW end.
    (* [comment removed for export] *)
    all: move HW at bottom.   (* [comment removed for export] *)
    all: astep; step; zb_fold_lits; step; [if_cases K; zify_cond K; [deadK K| clear K]..].
    all: move HW at bottom.
    all: step; step; step; zb_fold_lits; astep; fix_lit_store; step; [if_cases K; zify_cond K; [deadK K| clear K]..].
    all: match type of HW with context [Z_to_bv 64 ?v] => let v' := eval vm_compute in v in change v with v' in HW end.
    (* [comment removed for export] *)
    all: first [ replace 4352 with (0 + 256 * b1) in HW by (rewrite EB; reflexivity) | replace 37120 with (0 + 256 * b1) in HW by (rewrite EB; reflexivity)
               | replace 16640 with (0 + 256 * b1) in HW by (rewrite EB; reflexivity) | replace 49408 with (0 + 256 * b1) in HW by (rewrite EB; reflexivity) ].
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => apply (proj2 (hdr_word mq mhdr 0 b1 ltac:(hci; clear; lia) B1)) in HW end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
           assert (HDR0 : rw_cells asegs mq mhdr [C1 (b8 0); C1 (b8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)])
             by (apply (rw_cells_app asegs mq mhdr [C1 (b8 0); C1 (b8 b1); C2 (Z_to_bv 64 0)]); split; [exact HW| cbn [cells_size csize Nat.add]; change (Z.of_nat 4) with 4; exact HT]) end.
    all: clear HW HT.
    (* [comment removed for export] *)
    all: senv_img_at ENVY MUH WMH ENV1.
    all: assert (SHU1 := poisoned_carry _ _ _ _ _ _ SHUY MUH WMH ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; clear - SHR BND RU8 NR; try acb; lia)).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
           assert (MAG1 : rz = 16 \/ (32 <= rz /\ rw_cells asegs mq p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mhdr)]))
             by (destruct MAGY as [RZ16 | [RZ32 MC]]; [left; exact RZ16| right; split; [exact RZ32|]];
                 eapply rw_cells_transport; [exact MC| exact MUH| exact WMH| cbn [disjoint_from cells_size csize length Nat.add]; split; [| exact I]; left; clear - RZ32 PB; try acb; lia]) end.
    all: eapply rp_tail2; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rp_mid : forall (x16 x17 : word) (mX : mem),
    mem_inv asegs mX ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z m mX -> wmono asegs m mX ->
    stk asegs mX lo (bv_unsigned sp + -48) ->
    rw_cells asegs mX (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX cb [C8 (wz CA)] -> SENV tp TSD CTX TH mX ->
    rw_cells asegs mX (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)] -> rw_cells asegs mX (AINST + 48) [C8 (wz ARI)] ->
    rw_cells asegs mX R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)] ->
    rw_cells asegs mX mhdr [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n); C8 (wz actx)] ->
    (rz = 16 \/ (32 <= rz /\ rw_cells asegs mX p [C8 (wz 0xCC6E96B9CC6E96B9); C8 (wz mhdr)])) ->
    poisoned mX u (Z.to_nat (round_up n 8 / 8)) kAsanHeapFreeMagic -> stk asegs mX (TH + 2800) (TH + 3168) ->
    evt asegs (recycle_prim1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CA c p mhdr u rz n actx b1 TH)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz cb) (wz mhdr) (wz sb) (wz (sb + 2^37)) (wz c) (wz c) (wz (mhdr - sb)) (wz csz) x16 x17
               s2 (wz AINST) (wz (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1992c4) fc None mX (seg_rom asegs)).
  Proof.
    intros x16 x17 mX MIX MU WM STX FR CBX ENVX ISBX IRIX RIX HDRX MAGX SHUX TSTX.
    clear MI ST CBC ENV ISB IRI RI HDR MAG SHU TST. prep. clear Ha0 Ha1.
    assert (ICZ : 0 <= idx * csz) by (clear - IDX CS1; try acb; nia).
    assert (IDX' : idx * csz + csz <= mu) by (clear - IDX; try acb; nia).
    assert (RU8 : n <= round_up n 8 < n + 8 /\ round_up n 8 mod 8 = 0) by (unfold round_up; clear - NR; try acb; Z.div_mod_to_equations; lia).
    assert (PB : sb + c * 4294967296 <= p /\ p + csz <= sb + c * 4294967296 + mu /\ p + csz <= sb + (c + 1) * 4294967296 /\ mhdr + 16 = u /\ p + 16 <= u /\ u + round_up n 8 <= p + csz)
      by (rewrite EM, EU, PE, ERB; clear - IDX IDX' ICZ NR RZ CS1 HC; try acb; repeat split; lia).
    assert (BND : 17594333495296 <= p /\ p + 32 <= aceil /\ 17594333495296 <= mhdr /\ mhdr + 16 <= aceil /\ 17594333495296 <= u /\ u + 8 <= aceil
                  /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ aceil <= lo /\ bv_unsigned sp <= cb /\ cb + 8 <= 2^63)
      by (clear - PB SBR HC CS1 CS3 LO CBR RU8 NR; try acb; repeat split; nia).
    assert (E48 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR BND HI; try acb; lia).
    region_sides. name_bands.
    assert (SHR : 2148314624 <= sh u /\ sh u + round_up n 8 / 8 + 8 <= 17594333495296) by (unfold sh, ASHADOW_BASE; clear - BND PB RU8 NR HC CS1; try acb; Z.div_mod_to_equations; lia).
    pose proof (I : region_rank (sh u) 1) as RXRsh.
    assert (IDXB : 0 <= idx < 2^27).
    { assert (M32 : idx * 32 <= idx * csz) by (apply Z.mul_le_mono_nonneg_l; clear - IDX CS3 HC; try acb; lia). clear - IDX IDX' M32 CS3 HC; try acb. lia. }
    unfold wz in *. region_table.
    (* [comment removed for export] *)
    assert (OFF : (mhdr - sb) mod 2^32 = mhdr - sb - c * 4294967296) by (clear - PB HC RU8 NR; try acb; Z.div_mod_to_equations; nia).
    assert (DIVE : (mhdr - sb - c * 4294967296) / csz = idx).
    { rewrite EM, EU, PE, ERB. replace (sb + c * 4294967296 + idx * csz + rz - 16 - sb - c * 4294967296) with (idx * csz + (rz - 16)) by (clear; lia).
      rewrite Z.add_comm, Z.div_add by (clear - CS3 HC; try acb; lia). rewrite Z.div_small; [clear; lia|]. clear - RZ NR RU8 CS3 HC; try acb. lia. }
    step. rewrite (v_divuw_val (mhdr - sb) csz) by (rewrite ?OFF, ?DIVE; clear - PB BND CS1 CS3 HC IDX; try acb; lia). rewrite OFF, DIVE.
    step. step. step. step. step. step.
    rewrite ?(unsigned_lit c), ?(unsigned_lit ARI), ?(unsigned_lit idx) by (clear - HC SBR ARIE BND IDXB; try acb; lia).
    rewrite (Z.shiftl_mul_pow2 c 7), (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    change (2^7) with 128. replace (ARI + c * 128) with R by (rewrite ER; clear; lia). replace (c * 2^32 + sb) with rbeg by (rewrite ERB; clear; lia).
    (* [comment removed for export] *)
    assert (PRD : 0 <= csz * idx /\ csz * idx + csz <= mu /\ mu < 2^32) by (rewrite (Z.mul_comm csz idx); clear - ICZ IDX' IDX; try acb; lia).
    step. step. rewrite (shl32_val idx), (Z.shiftr_div_pow2 _ 32), (Z.div_mul idx (2^32)) by (clear - IDXB; try acb; lia).
    step. step. step.
    rewrite ?(unsigned_lit mu), ?(unsigned_lit csz), ?(unsigned_lit idx), ?(unsigned_lit (csz * idx)), ?(unsigned_lit (csz * idx + csz)) by (clear - IDXB PRD CS1; try acb; lia).
    rewrite v_sltu_ge by (rewrite ?(unsigned_lit mu), ?(unsigned_lit (csz * idx + csz)) by (clear - IDXB PRD CS1; try acb; lia); clear - PRD; try acb; lia).
    step. step. step.
    rewrite (unsigned_lit (rbeg + csz * idx)) by (rewrite ERB; clear - BND PRD HC CS1; try acb; lia).
    change 18446744073709551615 with (Z.ones 64). rewrite (Z.land_comm (Z.ones 64)), Z.land_ones by (clear; lia). rewrite Z.mod_small by (rewrite ERB; clear - BND PRD HC CS1; try acb; lia).
    replace (rbeg + csz * idx) with p by (rewrite PE, (Z.mul_comm csz idx); reflexivity).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - BND; try acb; lia). clear - BND PB HC CS3; try acb. intros K. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - BND; try acb; lia). clear - BND PB HC CS3; try acb. intros K. lia. } clear K.
    assert (PAL : p mod 8 = 0) by (rewrite PE, ERB; destruct SBA as [S4K]; clear - S4K CS2 HC IDX; try acb; Z.div_mod_to_equations; nia).
    assert (PR64 : 0 <= p < 2^64) by (clear - BND; try acb; lia).
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      eapply rp_tail; try eassumption. left. revert K. rewrite ?unsigned_lit by (clear - BND; try acb; lia). rewrite EM, EU. clear. intros K. lia.
    - (* [comment removed for export] *)
      destruct MAGX as [RZ16 | [RZ32 MC]]. { exfalso. apply K. rewrite EM, EU, RZ16. f_equal. clear; lia. }
      assert (PM : p + 16 <= mhdr) by (rewrite EM, EU; clear - RZ32; try acb; lia).
      pose proof (munch_refl [(p, p + 8)]%Z mX) as MUH. pose proof (wmono_refl asegs mX) as WMH.
      clear K. step. step. astep. step. if_cases K; zify_cond K. { deadK K. } clear K.
      astep. fix_lit_store. step. if_cases K; zify_cond K. { deadK K. } clear K.
      senv_img_at ENVX MUH WMH ENV1.
      assert (SHU1 := poisoned_carry _ _ _ _ _ _ SHUX MUH WMH ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; clear - SHR BND RU8 NR; try acb; lia)).
      eapply rp_tail; try eassumption. right. split; [exact RZ32| assumption].
  Qed.

  Theorem recycle_prim1 :
    evt asegs (recycle_prim1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CA c p mhdr u rz n actx b1 TH)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199214) fc None m (seg_rom asegs)).
  Proof.
    pose proof rp_mid as MID.
    prep. subst a0 a1.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mhdr, mhdr + 4); (sh u, sh u + round_up n 8 / 8); (TH + 2840, TH + 2856)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUF.
    assert (ICZ : 0 <= idx * csz) by (clear - IDX CS1; try acb; nia).
    assert (IDX' : idx * csz + csz <= mu) by (clear - IDX; try acb; nia).
    assert (RU8 : n <= round_up n 8 < n + 8 /\ round_up n 8 mod 8 = 0) by (unfold round_up; clear - NR; try acb; Z.div_mod_to_equations; lia).
    assert (PB : sb + c * 4294967296 <= p /\ p + csz <= sb + c * 4294967296 + mu /\ p + csz <= sb + (c + 1) * 4294967296 /\ mhdr + 16 = u /\ p + 16 <= u /\ u + round_up n 8 <= p + csz)
      by (rewrite EM, EU, PE, ERB; clear - IDX IDX' ICZ NR RZ CS1 HC; try acb; repeat split; lia).
    assert (BND : 17594333495296 <= p /\ p + 32 <= aceil /\ 17594333495296 <= mhdr /\ mhdr + 16 <= aceil /\ 17594333495296 <= u /\ u + 8 <= aceil
                  /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ aceil <= lo /\ bv_unsigned sp <= cb /\ cb + 8 <= 2^63)
      by (clear - PB SBR HC CS1 CS3 LO CBR RU8 NR; try acb; repeat split; nia).
    assert (SHR : 12599296 <= sh u /\ sh u + round_up n 8 / 8 + 8 <= 17594333495296) by (unfold sh, ASHADOW_BASE; clear - BND PB RU8 NR HC CS1; try acb; Z.div_mod_to_equations; lia).
    region_sides. name_bands.
    pose proof (I : region_rank (sh u) 1) as RXRsh.
    assert (EC : Z.shiftr (mhdr - sb) 32 = c) by (rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite EM, EU, PE, ERB; clear - IDX ICZ IDX' NR RZ RU8 HC CS1; try acb; Z.div_mod_to_equations; nia).
    assert (EA : Z.land c 31 = c) by (change 31 with (Z.ones 5); rewrite Z.land_ones by (clear; lia); apply Z.mod_small; clear - HC; try acb; lia).
    (* [comment removed for export] *)
    all: unfold wz in *; region_table.
    (* [comment removed for export] *)
    all: step; carve_frame 48%nat ST; spill_frame ltac:(do 6 step); do 4 step.
    (* [comment removed for export] *)
    all: do 3 step.
    all: step; [if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - BND; try acb; lia); clear - BND PB HC; try acb; intros K; lia| clear K]..].
    all: step; step; [if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - BND; try acb; lia); clear - BND PB HC RU8 NR CS3; try acb; intros K; lia| clear K]..].
    (* [comment removed for export] *)
    all: do 4 step.
    all: rewrite ?(unsigned_lit mhdr), ?(unsigned_lit sb) by (clear - BND; try acb; lia); rewrite (unsigned_lit (mhdr - sb)) by (clear - BND PB HC; try acb; lia); rewrite EC, (unsigned_lit c), EA by (clear - HC; try acb; lia).
    (* [comment removed for export] *)
    all: senv_img_at ENV MUF WM ENV1.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
           assert (SHU1 := poisoned_carry _ _ _ _ _ _ SHU MUF WM ltac:(hci; cbn [disjoint_from]; split; [| exact I]; left; clear - SHR BND HI RU8 NR; try acb; lia)) end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
           assert (MAG1 : rz = 16 \/ (32 <= rz /\ rw_cells asegs mq p [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 mhdr)]))
             by (destruct MAG as [RZ16 | [RZ32 MC]]; [left; exact RZ16| right; split; [exact RZ32|]];
                 eapply rw_cells_transport; [exact MC| exact MUF| exact WM| cbn [disjoint_from cells_size csize length Nat.add]; split; [| exact I]; left; clear - BND HI; try acb; lia]) end.
    (* [comment removed for export] *)
    all: step; [if_cases K; zify_cond K..].
    1: rewrite ?unsigned_lit in K by (clear - HC; try acb; lia); do 2 step;
         replace (Z_to_bv 64 64) with (Z_to_bv 64 csz) by (subst csz; unfold class_size; rewrite (proj2 (Z.eqb_eq c 31) K); reflexivity);
         eapply MID; try eassumption.
    all: step; step; [if_cases K2; zify_cond K2..]; rewrite ?unsigned_lit in K2 by (clear - HC; try acb; lia).
    1: eapply evt_cut; [eapply rsize_hi_spec; clear - K K2 HC; try acb; lia|]; intros ms1 PO; destruct PO as (x16 & x17 & ->); unfold wz; fold csz;
         eapply MID; try eassumption.
    all: step; [if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by (clear - HC; try acb; lia); clear - HC; try acb; intros K3; lia| clear K3]..].
    all: step; rewrite (unsigned_lit c) by (clear - HC; try acb; lia); rewrite (Z.shiftl_mul_pow2 c 5) by (clear; lia);
         replace (c * 2^5) with csz by (subst csz; unfold class_size; replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; clear - K; try acb; lia);
                                          replace (c <=? 16) with true by (symmetry; apply Z.leb_le; clear - K2; try acb; lia); clear; lia).
    all: step; eapply MID; try eassumption.
  Qed.
End RecPrim.

