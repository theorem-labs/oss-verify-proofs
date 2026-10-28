(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AW_AllocBaseAl AW_Alloc1Al AW_Alloc2Al AllocTacX. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Section Alloc.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (d : depot).
  Variables (TSD CTX TH : Z).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  (* [comment removed for export] *)
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: nil.
  Let POST := allocate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                            (d_put d (depot_hash T) n).
  Let AFR := aframeAl sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 352 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  (* [comment removed for export] *)
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Let PLACED : Prop := ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).

  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis ABR : hidden (sb <= AB /\ AB + csz <= sb + kSpaceSize).
  Hypothesis ABA : hidden (AB mod 64 = 0).   (* [comment removed for export] *)
  Hypothesis RZ64 : hidden (rz mod 64 = 0).  (* [comment removed for export] *)
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis NR : 1 <= n <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + n + 1 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.


  (* [comment removed for export] *)
  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328)
      by (clear - LO RNG SBR ABR TPR SOR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SOR as [SOR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SOR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz + 64 <= needed /\ 8 + rz <= needed /\ needed < size + rz + 128)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 64 - 1) / 64 * 8 + 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 4294967296 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T))) by (constructor; repeat split; assumption);
    assert (C8F : 8 * csz8 = csz /\ 1 <= fl <= size /\ fl <= 4096) by (clear - ALN SZ DC8 DFL; try acb; subst csz8 fl; Z.div_mod_to_equations; lia);
    assert (FLh : hidden (fl = Z.min size 4096)) by (constructor; exact DFL);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (LENQ : Z.of_nat (length (wlist (rev (tl chunks)))) = cnt - 1)
      by (clear - CNT HIT; try acb; unfold wlist; rewrite length_map, length_rev; destruct chunks;
          [unfold zlen in CNT; cbn in CNT; lia| cbn [tl]; unfold zlen in CNT; cbn [length] in CNT; lia]);
    (* [comment removed for export] *)
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

  (* [comment removed for export] *)
  Ltac plia :=
    first [ lia
          | match goal with H : hidden PLACED |- _ =>
              let P := fresh "PLu" in pose proof H as P; destruct P as [P]; unfold PLACED, kSpaceSize, AHI_LO in P;
              let A1 := fresh "PA" in let A2 := fresh "PA" in let A3 := fresh "PA" in
              let B1 := fresh "PB" in let B2 := fresh "PB" in let B3 := fresh "PB" in let B4 := fresh "PB" in
              let B5 := fresh "PB" in let B6 := fresh "PB" in let B7 := fresh "PB" in let B8 := fresh "PB" in
              destruct P as [[A1 [A2 A3]] [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]]];
              first [ clear A2 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B5; lia ]
            end ].

  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; plia |]]).

  (* [comment removed for export] *)
  Ltac remregF n name eqname folded :=
    remreg n name eqname; match type of eqname with ?e = _ => change (e = folded) in eqname end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Lemma partC3 : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mX : mem) (j8 : list byte) (jj0 jj1 jj2 jj3 : word) (ob0 : byte) (hb1 q8 r8 rz8 : Z) (shd : list byte),
    size = 8 * q8 + r8 -> 0 <= r8 < 8 -> rz = 8 * rz8 ->
    AENV tp TSD CTX TH sb SO T rest mX -> mem_inv asegs mX -> munch W m mX -> wmono asegs m mX ->
    AFR mX j8 -> stk asegs mX lo (bv_unsigned sp + -128) ->
    rw_cells asegs mX P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mX (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mX (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mX (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    rw_cells asegs mX (U + -16) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mX AB (U + -16) -> stk asegs mX U (AB + csz) ->
    u8arr asegs mX (sh AB) shd -> shd = pre_shadow rz8 q8 csz8 -> Z.of_nat (length shd) = csz8 ->
    stk asegs mX (TH + 2800) (TH + 3168) ->
    forall mC, DEPOT asegs (d_put d (depot_hash T) n) mC -> munch W2 mC mX -> wmono asegs mC mX ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) x10 x11 x12 x13 x14 x15 x16 x17
               (wz AB) (wz needed) (wz U) (wz (U + -16)) (wz (8 * q8)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1972b4) fc None mX (seg_rom asegs)).
  Proof.
    intros until shd. intros SZQ R8 RZ8 ENV MI MU WM FR ST QC1 QC3 QC4 QST HDR HB1R HB1M CHL USR SHD SHDE SHDN TST mC DEPC MUC WMC.
    unfold W in MU. unfold W2 in MUC. prep. open_env ENV. unfold AFR, aframeAl in FR. unfold wz in *.
    assert (FIT : 0 <= rz8 /\ 0 <= q8 /\ rz8 + q8 <= csz8) by (clear - RZ8 SZQ R8 RZB CSZ C8F; try acb; lia).
    destruct EQS as (EU & EP & EAB & En & ECA).
    pose proof (bv_unsigned_in_range _ ob0) as OB0. change (bv_modulus 8) with 256 in OB0. rewrite <- (b8_of_byte ob0) in HDR.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      eapply partD; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]); try (lia_guard; lia).
      rewrite SHDE. unfold pre_shadow, alloc_shadow.
      rewrite (shadow_of_mult8 size) by (clear - SZQ R8 K SZ; try acb; lia).
      f_equal; [f_equal; clear - RZ8 RZB; try acb; Z.div_mod_to_equations; lia|].
      f_equal; [f_equal; clear - SZQ R8 K SZ; try acb; Z.div_mod_to_equations; lia|].
      f_equal. unfold round_up. clear - SZQ R8 K SZ RZ8 C8F RZB; try acb. Z.div_mod_to_equations. nia.
    - (* [comment removed for export] *)
      assert (R8P : 1 <= r8 /\ rz8 + q8 + 1 <= csz8).
      { unhide_hyp EQh. destruct EQh as (_ & _ & _ & EN & _). clear - K RZ8 SZQ R8 RZB CSZ C8F EN SZ; try acb. unfold round_up in EN. Z.div_mod_to_equations. (first [clear - SZ SZQ R8 RZ8 CSZ RZB EN C8F K H H0; nia | nia]). }
      step. callD can_poison_spec. all: try (unfold ACANPOISON; eassumption).
      step. if_cases K2. { exfalso. revert K2. vm_compute. discriminate. } clear K2.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step. step.
      match goal with |- context [Z_to_bv 64 (Z.land ?x 2147450879)] =>
        replace (Z_to_bv 64 (Z.land x 2147450879)) with (Z_to_bv 64 2147450879) by (apply bv_eq; vm_compute; reflexivity) end.
      step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. clear - K3 BND EU RZB FIT C8F CSZ RZ8; try acb. lia. } clear K3.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      step. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. revert K4. rewrite ?unsigned_lit by lia.
        change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615. clear - BND EU RZB FIT CSZ C8F RZ8; try acb. intros K4. lia. }
      clear K4.
      (* [comment removed for export] *)
      step. step. step. step. step.
      step. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia. { exfalso. clear - K5 BND EU RZB FIT CSZ C8F RZ8; try acb. lia. } clear K5.
      step. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. { exfalso. clear - K6 BND EU RZB FIT CSZ C8F RZ8; try acb. lia. } clear K6.
      (* [comment removed for export] *)
      step. step. step. rewrite zxb_b8 by lia. step. step. step. step. step.
      match goal with |- context [Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.land ?x ?y))) 7)] =>
        replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.land x y))) 7)) with (Z_to_bv 64 r8) end.
      2:{ f_equal. replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz 1))))) with (Z.ones 64) by (vm_compute; reflexivity).
          rewrite (unsigned_lit size), Z.land_ones by (unfold kMaxSize in SZ; lia). rewrite Z.mod_small by (unfold kMaxSize in SZ; lia).
          rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - SZQ R8; try acb. Z.div_mod_to_equations. lia. }
      rewrite (unsigned_lit (U + 8 * q8)) by (first [clear - HI SZ SZQ R8 RZ8 SPR BND CSZ RZB ALN EU EAB C8F R8P; lia | lia]).
      replace (2147450880 + (U + 8 * q8) ≫ 3) with (sh AB + (rz8 + q8) + 0)
        by (rewrite Z.shiftr_div_pow2, EU, EAB, RZ8 by lia; unfold sh, ASHADOW_BASE; clear - ALN FIT; try acb; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      rewrite SHDE in SHD. unfold pre_shadow in SHD.
      apply u8arr_app in SHD. destruct SHD as [SH1 SHD]. apply u8arr_app in SHD. destruct SHD as [SH2 SH3].
      rewrite !repeat_length, !Z2Nat.id in SH2 by lia. rewrite !repeat_length, !Z2Nat.id in SH3 by lia.
      replace (sh AB + rz8 + q8) with (sh AB + (rz8 + q8)) in SH3 by lia.
      replace (Z.to_nat (csz8 - rz8 - q8)) with (S (Z.to_nat (csz8 - rz8 - q8 - 1))) in SH3 by (first [clear - SPR BND CSZ R8P; lia | lia]). cbn [repeat] in SH3.
      change (b8 250 :: repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8 - 1))) with ([b8 250] ++ repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8 - 1))) in SH3.
      apply u8arr_app in SH3. destruct SH3 as [SHB SH4]. change (Z.of_nat (length [b8 250])) with 1 in SH4.
      apply (rw_cells_of_u8arr asegs) in SHB. cbn [length] in SHB. apply rw_cells_CB1 in SHB.
      (* [comment removed for export] *)
      assert (L1 : Z.of_nat (length (repeat (b8 250) (Z.to_nat rz8))) = rz8) by (rewrite repeat_length; (first [clear - RZ8 SPR BND CSZ RZB; lia | lia])).
      assert (L2 : Z.of_nat (length (repeat (b8 0) (Z.to_nat q8))) = q8) by (rewrite repeat_length; (first [clear - SZ SZQ R8 SPR BND CSZ R8P; lia | lia])).
      assert (L4 : Z.of_nat (length (repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8 - 1)))) = csz8 - rz8 - q8 - 1) by (rewrite repeat_length; (first [clear - SPR BND CSZ R8P; lia | lia])).
      remember (sh AB + (rz8 + q8)) as SA eqn:ESA in *.
      (* [comment removed for export] *)
      st1.
      subst SA. replace (r8 mod 256) with r8 in SHB by (symmetry; apply Z.mod_small; lia).
      (* [comment removed for export] *)
      apply rw_cells_C1, (u8arr_of_rw_cells asegs) in SHB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SHD' : u8arr asegs mm (sh AB) (repeat (b8 250) (Z.to_nat rz8) ++ (repeat (b8 0) (Z.to_nat q8) ++ ([b8 r8] ++ repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8 - 1)))))) end.
      { apply u8arr_app. rewrite repeat_length, Z2Nat.id by lia. split; [exact SH1|].
        apply u8arr_app. rewrite repeat_length, Z2Nat.id by lia. split; [exact SH2|].
        replace (sh AB + rz8 + q8) with (sh AB + (rz8 + q8)) by lia.
        apply u8arr_app. split; [exact SHB| exact SH4]. }
      clear SH1 SH2 SHB SH4 L1 L2 L4.
      eapply partD; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]); try (lia_guard; (lia_guard; lia)).
      + unfold alloc_shadow. unfold shadow_of.
        replace (size mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; clear - SZQ R8 R8P; try acb; Z.div_mod_to_equations; lia).
        rewrite <- app_assoc. f_equal; [f_equal; clear - RZ8 RZB; try acb; Z.div_mod_to_equations; lia|].
        f_equal; [f_equal; clear - SZQ R8 SZ; try acb; Z.div_mod_to_equations; lia|].
        cbn [app]. f_equal; [f_equal; clear - SZQ R8 SZ; try acb; Z.div_mod_to_equations; lia|].
        f_equal. unfold round_up. clear - SZQ R8 R8P SZ RZ8 C8F RZB; try acb. Z.div_mod_to_equations. nia.
      + rewrite !length_app, !repeat_length. cbn [length]. (first [clear - R8P FIT; lia | lia]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partC2 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x26 x27 x28 x29 x30 x31 : word)
      (mX : mem) (j8 j8b : list byte) (jj0 jj1 jj2 jj3 : word) (ob0 : byte) (hb1 : Z),
    AENV tp TSD CTX TH sb SO T rest mX -> mem_inv asegs mX -> munch W m mX -> wmono asegs m mX ->
    AFR mX j8 -> stk asegs mX lo (bv_unsigned sp + -128) ->
    rw_cells asegs mX P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mX (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mX (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mX (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    rw_cells asegs mX (U + -16) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); CB 8 j8b] ->
    0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mX AB (U + -16) -> stk asegs mX U (AB + csz) ->
    u8arr asegs mX (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mX (TH + 2800) (TH + 3168) ->
    forall mC, DEPOT asegs d mC -> munch W2 mC mX -> wmono asegs mC mX ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 1) (wz size) x10 x11 x12 x13 x14 x15 x16 x17
               (wz AB) (wz needed) (wz U) (wz (U + -16)) x22 (wz SO) (wz 0) x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x19719c) fc None mX (seg_rom asegs)).
  Proof.
    intros until hb1. intros ENV MI MU WM FR ST QC1 QC3 QC4 QST HDR HB1R HB1M CHL USR SHK TST mC DEPC MUC WMC.
    unfold W in MU. unfold W2 in MUC. prep. open_env ENV. unfold AFR, aframeAl in FR. unfold wz in *.
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    destruct EQS as (EU & EP & EAB & En & ECA).
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs d _ mm) in DEPC; [| exact MUC | exact WMC | solve_depot_avoid] end.
    clear MUC WMC. try clear mC.
    assert (IDR : 1 <= id < 65536) by (unhide_hyp EQh; destruct EQh as (_ & _ & _ & _ & _ & Eid); rewrite Eid; apply d_putid_range; [exact (proj1 DEPC)| lia]).
    unfold depot_W in MU.
    step. callDep (depot_put_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo (SO + 16) T rest d).
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try (first [clear - En NR HI BND DCAP RXb RXb0; lia | (lia_guard; lia)]).
    all: try (unfold AIMG_TOP; (lia_guard; lia)). all: try (unfold wz; f_equal; (lia_guard; lia)).
    clear DEPC. fold (depot_W d) in MU.
    lazymatch goal with H : DEPOT asegs _ ?mm |- _ => rename H into DEPN; replace (Z.of_nat (length T)) with n in DEPN by exact En;
      pose proof (munch_refl W2 mm) as MUC; pose proof (wmono_refl asegs mm) as WMC; unfold W2 in MUC end.
    (* [comment removed for export] *)
    step. step. step. unhide_hyp EQh. destruct EQh as (Ec & Ecsz & Erz & Eneeded & Ecp & Eid). rewrite <- Eid.
    match goal with |- context [Z_to_bv 64 (Z.lor 0 ?x)] => replace (Z_to_bv 64 (Z.lor 0 x)) with (Z_to_bv 64 id) end.
    2:{ f_equal. rewrite Z.lor_0_l. unfold wz. rewrite (unsigned_lit id), Z.shiftl_mul_pow2 by lia.
        rewrite (unsigned_lit (id * 2^32)), Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. reflexivity. }
    step.
    (* [comment removed for export] *)
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. step. step. step.
    rewrite (unsigned_lit AB) by lia.
    replace (2147450880 + AB ≫ 3) with (sh AB) by (unfold sh, ASHADOW_BASE; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_read asegs mm _ _ 0 (b8 250) (wa (sh AB)) SHK
                    ltac:(hci; change (Z.to_nat 0) with 0%nat; destruct (Z.to_nat csz8) eqn:EE; [lia| reflexivity]) ltac:(hci; lia) ltac:(hci; unfold wa; f_equal; lia)) as RD end.
    step. clear RD. step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    assert (QR : exists q8 r8, size = 8 * q8 + r8 /\ 0 <= r8 < 8) by (clear; exists (size / 8), (size mod 8); Z.div_mod_to_equations; lia).
    destruct QR as (q8 & r8 & SZQ & R8).
    set (rz8 := 2 * rzk). assert (RZ8 : rz = 8 * rz8) by lia. clearbody rz8.
    assert (FIT : 0 <= rz8 /\ 0 <= q8 /\ rz8 + q8 <= csz8) by (clear - RZ8 SZQ R8 RZB CSZ C8F; try acb; lia).
    step. step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 size)) 281474976710648) with (8 * q8)
      by (rewrite (unsigned_lit size), land_m48_8 by (unfold kMaxSize in SZ; lia); clear - SZQ R8; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      replace q8 with 0 in * by lia.
      eapply (partC3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 r8 rz8); try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]); try (lia_guard; lia).
      symmetry. apply pre_shadow_0. lia.
    - (* [comment removed for export] *)
      assert (E3 : repeat (b8 250) (Z.to_nat csz8) = repeat (b8 250) (Z.to_nat rz8) ++ (repeat (b8 250) (Z.to_nat q8) ++ repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8))))
        by (rewrite <- !repeat_app; f_equal; (first [clear - FIT; lia | lia])).
      rewrite E3 in SHK. clear E3 SHKL. apply u8arr_app in SHK. destruct SHK as [SH1 SHK]. apply u8arr_app in SHK. destruct SHK as [SH2 SH3].
      rewrite !repeat_length, !Z2Nat.id in SH2 by lia. rewrite !repeat_length, !Z2Nat.id in SH3 by lia.
      replace (sh AB + rz8 + q8) with (sh AB + (rz8 + q8)) in SH3 by lia.
      assert (L1 : Z.of_nat (length (repeat (b8 250) (Z.to_nat rz8))) = rz8) by (rewrite repeat_length; lia).
      assert (L3 : Z.of_nat (length (repeat (b8 250) (Z.to_nat (csz8 - rz8 - q8)))) = csz8 - rz8 - q8) by (rewrite repeat_length; lia).
      step. step. step. step.
      callD (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo U (sh AB + rz8) q8 0 (repeat (b8 250) (Z.to_nat q8)))
        by (rewrite ?unsigned_lit by lia; try eassumption; try (lia_guard; (lia_guard; (lia_guard; first [clear - HI; lia | lia]))); try (unfold wz; f_equal; (lia_guard; (lia_guard; (lia_guard; lia))));
            try (unfold AGOT_LO, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, ACANPOISON; eassumption);
            try (rewrite repeat_length; lia)).
      all: try (rewrite EU, EAB, RZ8; unfold sh; clear - ALN FIT; try acb; Z.div_mod_to_equations; lia).
      all: try (unfold AHI_LO; acb; clear - BND FIT K EU RZ8 ALN EAB C8F CSZ; try acb;
                repeat split; try lia; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      lazymatch goal with H : u8arr asegs ?mm (sh AB + rz8) (repeat (b8 0) _) |- _ =>
        assert (SHD' : u8arr asegs mm (sh AB) (pre_shadow rz8 q8 csz8))
          by (unfold pre_shadow; apply u8arr_app; rewrite repeat_length, Z2Nat.id by lia; split; [exact SH1|];
              apply u8arr_app; rewrite repeat_length, Z2Nat.id by lia; split; [exact H|];
              replace (sh AB + rz8 + q8) with (sh AB + (rz8 + q8)) by lia; exact SH3);
        clear SH1 H SH3 L1 L3 end.
      eapply (partC3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q8 r8 rz8); try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]); try (lia_guard; (lia_guard; lia)).
      apply pre_shadow_length; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Alloc.
