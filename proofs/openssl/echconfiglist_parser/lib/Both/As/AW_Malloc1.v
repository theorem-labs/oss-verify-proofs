(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AW_Allocate AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AllocTacX. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.

Section Icpt.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bf41c (bv_unsigned sp) TOP BOT 30 CHI.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: depot_W d.
  Let W2 : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: nil.
  Let POST := malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                          (d_put d (depot_hash T) n).

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
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
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  (* [comment removed for export] *)
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.

  Ltac prepI :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    pose proof (bv_unsigned_in_range _ ra) as RAR; change (bv_modulus 64) with (2^64)%Z in RAR;
    pose proof (bv_unsigned_in_range _ s0) as S0R; change (bv_modulus 64) with (2^64)%Z in S0R;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP)
      by (clear - LO RNG SBR ABR TPR SPT TBR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz <= needed /\ 8 + rz <= needed /\ needed < size + rz + 8)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 8 - 1) / 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 2 ^ 32 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T) /\ T = utrace 0x1bf41c (bv_unsigned sp) TOP BOT 30 CHI
                       /\ CHI = icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH /\ csz8 = csz / 8)) by (constructor; repeat split; first [assumption | reflexivity]);
    assert (C8F : 8 * csz8 = csz) by (clear - ALN DC8; try acb; subst csz8; Z.div_mod_to_equations; lia);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (NR : 1 <= n <= 30) by (rewrite DN; unfold T; apply utrace_length; lia);
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

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
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  (* [comment removed for export] *)
  Lemma ienv_now : forall m1, IENV tp TSD CTX TH sb TOP BOT m -> munch W m m1 -> wmono asegs m m1 -> IENV tp TSD CTX TH sb TOP BOT m1.
  Proof.
    intros m1 E MU WM. unfold W in MU. unfold depot_W in MU. prepI. open_ienv E.
    region_table; lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    constructor; unfold AGOT_VALS; cbn [map repeat];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; slia]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma icpt2 : forall (x1 x5 x6 x7 x15 x16 x19 x28 x29 x30 x31 : word) (mX : mem) (jbuf j5 : list byte),
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs mX -> munch W m mX -> wmono asegs m mX ->
    rw_cells asegs mX (bv_unsigned sp + -2128)
      [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C8 (Z_to_bv 64 0); CB 2040 jbuf; C8 sp;
       CB 8 j5; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs mX lo (bv_unsigned sp + -2128) ->
    rw_cells asegs mX P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs mX (P + 8) [C8 (wz csz)] -> u32arr asegs mX (P + 16) (wlist (rev chunks)) ->
    stk asegs mX (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs mX (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs mX AB (AB + csz) ->
    u8arr asegs mX (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mX (TH + 2800) (TH + 3168) -> rw_cells asegs mX (TH + 3168) [C1 (b8 0)] ->
    forall mC, DEPOT asegs d mC -> munch W2 mC mX -> wmono asegs mC mX ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp (wz size)
               (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1831964) sp (Z_to_bv 64 0) (zxb (b8 1)) (wz 30) x15 x16
               (Z_to_bv 64 1831964) x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1bf474) fc None mX (seg_rom asegs)).
  Proof.
    intros until j5. intros ENV MI MU WM FRW ST QC1 QC2 QC3 QC4 QST CHUNK SHK TST UNW mC DEP MUC WMC.
    unfold W in MU. unfold W2 in MUC. prepI. unfold wz in *.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F0 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F1 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F2 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F3 F4]. cbn [cells_size csize Nat.add] in F4.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8) with (bv_unsigned sp + -2120) in F1 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -2112) in F2 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2040) with (bv_unsigned sp + -72) in F3 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2040 + Z.of_nat 8) with (bv_unsigned sp + -64) in F4 by lia.
    apply rw_cells_C8_zero_split in F1.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in F1. destruct F1 as [SZC PAD]. cbn [cells_size csize Nat.add] in PAD.
    replace (bv_unsigned sp + -2120 + Z.of_nat 4) with (bv_unsigned sp + -2116) in PAD by lia.
    change 2040%nat with (8 * 255)%nat in F2. destruct (u64arr_of_junk _ _ 255 _ F2) as (buf & BUF & LBUF). clear F2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (REC : rw_cells asegs mm (bv_unsigned sp + -16) [C8 (wz (bv_unsigned s0)); C8 (wz (bv_unsigned ra))]) end.
    { unfold wz. rewrite !Z_to_bv_bv_unsigned.
      apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])) in F4.
      destruct F4 as [_ R]. cbn [cells_size csize Nat.add] in R.
      replace (bv_unsigned sp + -64 + Z.of_nat 48) with (bv_unsigned sp + -16) in R by lia. exact R. }
    assert (BELOW : goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true -> goodframe BOT (bv_unsigned sp) TOP = true -> below W (bv_unsigned s0 - 16)).
    { intros G2 G1. destruct (FCH G1 G2) as [LE _]. unfold W, depot_W, below. intros l h Hin.
      cbn [In] in Hin. clear - Hin LE HI BND PB CSZ C8F SHR DLO EQS HC; try acb.
      repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; lia|]). destruct Hin. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FCH2 : goodframe BOT (bv_unsigned sp) TOP = true -> frame_chain asegs mm TOP (bv_unsigned sp) CHI) end.
    { intros G1. unfold CHI, icpt_chain.
      destruct (Sumbool.sumbool_of_bool (goodframe (bv_unsigned sp) (bv_unsigned s0) TOP)) as [G2|G2]; rewrite G2.
      - destruct (FCH G1 G2) as [LE FC]. apply fc_link; [exact REC| lia| lia| exact G2|].
        eapply frame_chain_transport; [exact FC| apply BELOW; assumption| exact MU| exact WM].
      - apply fc_last; [exact REC| lia| lia| exact G2]. }
    clear BELOW REC.
    (* [comment removed for export] *)
    pose proof (ienv_now _ ENV MU WM) as E.
    pose proof (i_got _ _ _ _ _ _ _ _ E) as Egot. unfold AGOT_VALS in Egot. cbn [map] in Egot.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Egot. destruct Egot as [GOTC _].
    pose proof (i_psc _ _ _ _ _ _ _ _ E) as PGC. pose proof (i_init _ _ _ _ _ _ _ _ E) as AI.
    pose proof (i_tsdi _ _ _ _ _ _ _ _ E) as TK. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in TK. destruct TK as [TKI TK].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in TK. destruct TK as [_ TKK]. cbn [cells_size csize length Nat.add] in TKK.
    replace (6988128 + Z.of_nat 1 + Z.of_nat 3) with 6988132 in TKK by reflexivity.
    pose proof (i_tp _ _ _ _ _ _ _ _ E) as TPC. pose proof (i_tsd _ _ _ _ _ _ _ _ E) as TSDC. pose proof (i_ctx _ _ _ _ _ _ _ _ E) as CTXC.
    pose proof (i_stk _ _ _ _ _ _ _ _ E) as TC. pose proof (i_t40 _ _ _ _ _ _ _ _ E) as T40. clear E. unfold wz in *.
    (* [comment removed for export] *)
    step.
    match goal with |- context [TNode (TNode TEmpty (Some (Z_to_bv 64 ?x)) TEmpty) (Some sp) (TNode TEmpty (Some ?y) TEmpty)] =>
      replace (TNode (TNode TEmpty (Some (Z_to_bv 64 x)) TEmpty) (Some sp) (TNode TEmpty (Some y) TEmpty))
         with (TNode (TNode TEmpty (Some (Z_to_bv 64 x)) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp))) (TNode TEmpty (Some y) TEmpty))
           by (rewrite Z_to_bv_bv_unsigned; reflexivity) end.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (unwindimpl_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ F fc (bv_unsigned sp + -2128) 255 lo 7578528 1831964
                                 (bv_unsigned sp) TOP BOT 30 buf mm TSD CTX TH) | post_callUI segs mm ] end.
    all: unfold KPAGE, AIMG_LO, AIMG_TOP, OFF_UNWINDING, GOT_PAGESIZECACHED, ASAN_INITED, TSD_KEY_INITED, TSD_KEY, wz; rewrite ?unsigned_lit by (first [clear - HI SPR BND ALN SPQ; lia | lia]).
    all: try eassumption. all: try (first [clear - BND HI; (lia_guard; first [clear - HI BND; lia | lia]) | (lia_guard; (first [clear - BND RXS5; lia | lia]))]).
    all: try (match goal with TB : akobj TH 4096 |- _ => clear - TB BND HI LO end; aunf; (lia_guard; lia)).   (* [comment removed for export] *)
    all: try (replace (bv_unsigned sp + -2128 + 8) with (bv_unsigned sp + -2120) by lia; eexists; exact SZC).
    all: try (replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact BUF).
    all: try (replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) by lia; exact F3).
    clear GOTC PGC AI TKI TKK TPC TSDC CTXC TC T40 FCH2.
    unhide_hyp EQh. destruct EQh as (Ec & Ecsz & Erz & Eneeded & Ecp & Eid & ET & ECHI & E8).
    destruct EQS as (EU & EP & EAB & En & ECA).
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2128 + 8) [C4 _] |- _ => fold CHI in H; fold T in H; rename H into SZT end.
    lazymatch goal with H : u64arr asegs _ (bv_unsigned sp + -2128 + 16) _ |- _ => fold CHI in H; fold T in H; rename H into TRB end.
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2128 + 2056) _ |- _ => rename H into TFB end.
    lazymatch goal with H : rw_cells asegs _ (TH + 3168) _ |- _ => rename H into UNW end.
    lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST end.
    replace (bv_unsigned sp + -2128 + 8) with (bv_unsigned sp + -2120) in SZT by lia.
    replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in TFB by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Eso : rw_cells asegs mm (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]) end.
    { apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [unfold wz; replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact F0|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -2128 + Z.of_nat 8) with (bv_unsigned sp + -2120) by lia.
      apply rw_cells_C4C4_C8; [clear - NR En; try acb; lia|]. apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [exact SZT|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -2120 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. exact PAD. }
    clear F0 SZT PAD.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 16%nat ST. st1. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs d _ mm) in DEP; [| exact MUC | exact WMC | solve_depot_avoid] end.
    clear MUC WMC.
    (* [comment removed for export] *)
    pose proof (ienv_now _ ENV MU WM) as E. open_ienv E.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AE : AENV tp TSD CTX TH sb (bv_unsigned sp + -2128) T (drop (length T) buf) mm) by (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact TRB]) end.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Emcs Epsc Ecfu Estk Et40.
    unfold depot_W in MU.
    step.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (allocate_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm lo size (bv_unsigned sp + -2128)
         T (drop (length T) buf) d TSD CTX TH sb cnt mc chunks j0 j1 j2 j3 rz needed c csz csz8 fl CA P cp AB U n id) | post_callA segs mm ] end.
    all: rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]).
    all: try exact DEFS. all: try exact AE. all: try eassumption. all: try reflexivity. all: try (lia_guard; lia).
    all: try (constructor; (first [clear - SPQ BND; lia | lia])).
    clear AE.
    { (* [comment removed for export] *)
      unfold T. apply utrace_range'; [| lia]. intros G1. unfold CHI, icpt_chain.
      destruct (Sumbool.sumbool_of_bool (goodframe (bv_unsigned sp) (bv_unsigned s0) TOP)) as [G2|G2]; rewrite G2.
      - constructor; [cbn [fst]; lia|]. destruct (FCH G1 G2) as [_ FC]. eapply frame_chain_ranges. exact FC.
      - constructor; [cbn [fst]; lia| constructor]. }
    fold (depot_W d) in MU.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    { exfalso. clear - K BND HC RZB CSZ EU EAB; try acb. unfold wz in K. rewrite unsigned_lit in K by lia. lia. }
    clear K.
    step. step. step. step.
    step. do 7 step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with H : u64arr asegs _ (bv_unsigned sp + -2128 + 16) _ |- _ => rename H into TRB' end.
    assert (LT : (1 <= length T <= 30)%nat) by (clear - NR En; try acb; lia).
    lazymatch goal with F16 : rw_cells asegs ?mm (bv_unsigned sp + -2144) _, F64 : rw_cells asegs _ (bv_unsigned sp + -64) _,
                         STL : stk asegs _ lo (bv_unsigned sp + -2144) |- _ =>
      pose proof (stk_of_rw_cells asegs _ _ _ F16) as K1; pose proof (stk_of_rw_cells asegs _ _ _ Eso) as K2;
      pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4; pose proof (stk_of_rw_cells asegs _ _ _ F64) as K5;
      pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB'))) as K3;
      cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5;
      rewrite u64s_length, length_app, length_map, length_skipn, LBUF in K3;
      assert (STF : stk asegs mm lo (bv_unsigned sp))
        by (eapply stk_merge; [exact STL| |lia]; eapply stk_merge; [exact K1| |lia];
            replace (bv_unsigned sp + -2144 + Z.of_nat 16) with (bv_unsigned sp + -2128) by lia;
            eapply stk_merge; [exact K2| |lia]; replace (bv_unsigned sp + -2128 + Z.of_nat 16) with (bv_unsigned sp + -2128 + 16) by lia;
            eapply stk_merge; [exact K3| |(first [clear - CSZ En NR; lia | lia])];
            replace (bv_unsigned sp + -2128 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -72) by (first [clear - SPR BND CSZ LT; lia | lia]);
            eapply stk_merge; [exact K4| |lia]; replace (bv_unsigned sp + -72 + Z.of_nat 8) with (bv_unsigned sp + -64) by lia;
            replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat 64) at 2 by lia; exact K5);
      clear K1 K2 K3 K4 K5 STL F16 Eso TRB' TFB F64 end.
    apply evt_done. unfold POST, malloc_post.
    do 14 eexists.
    lazymatch goal with H : rw_cells asegs _ (TH + 208 + 2560) [C8 ?a; C8 ?b; C8 ?c; C8 ?d], H1 : b1_ok ?e |- _ => exists a, b, c, d, e end.
    eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.

End Icpt.
