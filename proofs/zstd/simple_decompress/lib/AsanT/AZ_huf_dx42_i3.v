(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXSx KXSx2 KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globalsR AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_hufkit42 AZ_huf_dx42 AZ_huf_dx42_i4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
#[local] Ltac kx_sx3 ::= kx_rr_dedup; repeat kx_sx3_1.     (* [comment removed for export] *)
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
#[local] Ltac kxl_rd_exact ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : rw_cells segs m A _ |- _ => apply (kxl_rd_rw segs m A _ N H); reflexivity
      | H : ro_cells segs m A _ |- _ => apply (kxl_rd_ro segs m A _ N H); reflexivity
      | H : bytes_at segs m A ?bs, L : Z.of_nat (length ?bs) = N |- _ => rewrite <- L; exact (rd_at_bytes_at segs m A bs H)
      end
  end.
(* [comment removed for export] *)
#[local] Ltac kxl_lia ::= first [kxl_hyp | solve [kxl_lia_small] | kx_lia].
Tactic Notation "kx_autoFLA_v" constr(VMAX) constr(CH) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFLA_core (VMAX : Z) stops (FUEL : nat) true CH aks kzs rrs wws.
Lemma rwc_conv : forall sg mq A cs cs', rw_cells sg mq A cs' -> cs' = cs -> rw_cells sg mq A cs.
Proof. intros sg mq A cs cs' H E. subst cs. exact H. Qed.
Ltac cells_conv := lazymatch goal with |- rw_cells ?sg ?mq ?A _ =>
  match goal with H : rw_cells sg mq A _ |- _ =>
    eapply (rwc_conv sg mq A _ _ H);
    solve [ repeat first [ reflexivity | apply (f_equal2 (@cons cell)) | (apply (f_equal C8); apply (f_equal (Z_to_bv 64)); lia) ] ] end end.
Ltac hinv_enum hi :=
  lazymatch goal with
  | |- 0 <= _ /\ ((_ /\ 0 <= ?B <= 8) \/ _) =>
    lazymatch B with context [bv_unsigned (edenot ?E ?e)] =>
      let X := constr:(bv_unsigned (edenot E e)) in
      let f := lazymatch eval pattern X in B with ?f _ => f end in
      let BCE := fresh "BCE" in
      kx_read_ranges;
      lazymatch e with context [EVar ?j] =>
        kx_enum BCE E e j 1 255%nat (fun v => (0 <=? f v) && (f v <=? hi))%bool end;
      cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
    end
  end.
Ltac hinv3 :=
  first [ hinv_enum 8; split; [lia | left; split; [lia | split; lia]]
        | hinv_enum 64; split; [lia | right; split; [lia | split; lia]] ].
Ltac fix_s2 := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?X _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  lazymatch X with Z_to_bv 64 _ => idtac | _ => rewrite <- (Z_to_bv_bv_unsigned X) end end.

Section CANSEC1. Context {rc : runConstT}.
Section DX42BI.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x42b_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis ACTX : x42b_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 3136 [] m0 huf_noQ).
  Notation ST pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -576)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
             x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation FRS mm w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 :=
    (rw_cells bsegs mm (SPV + -408) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12;
                                     C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18]).
  Notation BD4 mm c b pad p st lm := (rw_cells bsegs mm (SPV + -256) [C8 c; C4 b; CB 4 pad; C8 p; C8 st; C8 lm]).
  Notation FRA mm j0 d j1 := (rw_cells bsegs mm (SPV + -576) [CB 40 j0; C8 d; CB 120 j1]).
  Notation FRJ mm j2 := (rw_cells bsegs mm (SPV + -216) [CB 112 j2]).
  Notation FRQ mm := (rw_cells bsegs mm (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation W0 := [(DST, DST + dcap); (SPV - 3136, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Hypothesis BITINIT : bit_init_stmtA.

  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333495296 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333497904 <= SPV) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 USRC UDT UDST RSRCS RDTS RDST RDSTS RSTK DSTA R1 R2 R3 LO SPB KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (AW0 : aappW [(SPV - 2608, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]);
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact UDT | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R3; lia | clear - R3; lia | clear - R3; lia]
          | eapply unp_carryW; [exact UDT | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R3; lia | clear - R3; lia | clear - R3; lia] ]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 400) 400) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  (* [comment removed for export] *)
  Ltac dfacts MU0 UDST RDST RDSTS DSTA AW0 R1 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryW; [exact (UDST D) | exact MU0 | apply aappW_cons_D; [exact DSTA | exact D | exact AW0] | clear - R1; lia | clear - R1 D; lia | clear - R1; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  (* [comment removed for export] *)
  Ltac sfacts0 MU0 USRC DSTA AW0 R1 R2 :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (destruct (Z_lt_le_dec 0 dcap) as [Hd|Hd];
          [ eapply unp_carryW; [exact USRC | exact MU0 | apply aappW_cons_D; [exact DSTA | exact Hd | exact AW0] | clear - R2; lia | clear - R2 N; lia | clear - R2; lia]
          | eapply unp_carryW; [exact USRC | eapply munch_drop_empty; replace (DST + dcap) with DST in MU0 by (clear - Hd R1; lia); exact MU0
                               | exact AW0 | clear - R2; lia | clear - R2 N; lia | clear - R2; lia] ]);
    clear N.
  Ltac sfacts BSS BSE LEN1 R2 DJ1 OS2 LO RSRC RSRCS USRCc :=
    lazymatch type of BSE with ?S + ?len <= SRC + n =>
      assert (SF : (4096 <= S <= 140737488355328) /\ (4096 <= S + len <= 140737488355328) /\ (1 <= len <= 4294967296) /\ S + len < 2^47 /\
                   (DST + dcap <= S \/ S + len <= DST) /\ (S + len <= lo \/ SPV <= S) /\
                   (SPV - 264 + 160 <= S \/ S + len <= SPV - 264) /\ (SPV - 400 + 136 <= S \/ S + len <= SPV - 400))
        by (clear - BSS BSE LEN1 R2 DJ1 OS2 LO; lia);
      destruct SF as (S0 & S1 & SL32 & S2 & DJS & DJK & DJB & DJFr);
      assert (RS : rng RNG S len) by (eapply rng_sub; [exact RSRC | clear - BSS; lia | clear - BSE LEN1; lia]);
      pose proof (rng_shspanZ_sub RNG SRC n S len RSRCS BSS ltac:(clear - LEN1; lia) BSE ltac:(clear - R2; lia)) as RSz;
      lazymatch type of USRCc with unpoisoned ?mm _ _ =>
        pose proof (unpoisoned_unpZ mm _ _ S (S + len) USRCc BSS BSE ltac:(unfold KXKEND; clear - BSE R2; lia)) as USz
      end
    end.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 400 \/ SPV - 400 + 136 <= DST) /\ (DST + dcap <= SPV - 264 \/ SPV - 264 + 160 <= DST) /\
                 (SPV - 264 + 160 <= DT \/ DT + 16388 <= SPV - 264) /\ (SPV - 400 + 136 <= DT \/ DT + 16388 <= SPV - 400) /\
                 (DST + dcap <= SPV - 400 \/ SPV - 400 + 400 <= DST))
      by (clear - OS1 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3 & DJF4 & DJF5).
  (* [comment removed for export] *)
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < dcap -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < dcap -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : aro_client RNG m0 |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : Z.of_nat (length src) = n |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac evr := (repeat match goal with H : 0 <= bv_unsigned (ev _ _) <= _ |- _ => clear H end); kx_ev_ranges.
  (* [comment removed for export] *)
  Ltac lside := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- SINVA _ _ _ => first [assumption | unfold SINVA in *; lia]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- @eq word _ _ => first [eassumption | reflexivity | idtac]
    | |- _ /\ _ => first [lia | kx_lia | idtac]
    | |- _ \/ _ => try lia
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => eassumption
    end.
  Notation x42_reta0 := (AZ_huf_dx42.x42_reta0 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Notation HINV o len b := (0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64))).
  Hypothesis KM : forall (dl pe1 pe2 pe3 S1 n1 S2 n2 S3 n3 S4 n4 : Z) (bs1 bs2 bs3 bs4 : list byte) (mb : amem)
      (o1 b1 o2 b2 o3 b3 o4 b4 : Z) (k1 k2 k3 k4 : word) (pad4 j0 j1 j2 : list byte)
      (w0 w8 w9 w10 w11 w12 w13 w14 w16 w18 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x29 x30 x31 : word),
    dl = tl + 256 * rsv -> pe1 = (dcap + 3) / 4 -> pe2 = 2 * pe1 -> pe3 = 3 * pe1 -> pe3 <= dcap ->
    zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 ->
    zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 1 <= n3 ->
    zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 1 <= n4 ->
    S1 = SRC + 6 -> S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 -> S4 + n4 = SRC + n ->
    FRQ mb -> munch W0 m0 mb -> wmono bsegs m0 mb -> mem_inv bsegs mb -> stk bsegs mb DST (DST + dcap) ->
    bytes_at bsegs mb DT dtb -> stk bsegs mb lo (SPV + -576) ->
    FRA mb j0 (Z_to_bv 64 dcap) j1 ->
    FRS mb w0 (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (DST + pe1)) (Z_to_bv 64 S2) (Z_to_bv 64 (DST + pe3)) (Z_to_bv 64 S1)
        (Z_to_bv 64 (DST + pe2)) (Z_to_bv 64 S3) w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 (S3 + o3)) w16 k1 w18 ->
    BD4 mb k4 (Z_to_bv 64 b4) pad4 (Z_to_bv 64 (S4 + o4)) (Z_to_bv 64 S4) (Z_to_bv 64 (S4 + 8)) -> FRJ mb j2 ->
    bytes_at bsegs mb S1 bs1 -> bytes_at bsegs mb S2 bs2 -> bytes_at bsegs mb S3 bs3 -> bytes_at bsegs mb S4 bs4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 -> HINV o3 n3 b3 -> HINV o4 n4 b4 ->
    evtF bsegs RNG POST (ST 0x9e6cc mb x1 x5 x6 x7 (Z_to_bv 64 dl) (Z_to_bv 64 b1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (DST + dcap)) x17
                            (Z_to_bv 64 b3) k3 (Z_to_bv 64 SRC) (Z_to_bv 64 b2) (Z_to_bv 64 (S2 + o2)) k2 (Z_to_bv 64 DST) (Z_to_bv 64 DT)
                            (Z_to_bv 64 (S1 + o1)) SB (Z_to_bv 64 (DST + pe3)) x29 x30 x31).
  Notation EINVB := (AZ_huf_dx42.EINVB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap lo).
  Notation x42_einvS := (AZ_huf_dx42_i4.x42_einvS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX).
  Notation x42_i4 := (AZ_huf_dx42_i4.x42_i4 RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX BITINIT KM).
  (* [comment removed for export] *)
  Ltac tostk A := match goal with H : rw_cells bsegs ?m2 A ?cs |- _ =>
    let S := fresh "SK" in pose proof (stk_of_rw_cells bsegs m2 A cs H) as S; cbn [cells_size csize Nat.add] in S; exact S end.
  (* [comment removed for export] *)
  Ltac err_ret SV1 HER HRB := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x42_reta0 m2 _);
    [ eapply (x42_einvS m2);
      [ exact SV1 | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ]
    | right; split; [exact HER | exact HRB] ] end.
  Ltac fix_a1 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  Ltac fix_a2 E := lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => first [constr_eq X E | replace X with E by lia] end.
  (* [comment removed for export] *)
  Ltac hold_ors := repeat match goal with H : _ \/ _ |- _ => apply iheld_intro in H end.
  Ltac unhold_ors := repeat match goal with H : iheld _ |- _ => unfold iheld in H end.
  Notation x42_err := (AZ_huf_dx42.x42_err RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX ACTX).
  Ltac ret_a0 := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    try (replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv64_eqm_k; reflexivity));
    eapply (x42_reta0 m2 _);
    [ eapply (x42_einvS m2);
      [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
      | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ]
    | right; split; [vm_compute; reflexivity | lia] ] end.
  Ltac ret_err := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
    eapply (x42_err m2); eapply (x42_einvS m2);
    [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | tostk (SPV + -576) | tostk (SPV + -408) | tostk (SPV + -256) | tostk (SPV + -216) ] end.

  (* [comment removed for export] *)
  Ltac lsideI HN1 HB1 HB2 NK := lazymatch goal with
    | |- evtF _ _ _ _ => idtac
    | |- forall _, _ => idtac
    | |- HINV _ _ _ => first [ assumption | unfold bitd_ptr; clear - HN1 HB1 HB2; destruct (Z.leb_spec 8 NK); lia ]
    | |- @eq Z _ _ => first [eassumption | reflexivity | lia]
    | |- Z_to_bv _ _ = Z_to_bv _ _ => first [reflexivity | f_equal; lia]
    | |- _ /\ _ => first [lia | idtac]
    | |- Z.le _ _ => lia
    | |- Z.lt _ _ => lia
    | |- _ => first [eassumption | lia | idtac]
    end.

  (* [comment removed for export] *)
  Lemma x42_i3 : forall mm e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 b2 o2 S3 n3 bs3 S4 n4 bs4 (c1 c2 : word) j0 j1 j2 junk4
      (x5 x6 x10 x14 x15 x16 x18 x19 x21 x29 x30 : word)
      (w0 w1 w4 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18 : word),
    FRQ mm -> munch W0 m0 mm -> wmono bsegs m0 mm -> mem_inv bsegs mm -> stk bsegs mm DST (DST + dcap) -> bytes_at bsegs mm DT dtb ->
    stk bsegs mm lo (SPV + -576) ->
    FRA mm j0 (Z_to_bv 64 dcap) j1 ->
    FRS mm w0 w1 (Z_to_bv 64 (DST + e1)) (Z_to_bv 64 S2) w4 (Z_to_bv 64 S1)
        (Z_to_bv 64 (DST + 2 * e1)) w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 c1 w18 ->
    rw_cells bsegs mm (SPV + -256) [CB 40 junk4] -> FRJ mm j2 ->
    bytes_at bsegs mm S1 bs1 -> zlen bs1 = n1 -> SRC <= S1 -> S1 + n1 <= SRC + n -> 1 <= n1 ->
    bytes_at bsegs mm S2 bs2 -> zlen bs2 = n2 -> SRC <= S2 -> S2 + n2 <= SRC + n -> 1 <= n2 ->
    bytes_at bsegs mm S3 bs3 -> zlen bs3 = n3 -> SRC <= S3 -> S3 + n3 <= SRC + n -> 0 <= n3 ->
    bytes_at bsegs mm S4 bs4 -> zlen bs4 = n4 -> SRC <= S4 -> S4 + n4 <= SRC + n -> 0 <= n4 ->
    HINV o1 n1 b1 -> HINV o2 n2 b2 ->
    0 <= e1 -> 3 * e1 <= dcap -> e1 = (dcap + 3) / 4 -> dl = tl + 256 * rsv -> S1 = SRC + 6 -> S2 = S1 + n1 -> S3 = S2 + n2 -> S4 = S3 + n3 -> tot = 6 + n1 + n2 + n3 -> n4 = n - tot ->
    evtF bsegs RNG POST (ST 0x9e370 mm (Z_to_bv 64 n) x5 x6 (Z_to_bv 64 S3) (Z_to_bv 64 dl) (Z_to_bv 64 b1) x10 (Z_to_bv 64 18446744073709551544) (Z_to_bv 64 tot) (Z_to_bv 64 n3) x14 x15 x16 (Z_to_bv 64 b2)
                            x18 x19 (Z_to_bv 64 (DST + dcap)) x21 (Z_to_bv 64 (S2 + o2)) c2 (Z_to_bv 64 DST) (Z_to_bv 64 DT)
                            (Z_to_bv 64 (S1 + o1)) SB (Z_to_bv 64 (DST + 3 * e1)) x29 x30 (Z_to_bv 64 SRC)).
  Proof using CTX ACTX BITINIT KM rc.
    pose proof CTX as CTX'. x42b_ctx_open CTX'. pose proof ACTX as ACTX'. x42b_actx_open ACTX'.
    intros mm e1 tot dl S1 n1 bs1 b1 o1 S2 n2 bs2 b2 o2 S3 n3 bs3 S4 n4 bs4 c1 c2 j0 j1 j2 junk4
      x5 x6 x10 x14 x15 x16 x18 x19 x21 x29 x30
      w0 w1 w4 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w18
      SV MU0 WM0 MI OUT DTB STK FA FR BJ4 FJ SB1 BL1 SS1 SE1 LN1 SB2 BL2 SS2 SE2 LN2 SB3 BL3 SS3 SE3 LN3 SB4 BL4 SS4 SE4 LN4 HI1 HI2 HE1 HE3 HE HDL HS1 HS2 HS3 HS4 HTOT HN4.
    facts R1 R2 R3 TL RSV LO SPB KLO.
    assert (RFR : rng RNG (SPV - 576) 576) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
    assert (KF : (0 <= n4 <= 4294967296) /\ (4096 <= S4 <= 140737488355328) /\ (0 <= tot <= 4294967296) /\ (4096 <= S3 <= 140737488355328) /\ (0 <= n3 <= 4294967296)
                 /\ (4096 <= S2 <= 140737488355328) /\ (0 <= n2 <= 4294967296) /\ (4096 <= S1 <= 140737488355328) /\ (0 <= n1 <= 4294967296))
      by (clear - R2 SS1 SE1 LN1 SS2 SE2 LN2 SS3 SE3 LN3 SS4 SE4 LN4 HTOT HN4; lia).
    pose proof KF as KF'; destruct KF' as (KF1 & KF2 & KF3 & KF4 & KF5 & KF6 & KF7 & KF8 & KF9).
    (* [comment removed for export] *)
    assert (AW0 : aappW [(SPV - 3136, SPV)]) by (apply aappW_cons_hi; [clear - LO KLO; lia | apply aappW_nil]).
    sfacts0 MU0 USRC DSTA AW0 R1 R2.
    assert (HN3 : n3 = 0 \/ n3 = 1 \/ n3 = 2 \/ n3 = 3 \/ n3 = 4 \/ n3 = 5 \/ n3 = 6 \/ n3 = 7 \/ 8 <= n3) by lia.
    destruct HN3 as [N3|[N3|[N3|[N3|[N3|[N3|[N3|[N3|N3]]]]]]]].
    9: kx_autoFLA tt [KAUnp SRC n; KAUnp S3 n3] [0x9e6a8; 0x9fd60; 0x9fd5c] 260%nat
         [KZRange n3 8 (2^32); KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange SPV 4096 (2^47);
          KZDisj (SPV - 576) 576 S3 n3]
         [(S3, n3)] [(SPV - 576, 576)].
    2-8: rewrite N3; lazymatch type of N3 with _ = ?k =>
           kx_autoFLA_v 8 tt [KAUnp SRC n; KAUnp S3 n3] [0x9e6a8; 0x9fd60; 0x9fd5c] 260%nat
             [KZRange n3 k k; KZRange S3 4096 (2^47); KZRange (S3 + n3) 4096 (2^47); KZRange SPV 4096 (2^47);
              KZDisj (SPV - 576) 576 S3 n3; KZImg 0x223e8 0x22400]
             [(S3, n3)] [(SPV - 576, 576)] end.
    1: rewrite N3; kx_autoFLA tt (@nil kza) [0x9fd60] 12%nat [KZRange SPV 4096 (2^47)] (@nil (Z * Z)) [(SPV - 576, 576)].
    all: aside.
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCStoreOk _ _) => kx_wr FR end).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd USRCc end).
    all: try (lazymatch goal with |- accP _ _ _ => first [kx_acc RSRC | kx_sh_acc RSRCS] end).
    all: try (lazymatch goal with |- evtF _ _ _ _ => kx_sh_dead USRCc 8 end).
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9e6a8) _ _ _ _) =>
             kx_gen_regsF [5%nat; 6%nat; 7%nat; 10%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 19%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd60) _ _ _ _) =>
             kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat;
                           21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd5c) _ _ _ _) =>
             kx_gen_regsF [1%nat; 5%nat; 6%nat; 7%nat; 8%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat;
                           21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat]
         end.
    all: intros; kx_mem.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd60) _ _ _ _) => ret_a0
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9fd5c) _ _ _ _) => ret_err
         | |- _ => idtac
         end.
    (* [comment removed for export] *)
    all: fix_a1 S4. all: fix_s2.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | _ : ?ptot = 6 + ?pn1 + ?pn2 + ?k, _ : ?pe1 = (dcap + 3) / 4, _ : ?pdl = tl + 256 * rsv,
           _ : ?pS1 = SRC + 6, _ : ?pS2 = ?pS1 + ?pn1, _ : ?pS3 = ?pS2 + ?pn2, _ : ?pS4 = ?pS3 + ?k, _ : ?pn4 = n - ?ptot,
           _ : bytes_at _ _ ?pS1 ?pbs1, _ : bytes_at _ _ ?pS2 ?pbs2, _ : bytes_at _ _ ?pS3 ?pbs3, _ : bytes_at _ _ ?pS4 ?pbs4,
           _ : HINV ?po1 ?pn1 ?pb1, _ : HINV ?po2 ?pn2 ?pb2,
           _ : FRA _ ?pj0 _ ?pj1, _ : FRJ _ ?pj2, _ : rw_cells _ _ (SPV + -256) [CB 40 ?pjk],
           _ : FRS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc1 _
           |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) =>
         tryif (match goal with K8 : 8 <= k |- _ => idtac end)
         then (eapply (x42_i4 m2 pe1 ptot pdl pS1 pn1 pbs1 pb1 po1 pS2 pn2 pbs2 pb2 po2 pS3 k pbs3 _ (k - 8) pS4 pn4 pbs4 pc1 _ _ pj0 pj1 pj2 pjk);
               first [ eassumption | cells_conv | hinv3 | lia ])
         else (eapply (x42_i4 m2 pe1 ptot pdl pS1 pn1 pbs1 pb1 po1 pS2 pn2 pbs2 pb2 po2 pS3 k pbs3 _ 0 pS4 pn4 pbs4 pc1 _ _ pj0 pj1 pj2 pjk);
               first [ eassumption | cells_conv | hinv3 | lia ])
         end.
  Qed.
End DX42BI.
End CANSEC1.
