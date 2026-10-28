(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_dx1 AZ_huf_dx2 AZ_huf_dx2b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
#[local] Ltac kx_lia ::= kx_lia_fast.
#[local] Ltac kx_path_hyp E zs nz KXA BR ::= kx_rr_dedup; kx_path_hyp_fast E zs nz KXA BR.
Ltac kxa_norm ::= unfold shspan in *.


Section CANSEC1. Context {rc : runConstT}.
Section DX2L4.
  Variables (RNG : footprint).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (SPV DST dcap SRC n DT tl rsv lo : Z) (src dtb : list byte).
  Hypothesis CTX : x1_ctx SPV DST dcap SRC n DT tl rsv lo src dtb.
  Hypothesis X2OK : huf_x2_ok dtb tl.
  Hypothesis ACTX : x1_actx RNG m0 SPV DST dcap SRC n DT lo.

  Notation POST := (huf_dec_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 2352 [] m0 huf_noQ).
  Notation W0 := [(DST, DST + dcap); (SPV - 2352, SPV)].
  Notation SB := (Z_to_bv 64 0x7fff8000).
  Notation DINV2 := (dinv2 ra s0 s1 s2 s3 s4 s5 m0 SPV DST dcap SRC DT lo src dtb).
  Notation PINV := (pinv2 SRC n).

  Ltac dinv_open DI :=
    let OUT := fresh "OUT" in let g := fresh "g" in
    destruct DI as (OUT & FR & [g GAP] & STK & SRCB & DTB & MU & WM & MI).
  Ltac dinv_close := unfold dinv2; repeat (split; [first [eassumption | eexists; eassumption]|]); eassumption.
  (* [comment removed for export] *)
  Ltac facts R1 R2 R3 TL RSV LO SPB KLO :=
    assert (GF : (4096 <= DST <= 140737488355328) /\ (0 <= dcap <= 4294967296) /\ (4096 <= DT <= 140737488338940) /\
                 (4096 <= SRC <= 140737488355328) /\ (4096 <= SRC + n <= 140737488355328) /\ (0 <= n <= 4294967296) /\
                 (17594333497648 <= SPV <= 140737488355328) /\ (1 <= tl <= 12) /\ (0 <= rsv <= 255) /\
                 (1 <= tl + 256 * rsv <= 65535) /\ (52 <= 64 - tl <= 63) /\ (17594333495296 <= SPV - 2352) /\ (4096 <= DT + 4 <= 140737488338944))
      by (clear - R1 R2 R3 TL RSV LO SPB KLO; lia);
    destruct GF as (GF1 & GF2 & GF3 & GF4 & GF5 & GF6 & GF7 & GF8 & GF9 & GF10 & GF11 & GF12 & GF13).
  (* [comment removed for export] *)
  Ltac afacts MU0 UDT RDTS RSTK DSTA R3 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    assert (UDTc : unpoisoned mm DT (DT + 16388))
      by (eapply unp_carryS; [exact UDT | exact MU0 | clear - R3; lia | clear - R3; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (rng_shspanZ _ _ _ RDTS) as RDTz;
    pose proof (unpoisoned_unpZ _ _ _ DT (DT + 16388) UDTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R3; lia)) as UDTz;
    assert (RFR : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | clear - LO; lia | clear - LO; lia]).
  Ltac dfacts MU0 UDST RDST RDSTS DSTA R1 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let D := fresh "DPOS" in
    assert (D : 0 < dcap) by lia;
    assert (UDSTc : unpoisoned mm DST (DST + dcap))
      by (eapply unp_carryS; [exact (UDST D) | exact MU0 | clear - R1; lia | clear - R1; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RDST D) as RDSTc; pose proof (RDSTS D) as RDSTSc;
    assert (DSTAc : DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST) by (clear - D DSTA; lia);
    pose proof (rng_shspanZ _ _ _ RDSTSc) as RDSTz;
    pose proof (unpoisoned_unpZ _ _ _ DST (DST + dcap) UDSTc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R1; lia)) as UDSTz;
    clear D.
  Ltac sfacts MU0 USRC RSRC RSRCS DSTA R1 R2 LO KLO :=
    let mm := lazymatch type of MU0 with munch _ _ ?mm => mm end in
    let N := fresh "NPOS" in
    assert (N : 0 < n) by lia;
    assert (USRCc : unpoisoned mm SRC (SRC + n))
      by (eapply unp_carryS; [exact (USRC N) | exact MU0 | clear - R2; lia | clear - R2; lia | clear - DSTA; lia | clear - LO KLO; lia]);
    pose proof (RSRC N) as RSRCc; pose proof (RSRCS N) as RSRCSc;
    pose proof (rng_shspanZ _ _ _ RSRCSc) as RSRCz;
    pose proof (unpoisoned_unpZ _ _ _ SRC (SRC + n) USRCc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; clear - R2 N; lia)) as USRCz;
    clear N.
  (* [comment removed for export] *)
  Ltac ffacts OS1 OS2 OS3 LO :=
    assert (FF : (DST + dcap <= SPV - 64 \/ SPV - 64 + 64 <= DST) /\ (SPV - 64 + 64 <= DT \/ DT + 16388 <= SPV - 64) /\
                 (SPV - 64 + 64 <= SRC \/ SRC + n <= SPV - 64))
      by (clear - OS1 OS2 OS3 LO; lia);
    destruct FF as (DJF1 & DJF2 & DJF3).
  Ltac kclean :=
    repeat match goal with
           | H : SPV mod 16 = 0 |- _ => clear H
           | H : DT mod 4 = 0 |- _ => clear H
           | H : unpoisoned m0 _ _ |- _ => clear H
           | H : 0 < _ -> unpoisoned m0 _ _ |- _ => clear H
           | H : rng RNG (shad _) _ |- _ => clear H
           | H : 0 < _ -> rng RNG (shad _) _ |- _ => clear H
           | H : azstk RNG m0 _ _ |- _ => clear H
           | H : art m0 |- _ => clear H
           | H : nth_error dtb _ = _ |- _ => clear H
           | H : dcap <= 0 \/ _ |- _ => clear H
           | H : SPV < 2^47 |- _ => clear H
           | H : 0x10007fff8000 <= lo |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac len_range :=
    match goal with
    | |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (DST + (_ + bv_unsigned (ev ?E ?k)))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        let H := fresh "LENR" in kx_erange H (EVar k); cbn [edenot] in H
    | |- _ => idtac
    end.
  Ltac aside := try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end.
  (* [comment removed for export] *)
  Ltac x2_open DI :=
    let CTX' := fresh "CTX'" in let ACTX' := fresh "ACTX'" in let DI' := fresh "DI'" in
    pose proof CTX as CTX'; x1_ctx_open CTX'; pose proof ACTX as ACTX'; x1_actx_open ACTX';
    pose proof DI as DI'; dinv_open DI';
    lazymatch goal with
    | R1 : 4096 <= DST /\ _, R2 : 4096 <= SRC /\ _, R3 : 4096 <= DT /\ _, TL : 1 <= tl <= 12, RSV : 0 <= rsv <= 255,
      LO : 4096 <= lo /\ _, SPB : SPV < 2^47, KLO : 0x10007fff8000 <= lo, UDT : unpoisoned m0 DT _, RDTS : rng RNG (shad DT) _,
      RSTK : rng RNG lo _, DSTA : dcap <= 0 \/ _, OS1 : DST + dcap <= lo \/ _, OS2 : SRC + n <= lo \/ _, OS3 : DT + 16388 <= lo \/ _,
      MU : munch _ m0 _ |- _ =>
        facts R1 R2 R3 TL RSV LO SPB KLO; afacts MU UDT RDTS RSTK DSTA R3 LO KLO; ffacts OS1 OS2 OS3 LO
    end.
  Ltac x2_dst :=
    lazymatch goal with UDST : 0 < dcap -> unpoisoned m0 DST _, RDST : 0 < dcap -> rng RNG DST _, RDSTS : 0 < dcap -> rng RNG (shad DST) _,
                        DSTA : dcap <= 0 \/ _, MU : munch _ m0 _, R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ _, LO : 4096 <= lo /\ _,
                        KLO : 0x10007fff8000 <= lo |- _ =>
      dfacts MU UDST RDST RDSTS DSTA R1 LO KLO end.     (* [comment removed for export] *)
  Ltac x2_src :=
    lazymatch goal with USRC : 0 < n -> unpoisoned m0 SRC _, RSRC : 0 < n -> rng RNG SRC _, RSRCS : 0 < n -> rng RNG (shad SRC) _,
                        DSTA : dcap <= 0 \/ _, MU : munch _ m0 _, R1 : 4096 <= DST /\ 0 <= dcap < 2^32 /\ _, R2 : 4096 <= SRC /\ 0 <= n < 2^32 /\ _,
                        LO : 4096 <= lo /\ _, KLO : 0x10007fff8000 <= lo |- _ =>
      sfacts MU USRC RSRC RSRCS DSTA R1 R2 LO KLO end.

  (* [comment removed for export] *)
  Notation ST pc mm x1 x7 x8 x9 x10 x13 x14 x15 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp (Z_to_bv 64 (tl + 256 * rsv)) (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10
             (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) x13 x14 x15 (Z_to_bv 64 (DT + 4)) SB
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Notation ST0 pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation x2_tbl := (AZ_huf_dx2.x2_tbl RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).
  Notation x2_fcc := (AZ_huf_dx2b.x2_fcc RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SPV DST dcap SRC n DT tl rsv lo src dtb CTX X2OK ACTX).

  (* [comment removed for export] *)
  Notation MST4 pc mm x1 j bc pm9 sh idx pt cont x9 x14 x18 x19 x20 x21 :=
    (ST pc mm x1 cont (Z_to_bv 64 64) x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DT + 4 * idx + 4)) x14 (Z_to_bv 64 sh)
        x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) (Z_to_bv 64 pm9) (Z_to_bv 64 8)).
  (* [comment removed for export] *)
  Notation LST4 pc mm x1 j bc pm9 sh pt cont x9 x13 x14 x18 x19 x20 x21 :=
    (ST pc mm x1 cont (Z_to_bv 64 64) x9 (Z_to_bv 64 (DST + j)) x13 x14 (Z_to_bv 64 sh)
        x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) (Z_to_bv 64 pm9) (Z_to_bv 64 8)).
  (* [comment removed for export] *)
  Notation HEADK4 jb := (forall mm' j' bc' pm9' sh' pt' (cont' : word) (x1' x9' x13' x14' x18' x19' x20' x21' : word),
    DINV2 mm' -> jb < j' <= dcap ->
    pm9' = DST + dcap - 7 -> sh' = 64 - tl -> 0 <= bc' <= 64 -> PINV (SRC + pt') ->
    evtF bsegs RNG POST (LST4 0x9a374 mm' x1' j' bc' pm9' sh' pt' cont' x9' x13' x14' x18' x19' x20' x21')).

  (* [comment removed for export] *)
  Lemma x2_4lenword : forall mm idx, bytes_at bsegs mm DT dtb -> zlen dtb = 16388 -> huf_x2_ok dtb tl -> 1 <= tl <= 12 ->
    0 <= idx < 2 ^ tl ->
    exists lv, 1 <= lv <= 2 /\ rdn bsegs mm (wa (DT + 4 * idx + 7)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 lv)).
  Proof.
    intros mm idx DTB DL X2 TL HI. destruct (X2 idx HI) as (b & NTH & BR).
    exists (bv_unsigned b). split; [exact BR|].
    assert (L : (Z.to_nat (4 * idx + 7) + 1 <= length dtb)%nat).
    { assert (Z.to_nat (4 * idx + 7) < length dtb)%nat by (apply nth_error_Some; rewrite NTH; discriminate). lia. }
    pose proof (bytes_at_rdn bsegs mm DT dtb (Z.to_nat (4 * idx + 7)) 1 DTB L) as R.
    rewrite Z2Nat.id in R by lia. replace (DT + 4 * idx + 7) with (DT + (4 * idx + 7)) by lia. rewrite R.
    rewrite (firstn1_skipn _ _ _ NTH). unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal.
    symmetry. apply bv_eq. rewrite Z_to_bv_unsigned.
    pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in RB.
    rewrite Z_to_bv_unsigned. rewrite !bv_wrap_small; [reflexivity| |]; unfold bv_modulus.
    - change (2 ^ Z.of_N 64) with (2^64). lia.
    - change (2 ^ Z.of_N 8) with 256. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_4idx_lt : forall (w : word) e, e = 64 - tl -> 1 <= tl <= 12 -> 0 <= bv_unsigned w / 2 ^ e < 2 ^ tl.
  Proof.
    intros w e -> TL. pose proof (bv_unsigned_in_range 64 w) as HX. unfold bv_modulus in HX. change (2 ^ Z.of_N 64) with (2^64) in HX.
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac x2_to_mid NEXT HN HK HSH HP :=
    eapply NEXT;
    [ dinv_close | exact HN | exact HK | lia | lia | lia | reflexivity | exact HSH | lia
    | lazymatch goal with TL : 1 <= tl <= 12 |- _ =>
        apply x2_4idx_lt; [rewrite HSH; repeat (rewrite Z.mod_small by lia); reflexivity | exact TL] end
    | exact HP ].
  Ltac x2_bc64 :=
    first [ lia
          | lazymatch goal with |- 0 <= bv_unsigned ?w <= 64 =>
              split; [exact (proj1 (bv_unsigned_in_range 64 w)) | assumption] end ].

  (* [comment removed for export] *)
  Lemma x2_4m4 : forall jb mm j bc pm9 sh idx pt (cont : word) (x1 x9 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> HEADK4 jb -> jb <= j -> 0 <= j -> 2 <= dcap - j ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> 0 <= bc <= 1000 -> 0 <= idx < 2^tl -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (MST4 0x9a60c mm x1 j bc pm9 sh idx pt cont x9 x14 x18 x19 x20 x21).
  Proof using All.
    intros jb mm j bc pm9 sh idx pt cont x1 x9 x14 x18 x19 x20 x21 DI HN HK HJB HJ ROOM HPM HSH HB HI HP.
    x2_open DI. x2_dst. subst pm9.
    lazymatch goal with TL : 1 <= tl <= 12, DTB : bytes_at bsegs mm DT dtb, DL : zlen dtb = 16388 |- _ =>
      assert (P2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia);
      assert (HI4 : 0 <= idx <= 4095) by (clear - HI P2; lia);
      destruct (x2_4lenword mm idx DTB DL X2OK TL HI) as (lv & LV & LW) end.
    assert (RJ : 2 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355326 /\ 52 <= sh <= 63)
      by (clear - HJ ROOM R1 HSH GF8; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4). kclean.
    Time kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9a374; 0x9a824] 90%nat
      [KZRange (dcap - j) 2 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355326;
       KZRange idx 0 4095; KZRange bc 0 1000; KZRange lv 1 2; KZWord (DT + 4 * idx + 7) 1 lv;
       KZRange SPV 17594333497648 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
       KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
       KZDisj DST dcap SRC n]
      [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)].
    all: aside.
    all: kx_gen_regsF [9%nat; 14%nat; 18%nat; 19%nat]; intros.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a374) _ _ _ _) =>
             eapply HK; [dinv_close | lia | reflexivity | exact HSH | x2_bc64 | exact HP]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9a824) _ _ _ _) =>
             eapply x2_fcc; [dinv_close | exact HN | lia | lia | intros; exfalso; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_4m3 : forall jb mm j bc pm9 sh idx pt (cont : word) (x1 x9 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> HEADK4 jb -> jb <= j -> 0 <= j -> 4 <= dcap - j ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> 0 <= bc <= 700 -> 0 <= idx < 2^tl -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (MST4 0x9a580 mm x1 j bc pm9 sh idx pt cont x9 x14 x18 x19 x20 x21).
  Proof using All.
    intros jb mm j bc pm9 sh idx pt cont x1 x9 x14 x18 x19 x20 x21 DI HN HK HJB HJ ROOM HPM HSH HB HI HP.
    x2_open DI. x2_dst. subst pm9.
    lazymatch goal with TL : 1 <= tl <= 12, DTB : bytes_at bsegs mm DT dtb, DL : zlen dtb = 16388 |- _ =>
      assert (P2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia);
      assert (HI4 : 0 <= idx <= 4095) by (clear - HI P2; lia);
      destruct (x2_4lenword mm idx DTB DL X2OK TL HI) as (lv & LV & LW) end.
    assert (RJ : 4 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355324 /\ 52 <= sh <= 63)
      by (clear - HJ ROOM R1 HSH GF8; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4). kclean.
    Time kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9a60c] 90%nat
      [KZRange (dcap - j) 4 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355324;
       KZRange idx 0 4095; KZRange bc 0 700; KZRange lv 1 2; KZWord (DT + 4 * idx + 7) 1 lv;
       KZRange SPV 17594333497648 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
       KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
       KZDisj DST dcap SRC n]
      [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)].
    all: aside.
    all: kx_gen_regsF [9%nat; 14%nat; 18%nat; 19%nat]; intros.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: x2_to_mid x2_4m4 HN HK HSH HP.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_4m2 : forall jb mm j bc pm9 sh idx pt (cont : word) (x1 x9 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> HEADK4 jb -> jb <= j -> 0 <= j -> 6 <= dcap - j ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> 0 <= bc <= 400 -> 0 <= idx < 2^tl -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (MST4 0x9a4f4 mm x1 j bc pm9 sh idx pt cont x9 x14 x18 x19 x20 x21).
  Proof using All.
    intros jb mm j bc pm9 sh idx pt cont x1 x9 x14 x18 x19 x20 x21 DI HN HK HJB HJ ROOM HPM HSH HB HI HP.
    x2_open DI. x2_dst. subst pm9.
    lazymatch goal with TL : 1 <= tl <= 12, DTB : bytes_at bsegs mm DT dtb, DL : zlen dtb = 16388 |- _ =>
      assert (P2 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia);
      assert (HI4 : 0 <= idx <= 4095) by (clear - HI P2; lia);
      destruct (x2_4lenword mm idx DTB DL X2OK TL HI) as (lv & LV & LW) end.
    assert (RJ : 6 <= dcap - j <= 4294967296 /\ 0 <= j <= 4294967296 /\ 4096 <= DST + j <= 140737488355322 /\ 52 <= sh <= 63)
      by (clear - HJ ROOM R1 HSH GF8; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4). kclean.
    Time kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9a580] 90%nat
      [KZRange (dcap - j) 6 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355322;
       KZRange idx 0 4095; KZRange bc 0 400; KZRange lv 1 2; KZWord (DT + 4 * idx + 7) 1 lv;
       KZRange SPV 17594333497648 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
       KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
       KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
       KZDisj DST dcap SRC n]
      [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)].
    all: aside.
    all: kx_gen_regsF [9%nat; 14%nat; 18%nat; 19%nat]; intros.
    all: kx_ev_ranges; kx_mem; kx_strip_mod.
    all: x2_to_mid x2_4m3 HN HK HSH HP.
  Qed.

  (* [comment removed for export] *)
  Notation B1ST mm x1 j bc pm9 sh P pt fl x9 x14 x18 x19 x20 x21 :=
    (ST 0x9a430 mm x1 (Z_to_bv 64 fl) (Z_to_bv 64 64) x9 (Z_to_bv 64 (DST + j)) (Z_to_bv 64 P) x14 (Z_to_bv 64 sh)
        x18 x19 x20 x21 (Z_to_bv 64 pt) (Z_to_bv 64 bc) (Z_to_bv 64 pm9) (Z_to_bv 64 8)).

  (* [comment removed for export] *)
  Lemma x2_4b1 : forall jb mm j bc pm9 sh P pt fl (x1 x9 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> HEADK4 jb -> jb <= j -> 0 <= j <= dcap ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> P = SRC + pt -> (fl = 0 \/ fl = 1) -> 0 <= bc <= 64 -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (B1ST mm x1 j bc pm9 sh P pt fl x9 x14 x18 x19 x20 x21).
  Proof using All.
    intros jb mm j bc pm9 sh P pt fl x1 x9 x14 x18 x19 x20 x21 DI HN HK HJB HJ HPM HSH HPP HFL HB HP.
    x2_open DI. subst pm9 P.
    assert (RJ : 0 <= j <= 4294967296 /\ 52 <= sh <= 63 /\ 0 <= bc <= 64) by (clear - HJ R1 HSH GF8 HB; lia). destruct RJ as (RJ1 & RJ2 & RJ3).
    destruct (Z_lt_le_dec (dcap - j) 8) as [SM|BG].
    - (* [comment removed for export] *)
      clear HK. kclean.
      assert (RJ4 : 0 <= dcap - j <= 7) by (clear - HJ SM; lia).
      destruct HFL as [-> | ->].
      all: kx_autoFLA tt (@nil kza) [0x9a824; 0x9a4f4] 20%nat
             [KZRange (dcap - j) 0 7; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328] (@nil (Z * Z)) (@nil (Z * Z)).
      all: aside.
      all: eapply x2_fcc; [exact DI | exact HN | lia | lia | intros; exact HP].
    - destruct HFL as [-> | ->].
      + clear HK. kclean.
        assert (RJ4 : 8 <= dcap - j <= 4294967296) by (clear - HJ BG GF2; lia).
        kx_autoFLA tt (@nil kza) [0x9a824; 0x9a4f4] 20%nat
          [KZRange (dcap - j) 8 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328] (@nil (Z * Z)) (@nil (Z * Z)).
        all: aside.
        all: eapply x2_fcc; [exact DI | exact HN | lia | lia | intros; exact HP].
      + (* [comment removed for export] *)
        x2_dst. kclean.
        lazymatch goal with DTB : bytes_at bsegs mm DT dtb |- _ =>
          assert (TBL : tbl_in_log bsegs mm DT sh 4 7 1 2) by (apply (x2_tbl mm sh DTB HSH)) end.
        assert (RJ4 : 8 <= dcap - j <= 4294967296 /\ 4096 <= DST + j <= 140737488355320) by (clear - HJ BG R1; lia). destruct RJ4 as (RJ4 & RJ5).
        Time kx_autoFLA tt [KAUnp DT 16388; KAUnp DST dcap; KAApp DST dcap; KAApp (SPV - 64) 64] [0x9a4f4; 0x9a824] 90%nat
          [KZRange (dcap - j) 8 4294967296; KZRange j 0 4294967296; KZRange dcap 0 4294967296; KZRange DST 4096 140737488355328; KZRange (DST + j) 4096 140737488355320;
           KZRange bc 0 64; KZRange SPV 17594333497648 140737488355328; KZRange DT 4096 140737488338940; KZRange sh 52 63;
           KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange n 0 4294967296;
           KZWr DST dcap; KZDisj DST dcap DT 16388; KZDisj DST dcap (SPV - 64) 64;
           KZDisj DST dcap SRC n; KZTblLog DT sh 4 7 1 2]
          [(DT, 16388)] [(DT, 16388); (DST, dcap); (SPV - 64, 64)].
        all: aside.
        all: kx_gen_regsF [7%nat; 9%nat; 14%nat; 18%nat; 19%nat]; intros.
        all: kx_ev_ranges; kx_mem; kx_strip_mod.
        all: x2_to_mid x2_4m2 HN HK HSH HP.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_4rl : forall mm j bc pm9 sh pt (cont : word) (x1 x9 x13 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> 0 <= j <= dcap ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> 0 <= bc <= 64 -> PINV (SRC + pt) ->
    (forall mm' fl bc' P' pt' (x9' x14' x18' x19' x20' x21' : word),
        DINV2 mm' -> P' = SRC + pt' -> (fl = 0 \/ fl = 1) -> 0 <= bc' <= 64 -> PINV (SRC + pt') ->
        evtF bsegs RNG POST (B1ST mm' x1 j bc' pm9 sh P' pt' fl x9' x14' x18' x19' x20' x21')) ->
    evtF bsegs RNG POST (LST4 0x9a374 mm x1 j bc pm9 sh pt cont x9 x13 x14 x18 x19 x20 x21).
  Proof using All.
    intros mm j bc pm9 sh pt cont x1 x9 x13 x14 x18 x19 x20 x21 DI HN HJ HPM HSH HBC HP KB.
    x2_open DI. x2_src. subst pm9.
    assert (QR : exists q r, bc = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc / 8), (bc mod 8); clear - HBC; lia).
    destruct QR as (q & r & -> & HQ & HR).
    assert (RJ : 0 <= j <= 4294967296 /\ 52 <= sh <= 63 /\ 0 <= 8 * q + r <= 64 /\ 1 <= n <= 4294967296) by (clear - HJ R1 R2 HSH GF8 HBC HN; lia).
    destruct RJ as (RJ1 & RJ2 & RJ3 & RJ4).
    destruct HP as [E0 | (O1 & O2)].
    - (* [comment removed for export] *)
      assert (PT0 : pt = 0) by (clear - E0; lia). subst pt. kclean.
      kx_autoFLA tt [KAApp (SPV - 64) 64] [0x9a824; 0x9a430] 40%nat
        [KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 1 4294967296; KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange j 0 4294967296; KZRange DT 4096 140737488338940]
        (@nil (Z * Z)) (@nil (Z * Z)).
      all: aside.
      all: eapply x2_fcc; [exact DI | exact HN | lia | lia | intros; unfold pinv2; lia].
    - rename pt into off.
      kclean.
      assert (RO : 1 <= off <= 4294967296 /\ 8 <= n - off <= 4294967296 /\ 9 <= n <= 4294967296 /\ 4097 <= SRC + off <= 140737488355320)
        by (clear - O1 O2 R2; lia).
      destruct RO as (RO1 & RO2 & RO3 & RO4).
      (* [comment removed for export] *)
      destruct (Z_lt_le_dec off 8) as [C8|C8]; [destruct (Z_lt_le_dec off q) as [CQ|CQ]|].
      1: assert (RC : 1 <= off <= 7 /\ 1 <= q - off <= 8) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      2: assert (RC : 1 <= off <= 7 /\ 0 <= off - q <= 7) by (clear - RO1 C8 CQ HQ; lia); destruct RC as (RC1 & RC2).
      3: assert (RC : 8 <= off <= 4294967296 /\ 0 <= off - q <= 4294967296) by (clear - RO1 C8 HQ; lia); destruct RC as (RC1 & RC2).
      3: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a430] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 8 4294967296; KZRange (off - q) 0 4294967296; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange j 0 4294967296; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n); (SPV - 64, 64)].
      2: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a430] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange (off - q) 0 7; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange j 0 4294967296; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n); (SPV - 64, 64)].
      1: kx_autoFLA tt [KAUnp SRC n; KAApp (SPV - 64) 64] [0x9a430] 120%nat
        [KZRange (n - off) 8 4294967296; KZRange off 1 7; KZRange (q - off) 1 8; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange n 9 4294967296;
         KZRange SRC 4096 140737488355328; KZRange (SRC + n) 4096 140737488355328; KZRange (SRC + off) 4097 140737488355320;
         KZRange SPV 17594333497648 140737488355328; KZRange DST 4096 140737488355328; KZRange dcap 0 4294967296; KZRange j 0 4294967296; KZRange DT 4096 140737488338940]
        [(SRC, n)] [(SRC, n); (SPV - 64, 64)].
      all: aside.
      all: kx_mem.
      all: kx_abs.
      all: eapply KB; [dinv_close | lia | first [left; reflexivity | right; reflexivity] | lia | unfold pinv2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_loop4 : forall (k : nat) mm j bc pm9 sh pt (cont : word) (x1 x9 x13 x14 x18 x19 x20 x21 : word),
    DINV2 mm -> 1 <= n -> 0 <= j <= dcap -> dcap - j <= Z.of_nat k ->
    pm9 = DST + dcap - 7 -> sh = 64 - tl -> 0 <= bc <= 64 -> PINV (SRC + pt) ->
    evtF bsegs RNG POST (LST4 0x9a374 mm x1 j bc pm9 sh pt cont x9 x13 x14 x18 x19 x20 x21).
  Proof using All.
    induction k as [|k IH]; intros mm j bc pm9 sh pt cont x1 x9 x13 x14 x18 x19 x20 x21 DI HN HJ HK HPM HSH HBC HP.
    all: eapply x2_4rl; [exact DI | exact HN | exact HJ | exact HPM | exact HSH | exact HBC | exact HP |].
    all: intros mm' fl bc' P' pt' x9' x14' x18' x19' x20' x21' DI' HPP HFL HBC' HP'.
    all: eapply (x2_4b1 j); [exact DI' | exact HN | | lia | exact HJ | exact HPM | exact HSH | exact HPP | exact HFL | exact HBC' | exact HP'].
    - intros until 0. intros. exfalso. lia.
    - intros mm'' j' bc'' pm9' sh' pt'' cont'' y1 y9 y13 y14 y18 y19 y20 y21 DI'' HJ' HPM' HSH' HBC'' HP''.
      eapply IH; [exact DI'' | exact HN | lia | lia | exact HPM' | exact HSH' | exact HBC'' | exact HP''].
  Qed.

End DX2L4.
End CANSEC1.
