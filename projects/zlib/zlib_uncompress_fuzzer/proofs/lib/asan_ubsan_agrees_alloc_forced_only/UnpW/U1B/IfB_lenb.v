(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit IfAPure IfAStore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj InfBTables. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import IfBTac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import IfB_base IfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= first [ acc_hint_sh | acc_hint_var ].

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo : Z) (rdL rdD fw : Z -> Z) (payload : list Z) (m1 : amem).
  Variables (sd : sdc) (id : idc) (ni ai no ao msg mode hw bw : word).
  Hypothesis CX : if_ctx RNG SP lo Zs S D n OB osz Wd wsz whave wnext lb db la na da nd bo rdL rdD fw payload m1.
  Notation ST := (fms SP Zs S D n OB osz la da gp tp FR fc).
  Notation INV m fo := (if_inv SP Zs S OB osz bo wsz whave wnext Wd la da lb db m1 m sd id ni ai no ao msg mode hw bw fo).
  (* [comment removed for export] *)
  Definition lst (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (len ci co hold bits pc : Z) (m : amem) : machine_state :=
    gms SP Zs S D n OB osz la da gp tp FR fc x5 x6 x7 x10 x11 x14 (Z_to_bv 64 len) x24 x28 x29 x30 ci co hold bits pc m.

  (* [comment removed for export] *)
  Definition refill_post (m : amem) (len ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (hold' : Z),
      ms' = lst x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 len (ci + 2) co hold' (bits + 16) 0x980ec m
      /\ 0 <= hold' < 2 ^ (bits + 16).

  Lemma if_refill2 : forall (m : amem) (fo : Z -> Z) (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (len ci co hold bits : Z),
    INV m fo ->
    0 <= ci -> ci + 2 <= n -> 0 <= bits <= 14 -> 0 <= hold < 2 ^ bits ->
    evtF bsegs RNG (refill_post m len ci co hold bits) (lst x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 len ci co hold bits 0x9809c m).
  Proof using All.
    intros until bits. intros INV0 CI0 CIN BITS HOLD.
    open_fctx CX. open_finv INV0. unfold lst, gms, xms, refill_post.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 LB DB OSZ Z0 ZL S0 SL OB0 OBL
          TLB TL4 TL0 TLN0 TLHI RTL TLR DJTL SHTL RSTL DJSTL TLS1 TLS2 TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2
          SHO DJO ROB RSOB FRM STRM SSC OUT FOR.
    pose proof (pow2_40 bits ltac:(lia)) as P40.
    assert (PAYC : bytes_at bsegs m D (map (Z_to_bv 8) payload)).
    { eapply bytes_at_transport; [exact PAYB| exact MU|]. rewrite length_map, PAYN. exact DJD. }
    destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0).
    zs. zs. pc_dec_ub. zs. pc_dec_ub.
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 14 0x980b8 CK0.
    destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci + 1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b1 & RDB1 & CK1).
    pose proof (pay_read bsegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
    pose proof (bz_range payload ci PAYR) as BZ0.
    zs. zs. zs. rewrite sxb_sval. zs. cbv beta. rewrite (bz_val payload ci PAYR).
    ck_branchJ 5 0x980cc CK1.
    pose proof (pay_read bsegs _ D payload (ci + 1) PAYC ltac:(lia)) as RDP1. fold (bz payload (ci + 1)) in RDP1.
    replace (D + (ci + 1)) with (D + ci + 1) in RDP1 by lia.
    pose proof (bz_range payload (ci + 1) PAYR) as BZ1.
    zs. zs. cbv beta. rewrite (bz_val payload (ci + 1) PAYR).
    zrunb [0x980ec].
    setreg 25 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8))) ltac:(rewrite !shl_byte by lia; f_equal; lia).
    setreg 26 (Z_to_bv 64 (bits + 16)) ltac:(rewrite lor_16 by lia; reflexivity).
    setreg 13 (Z_to_bv 64 (D + (ci + 2))) ltac:(f_equal; lia).
    pose proof (pull2_bound hold bits (bz payload ci) (bz payload (ci + 1)) ltac:(lia) HOLD BZ0 BZ1) as PB2.
    apply evtF_done. do 10 eexists. exists (hold + bz payload ci * 2 ^ bits + bz payload (ci + 1) * 2 ^ (bits + 8)).
    split; [unfold lst, gms, xms; reflexivity|]. lia.
  Qed.

  (* [comment removed for export] *)
  Definition lenb_post (m : amem) (ci co hold bits : Z) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 : word) (len ci' hold' bits' : Z),
      ms' = lst x5 x6 x7 x10 x11 x14 x24 x28 x29 x30 len ci' co hold' bits' 0x980ec m
      /\ 3 <= len <= 258 /\ ci <= ci' <= ci + 3 /\ 15 <= bits' <= 40 /\ 0 <= hold' < 2 ^ bits'
      /\ 8 * (n - ci') + bits' <= 8 * (n - ci) + bits /\ 8 * (n - ci) + bits - 5 <= 8 * (n - ci') + bits'
      /\ 8 * ci - bits <= 8 * ci' - bits' /\ ci' <= n.

  Lemma if_lenb : forall (m : amem) (fo : Z -> Z) (x6 x10 x14 x15 x24 x28 x29 x30 : word) (ci co hold bits k : Z),
    INV m fo ->
    0 <= k < na -> 16 <= code_op (rdL k) <= 21 -> 3 <= code_val (rdL k) -> code_val (rdL k) + 2 ^ (code_op (rdL k) - 16) - 1 <= 258 ->
    0 <= ci <= n -> 0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> 33 <= 8 * (n - ci) + bits ->
    evtF bsegs RNG (lenb_post m ci co hold bits)
      (ST x6 (Z_to_bv 64 (la + 4 * k)) x10 (Z_to_bv 64 (code_op (rdL k))) x14 x15 x24 x28 x29 x30 ci co hold bits 0x98020 m).
  Proof using All.
    intros until k. intros INV0 HK HOP HV3 HV258 CI0 BITS HOLD HA. pose proof INV0 as INVK.
    open_fctx CX. open_finv INV0. unfold fms, gms, xms.
    clear ZSD ZOD SOD WSZ WNX WIN TOKL TOKD SANE FWR WH WN BO0 DB LB
          TDB TD4 TD0 TDN0 TDHI RTD TDR DJTD SHTD RSTD DJSTD TDS1 TDS2 SHZ DJZ SHS DJS RZ RSZ RS RSS SHO DJO ROB RSOB FRM STRM SSC OUT FOR.
    pose proof (TLR k HK) as RK. pose proof (code_val_range (rdL k)) as RCV. pose proof (code_op_range (rdL k)) as ROP.
    pose proof (op_base_tests (code_op (rdL k)) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    pose proof (pow2_40 bits BITS) as P40.
    assert (TLC : bytes_at bsegs m la (u32s (fws rdL (Z.to_nat na)))).
    { eapply bytes_at_transport; [exact TLB| exact MU|]. rewrite u32s_length, fws_length.
      replace (Z.of_nat (4 * Z.to_nat na)) with (4 * na) by lia. exact DJTL. }
    pose proof (code_read_val bsegs m la (fws rdL (Z.to_nat na)) k (rdL k) TLC (f32arr_nth rdL (Z.to_nat na) k ltac:(lia)) ltac:(lia) RK) as RDV.
    zs. zs. zs. zs. zs.                      (* [comment removed for export] *)
    zs. rewrite zx16_small by lia.           (* [comment removed for export] *)
    zs. rewrite T15.                         (* [comment removed for export] *)
    remember (code_op (rdL k) - 16) as e eqn:EE.
    assert (ER : 0 <= e <= 5) by lia.
    pose proof (pow2_15 e ltac:(lia)) as PE.
    (* [comment removed for export] *)
    assert (REF : forall (y5 y6 y7 y10 y11 y14 y24 y28 y29 y30 : word) (len ci' hold' bits' : Z),
              3 <= len <= 258 -> 0 <= bits' <= 14 -> 0 <= hold' < 2 ^ bits' -> ci <= ci' <= ci + 1 -> ci' <= n ->
              8 * (n - ci') + bits' <= 8 * (n - ci) + bits -> 8 * (n - ci) + bits - 5 <= 8 * (n - ci') + bits' ->
              8 * ci - bits <= 8 * ci' - bits' ->
              evtF bsegs RNG (lenb_post m ci co hold bits)
                (lst y5 y6 y7 y10 y11 y14 y24 y28 y29 y30 len ci' co hold' bits' 0x9809c m)).
    { intros y5 y6 y7 y10 y11 y14 y24 y28 y29 y30 len ci' hold' bits' L' B' H' C' N' A1 A2 Q'.
      eapply evtF_mono; [eapply (if_refill2 m fo); [exact INVK | lia | lia | lia | exact H']|].
      cbv beta. intros ms' (z5 & z6 & z7 & z10 & z11 & z14 & z24 & z28 & z29 & z30 & h2 & -> & H2).
      unfold lenb_post. do 10 eexists. exists len, (ci' + 2), h2, (bits' + 16). split; [reflexivity|]. lia. }
    (* [comment removed for export] *)
    assert (TAIL : forall (y5 y7 y10 y14 : word) (ci' hold' bits' : Z),
              e <= bits' <= 40 -> 0 <= hold' < 2 ^ bits' -> ci <= ci' <= ci + 1 -> ci' <= n ->
              8 * (n - ci') + bits' = 8 * (n - ci) + bits -> 8 * ci - bits = 8 * ci' - bits' ->
              evtF bsegs RNG (lenb_post m ci co hold bits)
                (lst y5 x6 y7 y10 (Z_to_bv 64 e) y14 x24 x28 x29 x30 (code_val (rdL k)) ci' co hold' bits' 0x98070 m)).
    { intros y5 y7 y10 y14 ci' hold' bits' B' H' C' N' A' Q'. unfold lst, gms, xms.
      pose proof (pow2_40 bits' ltac:(lia)) as P40'.
      zs. zs. zs. rewrite mask_sllw by lia.
      zs. zs. zs. zs.
      setreg 25 (Z_to_bv 64 (hold' / 2 ^ e)) ltac:(rewrite srl_div by lia; reflexivity).
      setreg 26 (Z_to_bv 64 (bits' - e)) ltac:(rewrite swrap32_small by lia; reflexivity).
      setreg 15 (Z_to_bv 64 (code_val (rdL k) + hold' mod 2 ^ e)) ltac:(rewrite land_mask_mod by lia; f_equal; lia).
      pose proof (drop_bound hold' bits' e ltac:(lia) H') as HB. pose proof (mod_pow2_bound hold' e ltac:(lia)) as MB.
      zs. zbr KR.
      - eapply (REF _ _ _ _ _ _ _ _ _ _ (code_val (rdL k) + hold' mod 2 ^ e) ci' (hold' / 2 ^ e) (bits' - e)); lia.
      - zs. apply evtF_done. unfold lenb_post. do 10 eexists. exists (code_val (rdL k) + hold' mod 2 ^ e), ci', (hold' / 2 ^ e), (bits' - e).
        split; [unfold lst, gms, xms; reflexivity|]. lia. }
    zs. zbr K.
    - (* [comment removed for export] *)
      zs. zs. zbr KB.
      + apply evtF_done. unfold lenb_post. do 10 eexists. exists (code_val (rdL k)), ci, hold, bits.
        split; [unfold lst, gms, xms; reflexivity|]. lia.
      + eapply (REF _ _ _ _ _ _ _ _ _ _ (code_val (rdL k)) ci hold bits); lia.
    - zs. zbr K2.
      + (* [comment removed for export] *)
        eapply TAIL; lia.
      + (* [comment removed for export] *)
        assert (CIN : ci + 1 <= n) by lia.
        assert (PAYC : bytes_at bsegs m D (map (Z_to_bv 8) payload)).
        { eapply bytes_at_transport; [exact PAYB| exact MU|]. rewrite length_map, PAYN. exact DJD. }
        destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b0 & RDB0 & CK0).
        zs. zs. pc_dec_ub.
        zs. zs. zs. rewrite sxb_sval.
        ck_branchJ 5 0x9805c CK0.
        pose proof (pay_read bsegs _ D payload ci PAYC ltac:(lia)) as RDP0. fold (bz payload ci) in RDP0.
        pose proof (bz_range payload ci PAYR) as BZ0.
        zs. cbv beta. rewrite (bz_val payload ci PAYR).
        zs. zs. zs. zs.
        setreg 25 (Z_to_bv 64 (hold + bz payload ci * 2 ^ bits)) ltac:(rewrite shl_byte by lia; f_equal; lia).
        setreg 13 (Z_to_bv 64 (D + (ci + 1))) ltac:(f_equal; lia).
        pose proof (pull_bound hold bits (bz payload ci) ltac:(lia) HOLD BZ0) as PB1.
        eapply TAIL; lia.
  Qed.
End P.
End CANSEC1.
