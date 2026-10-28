(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_asn1_get_bool.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len LxConv_getlen LxConv_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.


Definition A_ASN1_GET_BOOL : Z := 0x0999bc.

(* [comment removed for export] *)
Notation ASN1_GET_BOOL_STACK_A := 64 (only parsing).

Definition asn1_get_bool_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP VALP P END lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (r p' : Z) (v : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - ASN1_GET_BOOL_STACK_A, bv_unsigned sp)] m m' /\
      wmono segs m m' /\
      mem_inv segs m' /\
      a0 = Z_to_bv 64 r /\
      (-127 < r /\ r <= 0) /\
      rw_cells segs m' PP [C8 (Z_to_bv 64 p')] /\
      rw_cells segs m' VALP [C4 v] /\
      stk segs m' lo (bv_unsigned sp) /\
      (P <= p' /\ p' <= END) /\
      (r = 0 -> P + 3 <= p')
(* [comment removed for export] *).

Definition asn1_get_bool_stmtA {L : heap_layout} (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP VALP P END BUF lo : Z) (bs : list byte) (valv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m VALP [C4 valv] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= VALP \/ VALP + 4 <= PP) ->
  (Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP) ->
  PP mod 8 = 0 -> VALP mod 4 = 0 -> 0 < PP -> 0 < VALP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_BOOL_STACK_A -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (VALP + 4 <= lo \/ bv_unsigned sp <= VALP) ->
  (Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  (* [comment removed for export] *)
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m PP 8 -> aobj segs AL CS m VALP 4 -> aobj segs AL CS m BUF (Z.of_nat (length bs)) ->
  aobj segs AL CS m (bv_unsigned sp - 48) 8 ->
  crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 VALP ->
  evtA segs AL CS (asn1_get_bool_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP VALP P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= VALP \/ VALP + 4 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ VALP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= VALP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis VALB : 0 <= VALP /\ VALP + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : VALP mod 4 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < VALP.
  Hypothesis SPL : lo <= bv_unsigned sp - 64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : VALP + 4 <= lo \/ bv_unsigned sp <= VALP.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (VALP, VALP + 4); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (asn1_get_bool_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP VALP P END lo m).


  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.

  Lemma main_walk : forall (a3 a4 a5 a6 a7 valv : word),
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m VALP [C4 valv] -> bytes_at asegs m BUF bs ->
    mem_inv asegs m -> abase asegs AL m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m VALP 4 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    aobj asegs AL CS m (bv_unsigned sp - 48) 8 ->
    stk asegs m lo (bv_unsigned sp) ->
    evtA asegs AL CS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 VALP) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x0999bc) fc None m (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros a3 a4 a5 a6 a7 valv HPP HVAL HBUF MI AB OPP OVAL OBUF OLEN ST.
    pose proof (munch_refl W m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB asegs m (bv_unsigned sp + -48) [] 48 junk [] [8; 40]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    cb8_to_c8 FR (@nil cell).
    lazymatch type of FR with rw_cells _ _ _ (C8 ?w :: _) => rewrite <- (Z_to_bv_bv_unsigned w) in FR end.
    pose proof (sums_getlen_ok AL IMG) as LXSUMS.
    lx_pre.
    lx_run_tac (PLANS [] [(0x99a18, DJoin); (0x99a8c, DJoin); (0x99aa0, DJoin)] 200%N [SUM_getlenA]).
    lx_tree.
    - (* [comment removed for export] *) try lx_rejoin; lx_leaf; try lxc_cells_conv; try lx_arith.
    - (* [comment removed for export] *) try lx_rejoin; lx_leaf; try lxc_cells_conv; try lx_arith.
    - (* [comment removed for export] *) try lx_rejoin; lx_leaf; try lxc_cells_conv; try lx_arith.
    - (* [comment removed for export] *) try lx_rejoin; lx_leaf; try lxc_cells_conv; try lx_arith.
    - (* [comment removed for export] *) try lx_rejoin; lx_leaf; try lxc_cells_conv; try lx_arith.
  Qed.
End Walk.

Lemma A_asn1_get_bool_spec {L : heap_layout} : forall AL, asan_img_ok AL -> asn1_get_bool_stmtA asegs AL A_ASN1_GET_BOOL.
Proof.
  intros AL IMG. unfold asn1_get_bool_stmtA, A_ASN1_GET_BOOL.
  intros until valv. intros HPP HVAL HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OVAL OBUF OLEN SCS -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HVAL) as VALB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, VALB.
  pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.
